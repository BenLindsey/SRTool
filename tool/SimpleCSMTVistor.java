package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class SimpleCSMTVistor extends SimpleCBaseVisitor<SMT> {

    private SMT returnExpr;
    private ExpressionUtils expressionUtils = new ExpressionUtils(this);

    private SSAMap ssaMap = new SSAMap();

    private ConditionStore conditionStore = new ConditionStore();
    private ConditionStack assertions = new ConditionStack();


    @Override
    public SMT visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        SMT result = SMT.createEmpty();

        for(SimpleCParser.FormalParamContext param : ctx.formals) {
            result = SMT.merge(result, visit(param));
        }

        // Visit pre conditions
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if( prepost.requires() == null ) continue;
            result = SMT.merge(result, (visit(prepost.requires())));
        }

        for(SimpleCParser.StmtContext statement : ctx.stmts) {
            result = SMT.merge(result, (visit(statement)));
        }

        // Save returnExpr for use in \return annotations
        returnExpr = visit(ctx.returnExpr);

        // Visit post conditions
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if( prepost.ensures() == null ) continue;
            result = SMT.merge(result, visit(prepost.ensures()));
        }

        // Add assertions
        result = SMT.merge(result, SMT.createAssertNot(assertions.getFullCondition()));

        // Add declarations to the top of the output

        return SMT.createProcedureDecl(SSAMap.getDeclarations(), result);
    }

    @Override
    public SMT visitRequires(SimpleCParser.RequiresContext ctx) {
        SMT condition = visit(ctx.condition);
        conditionStore.pushPredicate(condition);
        return SMT.createRequires(condition);
    }

    @Override
    public SMT visitEnsures(SimpleCParser.EnsuresContext ctx) {
        assertions.push(visit(ctx.condition));
        return SMT.createEmpty();
    }

    @Override
    public SMT visitFormalParam(SimpleCParser.FormalParamContext ctx) {
        ssaMap.addSMTDeclaration(ctx.ident.getText(), true);
        return SMT.createEmpty();
    }

    @Override
    public SMT visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        ssaMap.addSMTDeclaration(ctx.ident.getText(), true);
        return SMT.createEmpty();
    }

    @Override
    public SMT visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        final SMT expression = visit(ctx.expr());

        SMT currentVariable = visit(ctx.varref());
        String freshVariable = ssaMap.addSMTDeclaration(currentVariable.toString(), false);
        ssaMap.addModsetVariable(currentVariable.toString());
        return SMT.createAssign(freshVariable, expression);
    }

    @Override
    public SMT visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        ssaMap.addSMTDeclaration(ctx.var.getText(), false);
        return SMT.createEmpty();
    }

    @Override
    public SMT visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        SMT pred = conditionStore.getFullCondition();

        SMT assertion = visit(ctx.condition);

        if( !pred.isEmpty() ) {
            assertion = SMT.createImplication(pred, assertion);
        }

        assertions.push(assertion);

        return SMT.createEmpty();
    }

    @Override
    public SMT visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        SMT assumption = visit(ctx.condition);

        conditionStore.addAssumption(assumption);

        return SMT.createEmpty();
    }

    @Override
    public SMT visitIfStmt(SimpleCParser.IfStmtContext ctx) {

        SMT builder = SMT.createEmpty();

        SMT predicate = visit(ctx.condition);

        SSAMap mapForIfClause;
        SSAMap mapForElseClause = ssaMap;

        ssaMap.pushScope();
        conditionStore.pushPredicate(predicate);
        builder = SMT.merge(builder, visit(ctx.thenBlock));
        conditionStore.popPredicate();
        mapForIfClause = ssaMap.popScope();

        if (ctx.elseBlock != null) {
            ssaMap.pushScope();
            conditionStore.pushPredicate(SMT.createNot(predicate));
            builder = SMT.merge(builder, visit(ctx.elseBlock));
            conditionStore.popPredicate();
            mapForElseClause = ssaMap.popScope();
        }

        for( String var : union(mapForIfClause.getModset(), mapForElseClause.getModset())) {
            SMT ite = SMT.createITE(
                    predicate,
                    SMT.createVariable((SSAMap.getActualDeclaredVariables().contains(var) ? ssaMap : mapForIfClause).getCurrentVariable(var)),
                    SMT.createVariable((SSAMap.getActualDeclaredVariables().contains(var) ? ssaMap : mapForElseClause).getCurrentVariable(var))
            );

            // Add fresh variable for var
            ssaMap.addSMTDeclaration(var, false);

            builder = SMT.merge(builder, SMT.createAssert(ssaMap.getCurrentVariable(var),  ite));
        }

        return builder;
    }

    private <T> Set<T> union(Set<T> first, Set<T> second) {
        Set<T> union = new HashSet<>(first);
        union.addAll(second);
        return union;
    }

    @Override
    public SMT visitTernExpr(SimpleCParser.TernExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.ternaryToSMT(ctx.args) : super.visitTernExpr(ctx);
    }

    @Override
    public SMT visitLorExpr(SimpleCParser.LorExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitLorExpr(ctx);
    }

    @Override
    public SMT visitLandExpr(SimpleCParser.LandExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitLandExpr(ctx);
    }

    @Override
    public SMT visitBorExpr(SimpleCParser.BorExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitBorExpr(ctx);
    }

    @Override
    public SMT visitBandExpr(SimpleCParser.BandExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitBandExpr(ctx);
    }

    @Override
    public SMT visitRelExpr(SimpleCParser.RelExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitRelExpr(ctx);
    }

    @Override
    public SMT visitShiftExpr(SimpleCParser.ShiftExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitShiftExpr(ctx);
    }

    @Override
    public SMT visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitEqualityExpr(ctx);
    }

    @Override
    public SMT visitAddExpr(SimpleCParser.AddExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitAddExpr(ctx);
    }

    @Override
    public SMT visitMulExpr(SimpleCParser.MulExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitMulExpr(ctx);
    }

    @Override
    public SMT visitUnaryExpr(SimpleCParser.UnaryExprContext ctx) {
        return ctx.ops.size() > 0 ? expressionUtils.unaryToSMT(ctx.ops, ctx.arg) : visit(ctx.atomExpr());
    }
    
    @Override
    public SMT visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return returnExpr;
    }

    @Override
    public SMT visitOldExpr(SimpleCParser.OldExprContext ctx) {
        return SMT.createVariable(ssaMap.getCurrentVariable(super.visitOldExpr(ctx).toString()));
    }

    @Override
    public SMT visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return SMT.createVariable(ssaMap.getCurrentVariable(super.visitVarrefExpr(ctx).toString()));
    }

    @Override
    public SMT visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
        return SMT.createVariable(ctx.name.getText());
    }

    @Override
    public SMT visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        return SMT.createNumber(ctx.number.getText());
    }

    @Override
    protected SMT defaultResult() {
        return SMT.createEmpty();
    }

    @Override
    protected SMT aggregateResult(SMT aggregate, SMT nextResult) {
        return SMT.merge(aggregate, nextResult);
    }
}
