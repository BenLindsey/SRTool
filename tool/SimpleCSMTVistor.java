package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

public class SimpleCSMTVistor extends SimpleCBaseVisitor<SMT> {

    private SMT returnExpr;
    private ExpressionUtils expressionUtils = new ExpressionUtils(this);

    private SSAMap ssaMap = new SSAMap();
    private List<String> globals = new ArrayList<>();
    private Deque<Map<String, String>> globalsMapStack = new ArrayDeque<>();
    
    private ConditionStore conditionStore = new ConditionStore();
    private ConditionStack assertions = new ConditionStack();

    private Set<String> modset = new HashSet<>();

    private SMT declarations = SMT.createEmpty();

    public SimpleCSMTVistor(List<SimpleCParser.VarDeclContext> globals) {
        for (SimpleCParser.VarDeclContext global : globals) {
            this.globals.add(global.ident.getText());
        }
    }

    private void addDeclaration(String variable) {
        declarations = SMT.merge(declarations, SMT.createDeclaration(variable));
    }

    @Override
    public SMT visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        SMT result = SMT.createEmpty();

        // Save globals
        Map<String, String> globalsMap = new HashMap<>();
        for (String global : globals) {
            globalsMap.put(global, ssaMap.getCurrentVariable(global));
        }

        globalsMapStack.push(globalsMap);

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

        globalsMapStack.pop();

        return SMT.createProcedureDecl(declarations, result);
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
        addDeclaration(ssaMap.fresh(ctx.ident.getText()));
        return SMT.createEmpty();
    }

    @Override
    public SMT visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        addDeclaration(ssaMap.fresh(ctx.ident.getText()));
        return SMT.createEmpty();
    }

    @Override
    public SMT visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        final SMT expression = visit(ctx.expr());

        SMT currentVariable = visit(ctx.varref());
        String freshVariable = ssaMap.fresh(currentVariable.toString());
        modset.add(currentVariable.toString());

        addDeclaration(freshVariable);
        return SMT.createAssign(freshVariable, expression);
    }

    @Override
    public SMT visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        addDeclaration(ssaMap.fresh(ctx.var.getText()));
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

        SSAMap originalMap = ssaMap;
        SSAMap mapForIfClause = ssaMap.clone();
        SSAMap mapForElseClause = ssaMap.clone();

        Set<String> currentModset = modset;
        Set<String> newModset = new HashSet<>();
        modset = newModset;

        ssaMap = mapForIfClause;
        conditionStore.pushPredicate(predicate);
        builder = SMT.merge(builder, visit(ctx.thenBlock));
        conditionStore.popPredicate();

        if (ctx.elseBlock != null) {
            ssaMap = mapForElseClause;
            conditionStore.pushPredicate(SMT.createNot(predicate));
            builder = SMT.merge(builder, visit(ctx.elseBlock));
            conditionStore.popPredicate();
        }

        ssaMap = originalMap;

        modset = currentModset;

        for( String var : newModset ) {
            SMT ite = SMT.createITE(
                    predicate,
                    SMT.createVariable(mapForIfClause.getCurrentVariable(var)),
                    SMT.createVariable(mapForElseClause.getCurrentVariable(var))
            );

            // Add fresh variable for var
            addDeclaration(ssaMap.fresh(var));

            builder = SMT.merge(builder, SMT.createAssert(ssaMap.getCurrentVariable(var),  ite));
        }

        return builder;
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
        return SMT.createVariable(globalsMapStack.peek().get(ctx.arg.ident.name.getText()));
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
