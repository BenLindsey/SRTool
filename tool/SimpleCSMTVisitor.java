package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;
import parser.SimpleCParser.StmtContext;

import java.util.*;

public class SimpleCSMTVisitor extends SimpleCBaseVisitor<SMT> {

    private static final SimpleCParser.ExprContext FALSE_EXPRESSION = new SimpleCParser.ExprContext(null, 0);

    private SMT returnExpr;
    private ExpressionUtils expressionUtils = new ExpressionUtils(this);

    private Variables variables = new Variables();

    private ImplicationStore implicationStore = new ImplicationStore();
    private ConditionStack assertions = new ConditionStack();

    private Map<String, ProcedureSummarisation> summarisationMap;
    private Map<String, SMT> parameterMap;

    public SimpleCSMTVisitor(Map<String, ProcedureSummarisation> summarisationMap) {
        this.summarisationMap = summarisationMap;
    }

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

        for(StmtContext statement : ctx.stmts) {
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
        SMT assertionsSMT = assertions.getFullCondition();

        if (!assertionsSMT.isEmpty()) {
            result = SMT.merge(result, SMT.createAssertNot(assertions.getFullCondition()));
        }

        // Add declarations to the top of the output

        return SMT.createProcedureDecl(Variables.getDeclarations(), result);
    }

    @Override
    public SMT visitRequires(SimpleCParser.RequiresContext ctx) {
        SMT condition = visit(ctx.condition);
        implicationStore.pushImplication(condition);
        return SMT.createEmpty();
    }

    @Override
    public SMT visitEnsures(SimpleCParser.EnsuresContext ctx) {
        SMT assertion = visit(ctx.condition);

        SMT pred = implicationStore.getFullImplication();
        if( !pred.isEmpty() ) {
            assertion = SMT.createImplication(pred, assertion);
        }

        assertions.push(assertion);
        return SMT.createEmpty();
    }

    @Override
    public SMT visitFormalParam(SimpleCParser.FormalParamContext ctx) {
        variables.addSMTDeclaration(ctx.ident.getText(), true);
        return SMT.createEmpty();
    }

    @Override
    public SMT visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        variables.addSMTDeclaration(ctx.ident.getText(), true);
        return SMT.createEmpty();
    }

    @Override
    public SMT visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        final SMT expression = visit(ctx.expr());
        return assign(ctx.varref(), expression);
    }

    private SMT assign(SimpleCParser.VarrefContext ctx, SMT expression) {
        SMT currentVariable = visit(ctx);
        String freshVariable = variables.addSMTDeclaration(currentVariable.toString(), false);
        return SMT.createAssign(freshVariable, expression);

    }

    @Override
    public SMT visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        havoc(ctx.var.getText());
        return SMT.createEmpty();
    }

    private void havoc(String variable) {
        variables.addSMTDeclaration(variable, false);
    }

    private void havoc(Set<String> modset) {
        for (String var : modset) {
            havoc(var);
        }
    }

    @Override
    public SMT visitCallStmt(SimpleCParser.CallStmtContext ctx) {
        ProcedureSummarisation summarisation = summarisationMap.get(ctx.callee.getText());

        // Save current state
        SMT oldReturnExpr = returnExpr;
        Map<String,SMT> oldParameterMap = parameterMap;

        parameterMap = new HashMap<>();

        // Caller and callee should have same number of parameters
        assert ctx.actuals.size() == summarisation.getParameters().size();
        for (int i = 0; i < ctx.actuals.size(); i++) {
            SMT actualSMT = visit(ctx.actuals.get(i));
            parameterMap.put(summarisation.getParameters().get(i), actualSMT);
        }

        for (SimpleCParser.ExprContext exprContext : summarisation.getPreconditions()) {
            assertCondition(exprContext);
        }

        havoc(summarisation.getModset());

        String returnVar = ctx.callee.getText() + "_ret";
        SMT newReturnExpr = SMT.createVariable(variables.addSMTDeclaration(returnVar, true));

        returnExpr = newReturnExpr;

        for (SimpleCParser.ExprContext exprContext : summarisation.getPostconditions()) {
            assumeCondition(exprContext);
        }

        // Restore old state
        parameterMap = oldParameterMap;
        returnExpr = oldReturnExpr;

        return assign(ctx.varref(), newReturnExpr);
    }

    @Override
    public SMT visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        return assertCondition(ctx.condition);
    }

    private SMT assertCondition(SimpleCParser.ExprContext condition) {
        SMT pred = implicationStore.getFullImplication();

        SMT assertion = visit(condition);

        if( !pred.isEmpty() ) {
            assertion = SMT.createImplication(pred, assertion);
        }

        assertions.push(assertion);

        return SMT.createEmpty();
    }

    @Override
    public SMT visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        return assumeCondition(ctx.condition);
    }

    private SMT assumeCondition(SimpleCParser.ExprContext condition) {
        SMT assumption = condition == FALSE_EXPRESSION ? SMT.createBool(false) : visit(condition);

        implicationStore.pushImplication(assumption);

        return SMT.createEmpty();

    }

    @Override
    public SMT visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {

        SMT result = SMT.createEmpty();

        SimpleCParser.ExprContext condition = ctx.condition;

        ParserRuleContext dummyNode = new ParserRuleContext();

        for(SimpleCParser.LoopInvariantContext invariant : ctx.invariantAnnotations) {
            result = SMT.merge(result, assertCondition(invariant.invariant().condition));
        }

        ModSetVisitor modSetVisitor = new ModSetVisitor();
        havoc(ctx.body.accept(modSetVisitor));

        for(SimpleCParser.LoopInvariantContext invariant : ctx.invariantAnnotations) {
            result = SMT.merge(result, assumeCondition(invariant.invariant().condition));
        }

        SimpleCParser.IfStmtContext ifBlock = new SimpleCParser.IfStmtContext(dummyNode, 0);
        ifBlock.condition = condition;
        ifBlock.thenBlock = ctx.body;

        for(SimpleCParser.LoopInvariantContext invariant : ctx.invariantAnnotations) {
            SimpleCParser.AssertStmtContext assertion = new SimpleCParser.AssertStmtContext(ifBlock.thenBlock, 0);
            assertion.condition = invariant.invariant().condition;

            // Add invariant assertions to end of if block
            ifBlock.thenBlock.addChild(assertion);
        }

        // Assume false to block further loop execution
        SimpleCParser.AssumeStmtContext assumption = new SimpleCParser.AssumeStmtContext(ifBlock.thenBlock, 0);
        assumption.condition = FALSE_EXPRESSION;
        ifBlock.thenBlock.addChild(assumption);

        return SMT.merge(result, visit(ifBlock));
    }

    @Override
    public SMT visitIfStmt(SimpleCParser.IfStmtContext ctx) {

        SMT builder = SMT.createEmpty();

        SMT predicate = visit(ctx.condition);
        SMT notPredicate = SMT.createNot(predicate);

        Variables thenBlock;
        Variables elseBlock = variables;

        variables.enterScope();
        implicationStore.enterScope(predicate);
        implicationStore.pushImplication(predicate);
        builder = SMT.merge(builder, super.visitBlockStmt(ctx.thenBlock));
        implicationStore.exitScope();
        thenBlock = variables.exitScope();

        if (ctx.elseBlock != null) {
            variables.enterScope();
            implicationStore.enterScope(notPredicate);
            implicationStore.pushImplication(notPredicate);
            builder = SMT.merge(builder, super.visitBlockStmt(ctx.elseBlock));
            implicationStore.exitScope();
            elseBlock = variables.exitScope();
        }

        ModSetVisitor modSetVisitor = new ModSetVisitor();

        for( String var : union(ctx.thenBlock.accept(modSetVisitor),  ctx.elseBlock == null ? new HashSet<String>() : ctx.elseBlock.accept(modSetVisitor))) {
            SMT ite = SMT.createITE(
                    predicate,
                    SMT.createVariable((thenBlock.getActualDeclaredVariables().contains(var) ? variables : thenBlock).getCurrentVariable(var)),
                    SMT.createVariable((elseBlock.getActualDeclaredVariables().contains(var) ? variables : elseBlock).getCurrentVariable(var))
            );

            // Add fresh variable for var
            variables.addSMTDeclaration(var, false);

            builder = SMT.merge(builder, SMT.createAssert(variables.getCurrentVariable(var),  ite));
        }

        return builder;
    }

    private <T> Set<T> union(Set<T> first, Set<T> second) {
        Set<T> union = new HashSet<>(first);
        union.addAll(second);
        return union;
    }

    @Override
    public SMT visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
        variables.enterScope();

        SMT result = SMT.createEmpty();

        for(StmtContext stmt :ctx.stmts) {
            result = SMT.merge(result, visit(stmt));
        }

        Variables vars = variables.exitScope();

        ModSetVisitor modSetVisitor = new ModSetVisitor();

        for( String var : ctx.accept(modSetVisitor)) {

            if( !vars.getActualDeclaredVariables().contains(var) ) {
                SMT assignment = SMT.createAssign(variables.addSMTDeclaration(var, false), SMT.createVariable(vars.getCurrentVariable(var)));
                result = SMT.merge(result, assignment);
            }
        }

        return result;
    }

    @Override
    public SMT visitInvariant(SimpleCParser.InvariantContext ctx) {
        return assertCondition(ctx.condition);
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
    public SMT visitBxorExpr(SimpleCParser.BxorExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToSMT(ctx.ops, ctx.args) : super.visitBxorExpr(ctx);
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
        return ctx.ops.size() > 0 ? expressionUtils.unaryToSMT(ctx.ops, ctx.arg) : super.visitUnaryExpr(ctx);
    }
    
    @Override
    public SMT visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return returnExpr;
    }

    @Override
    public SMT visitOldExpr(SimpleCParser.OldExprContext ctx) {
        return SMT.createVariable(super.visitOldExpr(ctx).toString() + "-0");
    }

    @Override
    public SMT visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        String variable = super.visitVarrefExpr(ctx).toString();
        if (parameterMap != null && parameterMap.containsKey(variable)) {
            return parameterMap.get(variable);
        }

        return SMT.createVariable(variables.getCurrentVariable(variable));
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
