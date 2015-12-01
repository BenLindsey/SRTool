package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;
import parser.SimpleCParser.StmtContext;
import tool.SMTs.SMTFactory;
import tool.SMTs.SMT;

import java.util.*;

public class SimpleCSMTVisitor extends SimpleCBaseVisitor<SMT> {

    private static final SimpleCParser.ExprContext FALSE_EXPRESSION = new SimpleCParser.ExprContext(null, 0);

    private final int UNROLLING_DEPTH;
    private final boolean UNROLL_LOOPS;

    private SMT returnExpr;
    private ExpressionUtils expressionUtils = new ExpressionUtils(this);

    private Variables variables = new Variables();

    private ImplicationStore implicationStore = new ImplicationStore();
    private AssertionCollection assertions = new AssertionCollection();

    private Map<String, ProcedureSummarisation> summarisationMap;
    private Map<String, SMT> parameterMap;

    private List<Integer> unwindingAssertionIds = new ArrayList<>();

    private Map<Integer, SimpleCParser.CandidateInvariantContext> assertionToCandidateInvariantMap = new HashMap<>();
    private Set<SimpleCParser.CandidateInvariantContext> eliminatedCandidateInvariants = new HashSet<>();
    private List<SimpleCParser.ExprContext> candidateInvariantConditions = new ArrayList<>();

    private Map<Integer, SimpleCParser.PrepostContext> assertionToCandidatePrePostMap = new HashMap<>();
    private Set<SimpleCParser.PrepostContext> eliminatedPrePosts = new HashSet<>();
    private List<SimpleCParser.ExprContext> candidatePrePostConditions = new ArrayList<>();

    public SimpleCSMTVisitor(Map<String, ProcedureSummarisation> summarisationMap) {
        this.summarisationMap = summarisationMap;
        UNROLL_LOOPS = false;
        UNROLLING_DEPTH = 0;
    }

    public SimpleCSMTVisitor(Map<String, ProcedureSummarisation> summarisationMap, int unrollingDepth) {
        this.summarisationMap = summarisationMap;
        UNROLL_LOOPS = true;
        UNROLLING_DEPTH = unrollingDepth;
    }

    public List<Integer> getUnwindingAssertionIds() {
        return unwindingAssertionIds;
    }

    public Map<Integer, SimpleCParser.CandidateInvariantContext> getAssertionToCandidateInvariantMap() {
        return assertionToCandidateInvariantMap;
    }

    public Set<SimpleCParser.CandidateInvariantContext> getEliminatedCandidateInvariants() {
        return eliminatedCandidateInvariants;
    }

    public Set<SimpleCParser.PrepostContext> getEliminatedPrePosts() {
        return eliminatedPrePosts;
    }

    public Map<Integer, SimpleCParser.PrepostContext> getAssertionToCandidatePrePostMap() {
        return assertionToCandidatePrePostMap;
    }

    public int assertionsSize() {
        return assertions.size();
    }

    @Override
    public SMT visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        SMT result = SMTFactory.createEmpty();

        for(SimpleCParser.FormalParamContext param : ctx.formals) {
            result = SMTFactory.merge(result, visit(param));
        }

        // Visit pre conditions
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if( prepost.requires() != null ) {
                result = SMTFactory.merge(result, (visit(prepost.requires())));
            } else if (prepost.candidateRequires() != null && !eliminatedPrePosts.contains(prepost)) {
                result = SMTFactory.merge(result, visit(prepost.candidateRequires()));
            }
        }

        for(StmtContext statement : ctx.stmts) {
            result = SMTFactory.merge(result, (visit(statement)));
        }

        // Save returnExpr for use in \return annotations
        returnExpr = visit(ctx.returnExpr);

        // Visit post conditions
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if( prepost.ensures() != null ) {
                result = SMTFactory.merge(result, visit(prepost.ensures()));
            } else if (prepost.candidateEnsures() != null && !eliminatedPrePosts.contains(prepost)) {
                candidatePrePostConditions.add(prepost.candidateEnsures().condition);
                result = SMTFactory.merge(result, visit(prepost.candidateEnsures()));
            }
        }

        // Add assignments
        result = SMTFactory.merge(result, assertions.getAssignments());

        // Add assertions
        SMT assertionsSMT = assertions.getAssertions();

        if (!assertionsSMT.isEmpty()) {
            result = SMTFactory.merge(result, SMTFactory.createAssertNot(assertionsSMT));
        }

        // Add declarations to the top of the output
        SMT declarations = assertions.addAssertionDeclarations();
        declarations = SMTFactory.merge(declarations, Variables.getDeclarations());
        return SMTFactory.createProcedureDecl(declarations, result);
    }

    @Override
    public SMT visitRequires(SimpleCParser.RequiresContext ctx) {
        return assumeCondition(ctx.condition);
    }

    @Override
    public SMT visitCandidateRequires(SimpleCParser.CandidateRequiresContext ctx) {
        return assumeCondition(ctx.condition);
    }

    @Override
    public SMT visitEnsures(SimpleCParser.EnsuresContext ctx) {
        return assertCondition(ctx.condition);
    }

    @Override
    public SMT visitCandidateEnsures(SimpleCParser.CandidateEnsuresContext ctx) {
        return assertCondition(ctx.condition);
    }

    @Override
    public SMT visitFormalParam(SimpleCParser.FormalParamContext ctx) {
        variables.addSMTDeclaration(ctx.ident.getText(), true);
        return SMTFactory.createEmpty();
    }

    @Override
    public SMT visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        variables.addSMTDeclaration(ctx.ident.getText(), true);
        return SMTFactory.createEmpty();
    }

    @Override
    public SMT visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        final SMT expression = visit(ctx.expr());
        return assign(ctx.varref(), expression);
    }

    private SMT assign(SimpleCParser.VarrefContext ctx, SMT expression) {
        SMT currentVariable = visit(ctx);
        String freshVariable = variables.addSMTDeclaration(currentVariable.toString(), false);
        return SMTFactory.createBitVectorAssign(freshVariable, expression);

    }

    @Override
    public SMT visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        havoc(ctx.var.getText());
        return SMTFactory.createEmpty();
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
        Map<String, SMT> oldParameterMap = parameterMap;

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

        for (SimpleCParser.ExprContext exprContext : summarisation.getCandidatePreconditions()) {
            candidatePrePostConditions.add(exprContext);
            assertCondition(exprContext);
        }

        havoc(summarisation.getModset());

        String returnVar = ctx.callee.getText() + "_ret";
        SMT newReturnExpr = SMTFactory.createVariable(variables.addSMTDeclaration(returnVar, true));

        returnExpr = newReturnExpr;

        for (SimpleCParser.ExprContext exprContext : summarisation.getPostconditions()) {
            assumeCondition(exprContext);
        }

        for (SimpleCParser.ExprContext exprContext : summarisation.getCandidatePostconditions()) {
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

        SMT assertion = (condition == FALSE_EXPRESSION) ? SMTFactory.createBool(false) : visit(condition);

        if( !pred.isEmpty() ) {
            assertion = SMTFactory.createImplication(pred, assertion);
        }

        int assertionId = assertions.push(assertion);

        if( condition == FALSE_EXPRESSION ) {
            unwindingAssertionIds.add(assertionId);
        } else if (candidateInvariantConditions.contains(condition)) {
            assertionToCandidateInvariantMap.put(assertionId, (SimpleCParser.CandidateInvariantContext) condition.getParent());
        } else if (candidatePrePostConditions.contains(condition)) {
            assertionToCandidatePrePostMap.put(assertionId, (SimpleCParser.PrepostContext) condition.getParent().getParent());
        }

        return SMTFactory.createEmpty();
    }

    @Override
    public SMT visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        return assumeCondition(ctx.condition);
    }

    private SMT assumeCondition(SimpleCParser.ExprContext condition) {
        SMT assumption = condition == FALSE_EXPRESSION ? SMTFactory.createBool(false) : visit(condition);

        implicationStore.addAssume(assumption);
        return SMTFactory.createEmpty();
    }

    @Override
    public SMT visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {

        if( UNROLL_LOOPS ) return visitWhileStmtUnroll(ctx);

        if (ctx.invariantAnnotations.isEmpty()) {
            new CandidateInvariants(eliminatedCandidateInvariants).addInferredInvariants(ctx);
        }

        SMT result = SMTFactory.createEmpty();

        SimpleCParser.ExprContext condition = ctx.condition;

        ParserRuleContext dummyNode = new ParserRuleContext();

        for(SimpleCParser.LoopInvariantContext invariant : ctx.invariantAnnotations) {
            if (invariant.invariant() != null) {
                result = SMTFactory.merge(result, assertCondition(invariant.invariant().condition));
            } else {
                if (!eliminatedCandidateInvariants.contains(invariant.candidateInvariant())) {
                    candidateInvariantConditions.add(invariant.candidateInvariant().condition);
                    result = SMTFactory.merge(result, assertCondition(invariant.candidateInvariant().condition));
                }
            }
        }

        ModSetVisitor modSetVisitor = new ModSetVisitor();
        havoc(ctx.body.accept(modSetVisitor));

        for(SimpleCParser.LoopInvariantContext invariant : ctx.invariantAnnotations) {
            if (invariant.invariant() != null) {
                result = SMTFactory.merge(result, assumeCondition(invariant.invariant().condition));
            } else if (!eliminatedCandidateInvariants.contains(invariant.candidateInvariant())) {
                result = SMTFactory.merge(result, assumeCondition(invariant.candidateInvariant().condition));
            }
        }

        SimpleCParser.IfStmtContext ifBlock = new SimpleCParser.IfStmtContext(dummyNode, 0);
        ifBlock.condition = condition;
        ifBlock.thenBlock = ctx.body;

        // Keep count of assertions/assumptions nodes we manually add.
        int childrenAdded = 0;

        for(SimpleCParser.LoopInvariantContext invariant : ctx.invariantAnnotations) {
            SimpleCParser.AssertStmtContext assertion = new SimpleCParser.AssertStmtContext(ifBlock.thenBlock, 0);

            if (invariant.invariant() != null) {
                assertion.condition = invariant.invariant().condition;
                ifBlock.thenBlock.addChild(assertion);
                childrenAdded++;
            } else if (!eliminatedCandidateInvariants.contains(invariant.candidateInvariant())) {
                assertion.condition = invariant.candidateInvariant().condition;
                ifBlock.thenBlock.addChild(assertion);
                childrenAdded++;
            }

        }

        // Assume false to block further loop execution
        SimpleCParser.AssumeStmtContext assumption = new SimpleCParser.AssumeStmtContext(ifBlock.thenBlock, 0);
        assumption.condition = FALSE_EXPRESSION;
        ifBlock.thenBlock.addChild(assumption);
        childrenAdded++;

        SMT finalResult = SMTFactory.merge(result, visit(ifBlock));

        // Remove manual assertions/assumptions so we can reuse this ctx.
        for (int i = 0; i < childrenAdded; i++) {
            ifBlock.thenBlock.removeLastChild();
        }

        return finalResult;
    }

    private SMT visitWhileStmtUnroll(SimpleCParser.WhileStmtContext ctx) {
        ParserRuleContext dummyNode = new ParserRuleContext();

        // Add initial invarient assertions
        SMT result = SMTFactory.createEmpty();
        for(SimpleCParser.LoopInvariantContext invariant : ctx.invariantAnnotations) {
            if( invariant.invariant() == null ) continue;
            result = SMTFactory.merge(result, assertCondition(invariant.invariant().condition));
        }

        SimpleCParser.IfStmtContext ifStmt = new SimpleCParser.IfStmtContext(dummyNode, 0);
        unrollLoopAsNestedIfs(ifStmt, ctx.condition, ctx.body, ctx.invariantAnnotations, UNROLLING_DEPTH);

        return SMTFactory.merge(result, visit(ifStmt));
    }

    private void unrollLoopAsNestedIfs(SimpleCParser.IfStmtContext ifStmt,
                                       SimpleCParser.ExprContext condition,
                                       SimpleCParser.BlockStmtContext body,
                                       List<SimpleCParser.LoopInvariantContext> invariantAnnotations,
                                       int unrollDepth) {
        ifStmt.condition = condition;

        if( unrollDepth == 0 ) {
            // Assert and assume false at unroll depth

            SimpleCParser.BlockStmtContext blockStmt = new SimpleCParser.BlockStmtContext(ifStmt, 0);

            SimpleCParser.AssertStmtContext assertion = new SimpleCParser.AssertStmtContext(blockStmt, 0);
            assertion.condition = FALSE_EXPRESSION;
            blockStmt.addChild(assertion);

            SimpleCParser.AssumeStmtContext assumption = new SimpleCParser.AssumeStmtContext(blockStmt, 0);
            assumption.condition = FALSE_EXPRESSION;
            blockStmt.addChild(assumption);

            ifStmt.thenBlock = blockStmt;
            return;
        }

        // Use a new block stmt so we don't trample over body when adding things
        SimpleCParser.BlockStmtContext blockStmt = new SimpleCParser.BlockStmtContext(ifStmt, 0);
        for (int i = 0; i < body.getChildCount(); i++) {
            StmtContext child = body.getChild(StmtContext.class, i);

            // Ignore terminal nodes.
            if (child != null) {
                blockStmt.addChild(child);
            }
        }

        for(SimpleCParser.LoopInvariantContext invariant : invariantAnnotations) {
            if( invariant.invariant() == null ) continue;

            SimpleCParser.AssertStmtContext assertion = new SimpleCParser.AssertStmtContext(blockStmt, 0);
            assertion.condition = invariant.invariant().condition;

            // Add invariant assertions before checking condition again
            blockStmt.addChild(assertion);
        }

        SimpleCParser.IfStmtContext innerIfStmt = new SimpleCParser.IfStmtContext(blockStmt, 0);
        blockStmt.addChild(innerIfStmt);

        ifStmt.thenBlock = blockStmt;

        // Unroll inner if
        unrollLoopAsNestedIfs(innerIfStmt, condition, body, invariantAnnotations, unrollDepth - 1);
    }

    @Override
    public SMT visitIfStmt(SimpleCParser.IfStmtContext ctx) {

        SMT builder = SMTFactory.createEmpty();

        SMT predicate = visit(ctx.condition);
        SMT notPredicate = SMTFactory.createNot(predicate);

        Variables thenBlock;
        Variables elseBlock = variables;

        variables.enterScope();
        implicationStore.enterScope(predicate);
        builder = SMTFactory.merge(builder, super.visitBlockStmt(ctx.thenBlock));
        implicationStore.exitScope();
        thenBlock = variables.exitScope();

        if (ctx.elseBlock != null) {
            variables.enterScope();
            implicationStore.enterScope(notPredicate);
            builder = SMTFactory.merge(builder, super.visitBlockStmt(ctx.elseBlock));
            implicationStore.exitScope();
            elseBlock = variables.exitScope();
        }

        ModSetVisitor modSetVisitor = new ModSetVisitor();

        for( String var : union(ctx.thenBlock.accept(modSetVisitor),  ctx.elseBlock == null ? new HashSet<String>() : ctx.elseBlock.accept(modSetVisitor))) {
            SMT ite = SMTFactory.createITE(
                    predicate,
                    SMTFactory.createVariable((thenBlock.getActualDeclaredVariables().contains(var) ? variables : thenBlock).getCurrentVariable(var)),
                    SMTFactory.createVariable((elseBlock.getActualDeclaredVariables().contains(var) ? variables : elseBlock).getCurrentVariable(var))
            );

            // Add fresh variable for var
            variables.addSMTDeclaration(var, false);

            builder = SMTFactory.merge(builder, SMTFactory.createAssert(variables.getCurrentVariable(var),  ite));
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

        SMT result = SMTFactory.createEmpty();

        for(StmtContext stmt :ctx.stmts) {
            result = SMTFactory.merge(result, visit(stmt));
        }

        Variables vars = variables.exitScope();

        ModSetVisitor modSetVisitor = new ModSetVisitor();

        for( String var : ctx.accept(modSetVisitor)) {

            if( !vars.getActualDeclaredVariables().contains(var) ) {
                SMT assignment = SMTFactory.createBitVectorAssign(variables.addSMTDeclaration(var, false), SMTFactory.createVariable(vars.getCurrentVariable(var)));
                result = SMTFactory.merge(result, assignment);
            }
        }

        return result;
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
        return SMTFactory.createVariable(super.visitOldExpr(ctx).toString() + "-0");
    }

    @Override
    public SMT visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        String variable = super.visitVarrefExpr(ctx).toString();
        if (parameterMap != null && parameterMap.containsKey(variable)) {
            return parameterMap.get(variable);
        }

        return SMTFactory.createVariable(variables.getCurrentVariable(variable));
    }

    @Override
    public SMT visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
        return SMTFactory.createVariable(ctx.name.getText());
    }

    @Override
    public SMT visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        return SMTFactory.createNumber(ctx.number.getText());
    }

    @Override
    protected SMT defaultResult() {
        return SMTFactory.createEmpty();
    }

    @Override
    protected SMT aggregateResult(SMT aggregate, SMT nextResult) {
        return SMTFactory.merge(aggregate, nextResult);
    }
}
