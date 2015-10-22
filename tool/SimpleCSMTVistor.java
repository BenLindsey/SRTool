package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

public class SimpleCSMTVistor extends SimpleCBaseVisitor<String> {

    private final Map<String, Integer> SSAIdsByName = new HashMap<>();
    private String returnExpr;
    private ExpressionUtils expressionUtils = new ExpressionUtils(this);

    private ConditionStore conditionStore = new ConditionStore();
    private Set<String> modset = new HashSet<>();

    private String getFreshVariable(String variable) {
        Integer id = SSAIdsByName.get(variable);

        id = id == null ? 0 : id + 1;

        SSAIdsByName.put(variable, id);

        return variable + id;
    }

    private String getCurrentVariable(String variable) {
        Integer id = SSAIdsByName.get(variable);

        return id == null ? getFreshVariable(variable) : variable + id;
    }

    private String getDeclarationString(String variable) {
        return "(declare-fun " + variable  + " () (_ BitVec 32))\n";
    }

    public String visitProgram(SimpleCParser.ProgramContext ctx) {
        return super.visitProgram(ctx);
    }

    @Override
    public String visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        StringBuilder statements = new StringBuilder();

        for(SimpleCParser.FormalParamContext param : ctx.formals) {
            statements.append(visit(param));
        }

        for(SimpleCParser.StmtContext statement : ctx.stmts) {
            statements.append(visit(statement));
        }

        returnExpr = visit(ctx.returnExpr);

        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            statements.append(visitEnsures(prepost.ensures()));
        }

        return statements.toString();
    }

    @Override
    public String visitEnsures(SimpleCParser.EnsuresContext ctx) {
        return "(assert (not " + visit(ctx.condition) + "))\n";
    }

    @Override
    public String visitFormalParam(SimpleCParser.FormalParamContext ctx) {
        return getDeclarationString(getFreshVariable(ctx.ident.getText()));
    }

    @Override
    public String visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        return getDeclarationString(getFreshVariable(ctx.ident.getText()));
    }

    @Override
    public String visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        final String expression = visit(ctx.expr());

        String currentVariable = visit(ctx.varref());
        String freshVariable = getFreshVariable(currentVariable);
        modset.add(currentVariable);
        
        return getDeclarationString(freshVariable) +
               "(assert (= " + freshVariable + " " + expression + "))\n";
    }

    @Override
    public String visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        return getDeclarationString(getFreshVariable(ctx.var.getText()));
    }

    @Override
    public String visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        String pred = conditionStore.getFullPredicate();

        if(pred.isEmpty()) return "(assert (not " + super.visitAssertStmt(ctx) + "))\n";

        return "(assert (not (=> " + pred + " " + super.visitAssertStmt(ctx) + ")))\n";
    }

    @Override
    public String visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        String assumption = visit(ctx.condition);

        conditionStore.addAssumption(assumption);

        return "";
    }

    @Override
    public String visitIfStmt(SimpleCParser.IfStmtContext ctx) {

        StringBuilder builder = new StringBuilder();

        String predicate = visit(ctx.condition);

        Set<String> currentModset = modset;
        Set<String> newModset = new HashSet<String>();
        modset = newModset;

        conditionStore.pushPredicate(predicate);
        builder.append(visit(ctx.thenBlock));
        conditionStore.popPredicate();

        Map<String, Integer> mapForIfClause = new HashMap<>(SSAIdsByName);

        if (ctx.elseBlock != null ) {
            conditionStore.pushPredicate("(not " + predicate + ")");
            builder.append(visit(ctx.elseBlock));
            conditionStore.popPredicate();
        }

        modset = currentModset;

        for( String var : newModset ) {

            Integer i = mapForIfClause.get(var);
            if( i == null ) i = 0;

            String ite = "(ite " + predicate + " " + var + i + " " + getCurrentVariable(var) + ")";

            // Add fresh variable for var
            builder.append(getDeclarationString(getFreshVariable(var)));

            builder.append("(assert (= " + getCurrentVariable(var) + " " + ite + "))\n");
        }

        return builder.toString();
    }

    @Override
    public String visitTernExpr(SimpleCParser.TernExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.ternaryToITE(ctx.args) : super.visitTernExpr(ctx);
    }

    @Override
    public String visitLorExpr(SimpleCParser.LorExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitLorExpr(ctx);
    }

    @Override
    public String visitLandExpr(SimpleCParser.LandExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitLandExpr(ctx);
    }

    @Override
    public String visitBorExpr(SimpleCParser.BorExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitBorExpr(ctx);
    }

    @Override
    public String visitBandExpr(SimpleCParser.BandExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitBandExpr(ctx);
    }

    @Override
    public String visitRelExpr(SimpleCParser.RelExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitRelExpr(ctx);
    }

    @Override
    public String visitShiftExpr(SimpleCParser.ShiftExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitShiftExpr(ctx);
    }

    @Override
    public String visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitEqualityExpr(ctx);
    }

    @Override
    public String visitAddExpr(SimpleCParser.AddExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitAddExpr(ctx);
    }

    @Override
    public String visitMulExpr(SimpleCParser.MulExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToPrefix(ctx.ops, ctx.args) : super.visitMulExpr(ctx);
    }

    @Override
    public String visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return returnExpr;
    }

    @Override
    public String visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return getCurrentVariable(super.visitVarrefExpr(ctx));
    }

    @Override
    public String visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
        return ctx.name.getText();
    }

    @Override
    public String visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        return "(_ bv" + ctx.number.getText() + " 32)";
    }

    @Override
    protected String defaultResult() {
        return "";
    }

    @Override
    protected String aggregateResult(String aggregate, String nextResult) {
        return aggregate + nextResult;
    }
}
