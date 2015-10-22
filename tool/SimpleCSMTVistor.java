package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

public class SimpleCSMTVistor extends SimpleCBaseVisitor<String> {

    private String returnExpr;
    private ExpressionUtils expressionUtils = new ExpressionUtils(this);
    private boolean nestedExpression = false;

    private SSAMap ssaMap = new SSAMap();

    private PredicateStack predicateStack = new PredicateStack();
    private Set<String> modset = new HashSet<>();


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
        return getDeclarationString(ssaMap.fresh(ctx.ident.getText()));
    }

    @Override
    public String visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        return getDeclarationString(ssaMap.fresh(ctx.ident.getText()));
    }

    @Override
    public String visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        nestedExpression = true;
        final String expression = visit(ctx.expr());
        nestedExpression = false;

        String currentVariable = visit(ctx.varref());
        String freshVariable = ssaMap.fresh(currentVariable);
        modset.add(currentVariable);
        
        return getDeclarationString(freshVariable) +
               "(assert (= " + freshVariable + " " + expression + "))\n";
    }

    @Override
    public String visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        return getDeclarationString(ssaMap.fresh(ctx.var.getText()));
    }

    @Override
    public String visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        String pred = predicateStack.getFullPredicate();

        if(pred.isEmpty()) return "(assert (not " + super.visitAssertStmt(ctx) + "))\n";

        return "(assert (=> " + pred + " (not " + super.visitAssertStmt(ctx) + ")))\n";
    }

    @Override
    public String visitIfStmt(SimpleCParser.IfStmtContext ctx) {

        StringBuilder builder = new StringBuilder();

        String condition = visit(ctx.condition);

        Set<String> currentModset = modset;
        Set<String> newModset = new HashSet<String>();
        modset = newModset;

        predicateStack.push(condition);
        builder.append(visit(ctx.thenBlock));
        predicateStack.pop();

        SSAMap mapForIfClause = ssaMap.clone();

        if (ctx.elseBlock != null ) {
            predicateStack.push("(not " + condition + ")");
            builder.append(visit(ctx.elseBlock));
            predicateStack.pop();
        }

        modset = currentModset;

        for( String var : newModset ) {
            String ite = "(ite " + condition + " " + mapForIfClause.getCurrentVariable(var) + " " +
                                                     ssaMap.getCurrentVariable(var) + ")";

            // Add fresh variable for var
            builder.append(getDeclarationString(ssaMap.fresh(var)));

            builder.append("(assert (= " + ssaMap.getCurrentVariable(var) + " " + ite + "))\n");
        }

        return builder.toString();
    }

    @Override
    public String visitExpr(SimpleCParser.ExprContext ctx) {
        String result = super.visitExpr(ctx);
        if (nestedExpression) return result;

        if (result.equals("(_ bv0 32)")) {
            return "false";
        }

        if (result.matches("\\(_ bv\\d+ 32\\)")) {
            return "true";
        }

        return result;
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
    public String visitParenExpr(SimpleCParser.ParenExprContext ctx) {
        nestedExpression = true;
        String result = super.visitParenExpr(ctx);
        nestedExpression = false;
        return result;
    }

    @Override
    public String visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return returnExpr;
    }

    @Override
    public String visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return ssaMap.getCurrentVariable(super.visitVarrefExpr(ctx));
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
