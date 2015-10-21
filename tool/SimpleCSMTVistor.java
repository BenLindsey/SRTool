package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SimpleCSMTVistor extends SimpleCBaseVisitor<String> {

    Map<String, Integer> SSAIdsByName = new HashMap<>();

    private String getFreshVariable(String variable) {
        Integer id = SSAIdsByName.get(variable);

        id = id == null ? 0 : id;

        SSAIdsByName.put(variable, id + 1);

        return variable + id;
    }

    private String getCurrentVariable(String variable) {
        Integer id = SSAIdsByName.get(variable);

        return id == null ? getFreshVariable(variable) : variable + id;
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
    public String visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        final List<SimpleCParser.RelExprContext> args = ctx.args;

        if(args.size() == 2) {
            return "(= " + visit(args.get(0)) + " " + visit(args.get(1)) + ")";
        }

        return super.visitEqualityExpr(ctx);
    }

    @Override
    public String visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        StringBuilder statements = new StringBuilder();

        for(SimpleCParser.StmtContext statement : ctx.stmts) {
            statements.append(visit(statement));
        }

        return statements.toString();
    }

    @Override
    public String visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        return "(declare-fun " + visit(ctx.varIdentifier())  + " () (_ BitVec 32))\n";
    }

    @Override
    public String visitAddExpr(SimpleCParser.AddExprContext ctx) {
        return super.visitAddExpr(ctx);
    }

    @Override
    public String visitMulExpr(SimpleCParser.MulExprContext ctx) {
        return super.visitMulExpr(ctx);
    }

    @Override
    public String visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        return "(assert (= " + visit(ctx.varref()) + " " + visit(ctx.expr()) + "))\n";
    }

    @Override
    public String visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        return "(assert (not " + super.visitAssertStmt(ctx)  + "))\n";
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
