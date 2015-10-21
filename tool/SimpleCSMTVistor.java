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
    public String visitProgram(SimpleCParser.ProgramContext ctx) {
        return super.visitProgram(ctx);
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
    public String visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        return "(assert (= " + visit(ctx.varref()) + " " + visit(ctx.expr()) + "))\n";
    }

    @Override
    public String visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        return "(assert (not " + super.visitAssertStmt(ctx)  + "))\n";
    }

    @Override
    public String visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        return ctx.args.size() == 2 ?
                "(= " + visit(ctx.args.get(0)) + " " + visit(ctx.args.get(1)) + ")" :
                super.visitEqualityExpr(ctx);
    }

    @Override
    public String visitAddExpr(SimpleCParser.AddExprContext ctx) {
        return ctx.args.size() == 2 ?
                "(bvadd " + visit(ctx.args.get(0)) + " " + visit(ctx.args.get(1)) + ")" :
                super.visitAddExpr(ctx);
    }

    @Override
    public String visitMulExpr(SimpleCParser.MulExprContext ctx) {
        return ctx.args.size() == 2 ?
                "(bvmul " + visit(ctx.args.get(0)) + " " + visit(ctx.args.get(1)) + ")" :
                super.visitMulExpr(ctx);
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
