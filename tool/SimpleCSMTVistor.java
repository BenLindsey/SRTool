package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.List;

public class SimpleCSMTVistor extends SimpleCBaseVisitor<String> {
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
