package tool.Fuzz;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;
import tool.SMTs.SMT;
import tool.SMTs.SMTFactory;

import java.util.ArrayList;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CodeVisitor extends SimpleCBaseVisitor<Code> {
    @Override
    protected Code defaultResult() {
        return CodeFactory.createEmpty();
    }

    @Override
    protected Code aggregateResult(Code aggregate, Code nextResult) {
        return CodeFactory.merge(aggregate, nextResult);
    }

    @Override
    public Code visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        return CodeFactory.createAssign(ctx.lhs.getText(), visit(ctx.rhs));
    }

    @Override
    public Code visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        return CodeFactory.createDeclaration(ctx.ident.getText());
    }

    @Override
    public Code visitExpr(SimpleCParser.ExprContext ctx) {
        return new SingleCode(ctx.getText());
    }

    @Override
    public Code visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        ArrayList<Code> statements = new ArrayList<>();

        for(SimpleCParser.StmtContext statementCtx : ctx.stmts) {
            statements.add(visit(statementCtx));
        }

        statements.add(CodeFactory.createReturn(visit(ctx.returnExpr)));

        return CodeFactory.createFunction(ctx.name.getText(), statements);
    }

    @Override
    public Code visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        return CodeFactory.createAssert(ctx.expr().getText());
    }

    @Override
    public Code visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {
        Code condition = visit(ctx.condition);
        Code body = visit(ctx.body);

        return CodeFactory.createWhile(condition, body);
    }
}
