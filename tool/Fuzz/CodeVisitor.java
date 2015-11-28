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

    public static final String RESULT_VARIABLE = "RESULT";

    private CodeExpressionUtils expressionUtils = new CodeExpressionUtils(this);

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
        Code code = super.visitExpr(ctx);

        return code.isEmpty() ?  new SingleCode(ctx.getText()) : code;
    }

    @Override
    public Code visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        ArrayList<Code> statements = new ArrayList<>();

        for(SimpleCParser.FormalParamContext paramContext : ctx.formalParam()) {
            statements.add(CodeFactory.createDeclaration(paramContext.ident.getText()));
        }

        for(SimpleCParser.PrepostContext prepostContext : ctx.prepost()) {
            if(prepostContext.requires() != null) {
                statements.add(visit(prepostContext));
            }
        }

        for(SimpleCParser.StmtContext statementCtx : ctx.stmts) {
            statements.add(visit(statementCtx));
        }

        Code returnCode = visit(ctx.returnExpr);

        statements.add(CodeFactory.createDeclaration(RESULT_VARIABLE));
        statements.add(CodeFactory.createAssign(RESULT_VARIABLE, returnCode));

        for(SimpleCParser.PrepostContext prepostContext : ctx.prepost()) {
            if(prepostContext.ensures() != null) {
                statements.add(visit(prepostContext));
            }
        }

        statements.add(CodeFactory.createReturn(CodeFactory.createVariable(RESULT_VARIABLE)));

        return CodeFactory.createFunction(ctx.name.getText(), statements);
    }

    @Override
    public Code visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        return CodeFactory.createAssert(visit(ctx.expr()));
    }


    @Override
    public Code visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {
        Code condition = visit(ctx.condition);
        Code body = visit(ctx.body);

        return CodeFactory.createWhile(condition, body);
    }

    @Override
    public Code visitIfStmt(SimpleCParser.IfStmtContext ctx) {
        Code condition = visit(ctx.condition);
        Code thenBlock = visit(ctx.thenBlock);
        Code elseBlock = visit(ctx.elseBlock);

        return CodeFactory.createIf(condition, thenBlock, elseBlock);
    }

    @Override
    public Code visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        return CodeFactory.createEmpty();
        //return CodeFactory.createAssume(visit(ctx.condition));
    }

    @Override
    public Code visitRequires(SimpleCParser.RequiresContext ctx) {
        Code condition = visit(ctx.condition);

        return CodeFactory.createEmpty();
        //return CodeFactory.createAssume(condition);
    }

    @Override
    public Code visitEnsures(SimpleCParser.EnsuresContext ctx) {
        Code condition = visit(ctx.condition);

        return CodeFactory.createAssert(condition);
    }

    @Override
    public Code visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return CodeFactory.createVariable(RESULT_VARIABLE);
    }

    @Override
    public Code visitTernExpr(SimpleCParser.TernExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.ternaryToCode(ctx.args) : super.visitTernExpr(ctx);
    }

    @Override
    public Code visitLorExpr(SimpleCParser.LorExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitLorExpr(ctx);
    }

    @Override
    public Code visitLandExpr(SimpleCParser.LandExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitLandExpr(ctx);
    }

    @Override
    public Code visitBorExpr(SimpleCParser.BorExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitBorExpr(ctx);
    }

    @Override
    public Code visitBandExpr(SimpleCParser.BandExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitBandExpr(ctx);
    }

    @Override
    public Code visitBxorExpr(SimpleCParser.BxorExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitBxorExpr(ctx);
    }

    @Override
    public Code visitRelExpr(SimpleCParser.RelExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitRelExpr(ctx);
    }

    @Override
    public Code visitShiftExpr(SimpleCParser.ShiftExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitShiftExpr(ctx);
    }

    @Override
    public Code visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitEqualityExpr(ctx);
    }

    @Override
    public Code visitAddExpr(SimpleCParser.AddExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitAddExpr(ctx);
    }

    @Override
    public Code visitMulExpr(SimpleCParser.MulExprContext ctx) {
        return ctx.args.size() >= 2 ? expressionUtils.infixToCode(ctx.ops, ctx.args) : super.visitMulExpr(ctx);
    }

    @Override
    public Code visitUnaryExpr(SimpleCParser.UnaryExprContext ctx) {
        return ctx.ops.size() > 0 ? expressionUtils.unaryToCode(ctx.ops, ctx.arg) : super.visitUnaryExpr(ctx);
    }

    @Override
    public Code visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return CodeFactory.createVariable(ctx.getText());
    }

    @Override
    public Code visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
        return CodeFactory.createVariable(ctx.name.getText());
    }

    @Override
    public Code visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        return CodeFactory.createNumber(ctx.number.getText());
    }

    //todo OLD, ASSUME, REQUIRES,
}

