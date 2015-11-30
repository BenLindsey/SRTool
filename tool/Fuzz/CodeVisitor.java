package tool.Fuzz;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CodeVisitor extends SimpleCBaseVisitor<Code> {
    public static final String RESULT_VARIABLE = "RESULT";

    private CodeExpressionUtils expressionUtils = new CodeExpressionUtils(this);
    private List<Integer> fuzzInputs;
    private int fuzzIndex = 0;

    public CodeVisitor(List<Integer> fuzzInputs) {
        this.fuzzInputs = fuzzInputs;
    }

    private int getFuzzInput() {
        if(fuzzIndex >= fuzzInputs.size()) {
            fuzzIndex = 0;
        }

        return fuzzInputs.get(fuzzIndex++);
    }

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
        return CodeFactory.createDeclaration(ctx.ident.getText(), getFuzzInput());
    }

    @Override
    public Code visitExpr(SimpleCParser.ExprContext ctx) {
        Code code = super.visitExpr(ctx);

        return code.isEmpty() ?  new SingleCode(ctx.getText()) : code;
    }

    @Override
    public Code visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        List<Code> statements = new ArrayList<>();

        List<String> params = new ArrayList<>();

        for(SimpleCParser.FormalParamContext paramContext : ctx.formalParam()) {
            params.add(paramContext.ident.getText());
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

        statements.add(CodeFactory.createDeclaration(RESULT_VARIABLE, 0));
        statements.add(CodeFactory.createAssign(RESULT_VARIABLE, returnCode));

        for(SimpleCParser.PrepostContext prepostContext : ctx.prepost()) {
            if(prepostContext.ensures() != null) {
                statements.add(visit(prepostContext));
            }
        }

        statements.add(CodeFactory.createReturn(CodeFactory.createVariable(RESULT_VARIABLE)));

        return CodeFactory.createFunction(ctx.name.getText(), params, statements);
    }

    @Override
    public Code visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        return CodeFactory.createAssert(visit(ctx.expr()));
    }

    @Override
    public Code visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {
        Code condition = visit(ctx.condition);
        Code body = visit(ctx.body);

        List<Code> invarients = new ArrayList<>();

        for(SimpleCParser.LoopInvariantContext loopInvariantContext: ctx.loopInvariant()) {
            if(loopInvariantContext.invariant() != null) {
                invarients.add(visit(loopInvariantContext.invariant()));
            }
        }

        return CodeFactory.createWhile(condition, body, new CompositeCode(invarients));
    }

    @Override
    public Code visitIfStmt(SimpleCParser.IfStmtContext ctx) {
        Code condition = visit(ctx.condition);
        Code thenBlock = visit(ctx.thenBlock);

        return ctx.elseBlock == null ? CodeFactory.createIf(condition, thenBlock) :
                CodeFactory.createIf(condition, thenBlock, visit(ctx.elseBlock));
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

    @Override
    public Code visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        return CodeFactory.createHavoc(ctx.var.getText(), getFuzzInput());
    }

    @Override
    public Code visitParenExpr(SimpleCParser.ParenExprContext ctx) {
        return CodeFactory.createParenthesis(visit(ctx.arg));
    }

    @Override
    public Code visitCallStmt(SimpleCParser.CallStmtContext ctx) {
        return new SingleCode(ctx.getText() + "\n");
    }

    @Override
    public Code visitInvariant(SimpleCParser.InvariantContext ctx) {
        return CodeFactory.createAssert(visit(ctx.condition));
    }

    @Override
    public Code visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
        List<Code> code = new ArrayList<>();

        for(SimpleCParser.StmtContext stmnt : ctx.stmts) {
            code.add(visit(stmnt));
        }

        return CodeFactory.createBlock(new CompositeCode(code));
    }

    /**
     * UNHANDLED CASES
     *
     *
     *
     *
     */

    @Override
    public Code visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        return CodeFactory.createAssume(visit(ctx.condition));
    }

    @Override
    public Code visitPrepost(SimpleCParser.PrepostContext ctx) {
        if(ctx.requires() != null) {
            return CodeFactory.createAssume(visit(ctx.requires().condition));
        } else if(ctx.ensures() != null) {
            return CodeFactory.createAssert(visit(ctx.ensures().condition));
        }

        throw new RuntimeException("Invalid fuzz program");
    }

    @Override
    public Code visitRequires(SimpleCParser.RequiresContext ctx) {
        throw new RuntimeException("Invalid fuzz program");
    }

    @Override
    public Code visitEnsures(SimpleCParser.EnsuresContext ctx) {
        throw new RuntimeException("Invalid fuzz program");
    }

    @Override
    public Code visitCandidateRequires(SimpleCParser.CandidateRequiresContext ctx) {
        throw new RuntimeException("Invalid fuzz program");
    }

    @Override
    public Code visitCandidateEnsures(SimpleCParser.CandidateEnsuresContext ctx) {
        throw new RuntimeException("Invalid fuzz program");
    }

    @Override
    public Code visitLoopInvariant(SimpleCParser.LoopInvariantContext ctx) {
        throw new RuntimeException("Invalid fuzz program");
    }

    @Override
    public Code visitCandidateInvariant(SimpleCParser.CandidateInvariantContext ctx) {
        throw new RuntimeException("Invalid fuzz program");
    }

    @Override
    public Code visitOldExpr(SimpleCParser.OldExprContext ctx) {
        throw new RuntimeException("Invalid fuzz program");
    }
}

