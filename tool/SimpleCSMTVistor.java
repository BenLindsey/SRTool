package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

public class SimpleCSMTVistor extends SimpleCBaseVisitor<String> {

    private String returnExpr;
    private ExpressionUtils expressionUtils = new ExpressionUtils(this);

    private SSAMap ssaMap = new SSAMap();
    private List<String> globals = new ArrayList<>();
    private Deque<Map<String, String>> globalsMapStack = new ArrayDeque<>();
    
    private ConditionStore conditionStore = new ConditionStore();
    private Set<String> modset = new HashSet<>();

    private List<String> declarations = new ArrayList<>();

    private void addDeclaration(String variable) {
        declarations.add("(declare-fun " + variable + " () (_ BitVec 32))\n");
    }

    @Override
    public String visitProgram(SimpleCParser.ProgramContext ctx) {
        StringBuilder program = new StringBuilder();

        for (SimpleCParser.VarDeclContext global : ctx.globals) {
            globals.add(global.ident.getText());
            program.append(visit(global));
        }

        program.append(super.visitProgram(ctx));

        return program.toString();
    }

    @Override
    public String visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        StringBuilder statements = new StringBuilder();

        // Save globals
        Map<String, String> globalsMap = new HashMap<>();
        for (String global : globals) {
            globalsMap.put(global, ssaMap.getCurrentVariable(global));
        }

        globalsMapStack.push(globalsMap);

        for(SimpleCParser.FormalParamContext param : ctx.formals) {
            statements.append(visit(param));
        }

        // Visit pre conditions
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if( prepost.requires() == null ) continue;
            statements.append(visit(prepost.requires()));
        }

        for(SimpleCParser.StmtContext statement : ctx.stmts) {
            statements.append(visit(statement));
        }

        // Save returnExpr for use in \return annotations
        returnExpr = visit(ctx.returnExpr);

        // Visit post conditions
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if( prepost.ensures() == null ) continue;
            statements.append(visit(prepost.ensures()));
        }

        // Add declarations to the top of the output
        StringBuilder declarationStrings = new StringBuilder();

        for( String dec : declarations ) {
            declarationStrings.append(dec);
        }

        globalsMapStack.pop();

        return "\n" + declarationStrings.toString() + "\n" + statements.toString();
    }

    @Override
    public String visitRequires(SimpleCParser.RequiresContext ctx) {
        return "(assert " + visit(ctx.condition) + ")\n";
    }

    @Override
    public String visitEnsures(SimpleCParser.EnsuresContext ctx) {
        return "(assert (not " + visit(ctx.condition) + "))\n";
    }

    @Override
    public String visitFormalParam(SimpleCParser.FormalParamContext ctx) {
        addDeclaration(ssaMap.fresh(ctx.ident.getText()));
        return "";
    }

    @Override
    public String visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        addDeclaration(ssaMap.fresh(ctx.ident.getText()));
        return "";
    }

    @Override
    public String visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        final String expression = visit(ctx.expr());

        String currentVariable = visit(ctx.varref());
        String freshVariable = ssaMap.fresh(currentVariable);
        modset.add(currentVariable);

        addDeclaration(freshVariable);
        return "(assert (= " + freshVariable + " " + expression + "))\n";
    }

    @Override
    public String visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        addDeclaration(ssaMap.fresh(ctx.var.getText()));
        return "";
    }

    @Override
    public String visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        String pred = conditionStore.getFullPredicate();
        String condition = visit(ctx.condition);

        if(pred.isEmpty()) return "(assert (not " + condition + "))\n";

        return "(assert (not (=> " + pred + " " + condition + ")))\n";
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
        Set<String> newModset = new HashSet<>();
        modset = newModset;

        conditionStore.pushPredicate(predicate);
        builder.append(visit(ctx.thenBlock));
        conditionStore.popPredicate();

        SSAMap mapForIfClause = ssaMap.clone();

        if (ctx.elseBlock != null) {
            conditionStore.pushPredicate("(not " + predicate + ")");
            builder.append(visit(ctx.elseBlock));
            conditionStore.popPredicate();
        }

        modset = currentModset;

        for( String var : newModset ) {
            String ite = "(ite " + predicate + " " + mapForIfClause.getCurrentVariable(var) + " " +
                                                     ssaMap.getCurrentVariable(var) + ")";

            // Add fresh variable for var
            addDeclaration(ssaMap.fresh(var));

            builder.append("(assert (= " + ssaMap.getCurrentVariable(var) + " " + ite + "))\n");
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
    public String visitOldExpr(SimpleCParser.OldExprContext ctx) {
        return ssaMap.getCurrentVariable(super.visitOldExpr(ctx));
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
