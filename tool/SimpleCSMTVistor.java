package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

public class SimpleCSMTVistor extends SimpleCBaseVisitor<String> {

    Map<String, Integer> SSAIdsByName = new HashMap<>();

    Deque<String> predicate = new ArrayDeque<>();
    List<String> modset = new ArrayList<>();

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

        return statements.toString();
    }


    @Override
    public String visitFormalParam(SimpleCParser.FormalParamContext ctx) {
        return getDeclarationString(getCurrentVariable(ctx.ident.getText()));
    }

    @Override
    public String visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        return getDeclarationString(getCurrentVariable(ctx.ident.getText()));
    }

    @Override
    public String visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        String currentVariable = visit(ctx.varref());
        String freshVariable = getFreshVariable(currentVariable);
        modset.add(currentVariable);
        return getDeclarationString(freshVariable) +
               "(assert (= " + getCurrentVariable(currentVariable) + " " + visit(ctx.expr()) + "))\n";
    }

    @Override
    public String visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        return "(assert (not " + super.visitAssertStmt(ctx)  + "))\n";
    }

    @Override
    public String visitIfStmt(SimpleCParser.IfStmtContext ctx) {

        StringBuilder builder = new StringBuilder();

        String condition = visit(ctx.condition);

        List<String> currentModset = modset;
        List<String> newModset = new ArrayList<String>();
        modset = newModset;

        predicate.push(condition);
        builder.append(visit(ctx.thenBlock));
        predicate.pop();

        Map<String, Integer> mapForIfClause = new HashMap<>(SSAIdsByName);

        if( ctx.elseBlock != null ) {
            predicate.push("(not " + condition + ")");
            builder.append(visit(ctx.elseBlock));
            predicate.pop();
        }

        modset = currentModset;

        for( String var : newModset ) {

            Integer i = mapForIfClause.get(var);
            if( i == null ) i = 0;

            String ite = "(ite " + condition + " " + var + i + " " + getCurrentVariable(var) + ")";

            // Add fresh variable for var
            builder.append(getDeclarationString(getFreshVariable(var)));

            builder.append("(assert (= " + getCurrentVariable(var) + " " + ite + "))\n");
        }

        return builder.toString();
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
