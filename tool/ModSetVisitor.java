package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.HashSet;
import java.util.Set;

public class ModSetVisitor extends SimpleCBaseVisitor<Set<String>> {

    @Override
    public Set<String> visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        Set<String> modset = new HashSet<>();
        modset.add(ctx.lhs.getText());
        return modset;
    }

    @Override
    public Set<String> visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        Set<String> modset = new HashSet<>();
        modset.add(ctx.var.getText());
        return modset;
    }

    @Override
    protected Set<String> defaultResult() {
        return new HashSet<>();
    }

    @Override
    protected Set<String> aggregateResult(Set<String> aggregate, Set<String> nextResult) {
        aggregate.addAll(nextResult);
        return aggregate;
    }
}
