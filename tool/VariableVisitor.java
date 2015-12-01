package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.HashSet;
import java.util.Set;

public class VariableVisitor extends SimpleCBaseVisitor<Set<String>> {

    @Override
    public Set<String> visitVarref(SimpleCParser.VarrefContext ctx) {
        Set<String> result = new HashSet<>();
        result.add(ctx.ident.getText());
        return result;
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
