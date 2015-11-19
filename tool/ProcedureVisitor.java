package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

public class ProcedureVisitor extends SimpleCBaseVisitor<Map<String, ProcedureSummarisation>> {

    @Override
    public Map<String, ProcedureSummarisation> visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        Map<String, ProcedureSummarisation> summarisationMap = new HashMap<>();

        ProcedureSummarisation summarisation = new ProcedureSummarisation();

        List<String> parameters = new ArrayList<>();
        for (SimpleCParser.FormalParamContext formal : ctx.formals) {
            parameters.add(formal.ident.getText());
        }
        summarisation.setParameters(parameters);

        ModSetVisitor modSetVisitor = new ModSetVisitor();
        Set<String> modset = ctx.accept(modSetVisitor);
        summarisation.setModset(modset);

        List<SimpleCParser.ExprContext> preconditions = new ArrayList<>();
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if (prepost.requires() != null) {
                preconditions.add(prepost.requires().condition);
            }
        }
        summarisation.setPreconditions(preconditions);

        List<SimpleCParser.ExprContext> postconditions = new ArrayList<>();
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if (prepost.ensures() != null) {
                postconditions.add(prepost.ensures().condition);
            }
        }
        summarisation.setPostconditions(postconditions);

        summarisationMap.put(ctx.name.getText(), summarisation);

        return summarisationMap;
    }

    @Override
    protected Map<String, ProcedureSummarisation> defaultResult() {
        return new HashMap<>();
    }

    @Override
    protected Map<String, ProcedureSummarisation> aggregateResult(Map<String, ProcedureSummarisation> aggregate, Map<String, ProcedureSummarisation> nextResult) {
        aggregate.putAll(nextResult);
        return aggregate;
    }
}
