package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

public class ProcedureVisitor extends SimpleCBaseVisitor<Map<String, ProcedureSummarisation>> {

    private Set<SimpleCParser.PrepostContext> eliminatedPrePostConditions;

    public ProcedureVisitor(Set<SimpleCParser.PrepostContext> eliminatedPrePostConditions) {
        this.eliminatedPrePostConditions = eliminatedPrePostConditions;
    }

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
        List<SimpleCParser.ExprContext> candidatePreconditions = new ArrayList<>();
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if (prepost.requires() != null) {
                preconditions.add(prepost.requires().condition);
            } else if (prepost.candidateRequires() != null && !eliminatedPrePostConditions.contains(prepost)) {
                candidatePreconditions.add(prepost.candidateRequires().condition);
            }
        }
        summarisation.setPreconditions(preconditions);
        summarisation.setCandidatePreconditions(candidatePreconditions);

        List<SimpleCParser.ExprContext> postconditions = new ArrayList<>();
        List<SimpleCParser.ExprContext> candidatePostconditions = new ArrayList<>();
        for (SimpleCParser.PrepostContext prepost : ctx.contract) {
            if (prepost.ensures() != null) {
                postconditions.add(prepost.ensures().condition);
            } else if (prepost.candidateEnsures() != null && !eliminatedPrePostConditions.contains(prepost)) {
                candidatePostconditions.add(prepost.candidateEnsures().condition);
            }
        }
        summarisation.setPostconditions(postconditions);
        summarisation.setCandidatePostconditions(candidatePostconditions);

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
