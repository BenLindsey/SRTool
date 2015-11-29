package tool;

import parser.SimpleCParser;
import tool.SMTs.SMT;

import java.util.Map;

public class HoudiniLoopRunner {
    private SimpleCSMTVisitor visitor;
    private final Map<String, ProcedureSummarisation> summarisationMap;
    private final SimpleCParser.ProcedureDeclContext proc;
    private final String programHead;

    public HoudiniLoopRunner(SimpleCSMTVisitor visitor, SimpleCParser.ProcedureDeclContext proc, Map<String, ProcedureSummarisation> summarisationMap, String programHead) {
        this.visitor = visitor;
        this.proc = proc;
        this.summarisationMap = summarisationMap;
        this.programHead = programHead;
    }

    public String eliminateCandidates(SMT funcSMT) {
        Z3Result result = staticallyVerify(funcSMT);

        switch (result) {
            case INCORRECT:
                if (failedDueToCandidateInvariant(result)) {
                    SimpleCSMTVisitor newVisitor = new SimpleCSMTVisitor(summarisationMap);
                    newVisitor.getEliminatedCandidateInvariants().addAll(visitor.getEliminatedCandidateInvariants());
                    visitor = newVisitor;
                    Variables.refresh();
                    return eliminateCandidates(proc.accept(visitor));
                }
            default:
                return funcSMT.toString();
        }
    }

    private boolean failedDueToCandidateInvariant(Z3Result result) {
        boolean eliminatedInvariants = false;
        for (Integer assertionId : result.getFailingAssertions()) {
            if (visitor.getAssertionToCandidateInvariantMap().containsKey(assertionId)) {
                eliminate(visitor.getAssertionToCandidateInvariantMap().get(assertionId));
                eliminatedInvariants = true;
                System.err.println("Eliminated invariant at assertion " + assertionId);
            }
        }
        return eliminatedInvariants;
    }

    private void eliminate(SimpleCParser.CandidateInvariantContext ctx) {
        visitor.getEliminatedCandidateInvariants().add(ctx);
    }

    private String buildProgram(SMT funcSMT) {
        return programHead + funcSMT + buildProgramTail();
    }

    private String buildProgramTail() {
        StringBuilder programTailBuilder = new StringBuilder();
        programTailBuilder
                .append("\n(check-sat)")
                .append("\n(get-model)")
                .append("\n(get-value (");

        for(int i = 0; i < visitor.assertionsSize(); i++) {
            programTailBuilder.append(" ").append(AssertionCollection.getAssertionName(i));
        }

        programTailBuilder.append("))\n");

        return programTailBuilder.toString();
    }

    private Z3Result staticallyVerify(SMT funcSMT) {
        return new Z3().getResult(buildProgram(funcSMT));
    }
}
