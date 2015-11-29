package tool;

import parser.SimpleCParser;

import java.util.*;

public class HoudiniProcedureRunner {
    private SimpleCParser.ProgramContext program;
    private Map<String, ProcedureSummarisation> summarisationMap;
    private Set<SimpleCParser.PrepostContext> eliminatedPrePosts = new HashSet<>();

    private final int UNROLLING_DEPTH;
    private final boolean UNROLL_LOOPS;

    public HoudiniProcedureRunner(SimpleCParser.ProgramContext program) {
        this.program = program;
        summarisationMap = program.accept(new ProcedureVisitor(Collections.<SimpleCParser.PrepostContext>emptySet()));
        UNROLL_LOOPS = false;
        UNROLLING_DEPTH = 0;
    }

    public HoudiniProcedureRunner(SimpleCParser.ProgramContext program, int unrollingDepth) {
        this.program = program;
        summarisationMap = program.accept(new ProcedureVisitor(Collections.<SimpleCParser.PrepostContext>emptySet()));
        UNROLL_LOOPS = true;
        UNROLLING_DEPTH = unrollingDepth;
    }

    public List<VerificationResult> verify() {
        List<VerificationResult> results = new ArrayList<>();


        for (SimpleCParser.ProcedureDeclContext proc : program.procedures) {
            // The static variables in the Variables class mean that we use the
            // wrong ids/declarations for global variables, so we need to reset these
            // across procedures.
            Variables.refresh();

            SimpleCSMTVisitor visitor = UNROLL_LOOPS ? new SimpleCSMTVisitor(summarisationMap, UNROLLING_DEPTH) : new SimpleCSMTVisitor(summarisationMap);
            visitor.getEliminatedPrePosts().addAll(eliminatedPrePosts);
            VCGenerator vcGenerator = new VCGenerator(visitor, proc, program.globals, summarisationMap);

            Z3Result z3Result = new Z3().getResult(vcGenerator.generateVC().toString());
            switch (z3Result) {
                case INCORRECT:
                    if (failedDueToCandidatePrePost(visitor, z3Result)) {
                        summarisationMap = program.accept(new ProcedureVisitor(eliminatedPrePosts));
                        return verify();
                    }
            }

            VerificationResult verificationResult = new VerificationResult();
            verificationResult.setZ3Result(z3Result);
            verificationResult.setUnwindingAssertionIds(vcGenerator.getUnwindingAssertionIds());
            results.add(verificationResult);
        }

        return results;
    }

    private boolean failedDueToCandidatePrePost(SimpleCSMTVisitor visitor, Z3Result result) {
        boolean eliminatedPrePost = false;
        for (Integer assertionId : result.getFailingAssertions()) {
            if (visitor.getAssertionToCandidatePrePostMap().containsKey(assertionId)) {
                eliminatedPrePosts.add(visitor.getAssertionToCandidatePrePostMap().get(assertionId));
                System.err.println("Eliminated pre/post-condition at assertion " + assertionId);
                eliminatedPrePost = true;
            }
        }
        return eliminatedPrePost;
    }

}
