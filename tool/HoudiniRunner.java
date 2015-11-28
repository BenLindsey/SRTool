package tool;

import tool.SMTs.SMT;

/**
 * Created by bl2312 on 28/11/15.
 */
public class HoudiniRunner {
    private final String programHead;
    private final String programTail;

    public HoudiniRunner(String programHead) {
        this.programHead = programHead;
        this.programTail = "\n(check-sat)\n(get-model)\n";
    }

    public String eliminateCandidates(SMT funcSMT) {
        Z3Result result = staticallyVerify(funcSMT);

        switch (result) {
            case INCORRECT_DUE_TO_CANDIDATE:
                return eliminateCandidates(funcSMT.withoutCandidate(result.getFailingCandidate()));

            default:
                return funcSMT.toString();
        }
    }

    private String buildProgram(SMT funcSMT) {
        return programHead + funcSMT + programTail;
    }

    private Z3Result staticallyVerify(SMT funcSMT) {
        return new Z3().getResult(buildProgram(funcSMT));
    }
}
