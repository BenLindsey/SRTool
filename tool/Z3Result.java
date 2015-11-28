package tool;

/**
 * Created by bl2312 on 28/11/15.
 */
public enum Z3Result {
    CORRECT, INCORRECT, INCORRECT_DUE_TO_CANDIDATE, UNKNOWN;

    private int failingCandidate = -1;

    public int getFailingCandidate() {
      return failingCandidate;
    }

    public static Z3Result INCORRECTWithFailingCandidate(int id) {
        Z3Result result = Z3Result.INCORRECT;
        result.failingCandidate = id;

        return result;
    }
}
