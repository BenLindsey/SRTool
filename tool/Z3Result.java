package tool;

/**
 * Created by bl2312 on 28/11/15.
 */
public enum Z3Result {
    CORRECT, INCORRECT, INCORRECT_DUE_TO_CANDIDATE, UNKNOWN;

    private int failingCandidate;

    Z3Result() {
        failingCandidate = -1;
    }

    Z3Result(int failingCandidate) {
        this.failingCandidate = failingCandidate;
    }

    public int getFailingCandidate() {
      return failingCandidate;
    }
}
