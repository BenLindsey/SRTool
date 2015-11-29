package tool;

import java.util.List;

public class VerificationResult {
    private Z3Result z3Result;
    private List<Integer> unwindingAssertionIds;

    public Z3Result getZ3Result() {
        return z3Result;
    }

    public void setZ3Result(Z3Result z3Result) {
        this.z3Result = z3Result;
    }

    public List<Integer> getUnwindingAssertionIds() {
        return unwindingAssertionIds;
    }

    public void setUnwindingAssertionIds(List<Integer> unwindingAssertionIds) {
        this.unwindingAssertionIds = unwindingAssertionIds;
    }
}
