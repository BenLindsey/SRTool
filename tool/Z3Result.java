package tool;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by bl2312 on 28/11/15.
 */
public enum Z3Result {
    CORRECT, INCORRECT, UNKNOWN;

    private List<Integer> failingAssertions = new ArrayList<>();

    public List<Integer> getFailingAssertions() {
        return failingAssertions;
    }

    public static Z3Result INCORRECTWithFailingAssertion(List<Integer> ids) {
        Z3Result result = Z3Result.INCORRECT;
        result.failingAssertions = ids;

        return result;
    }
}
