package tool.SMTs;

/**
 * Created by bl2312 on 28/11/15.
 */
public interface SMT {
    boolean isBoolean();
    boolean isEmpty();
    boolean isCandidate();

    SMT asBoolean();
    SMT asBitVector();

    int getCandidateId();
    SMT withoutCandidate(int failingCandidate);
}
