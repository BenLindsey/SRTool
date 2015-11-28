package tool.SMTs;

/**
 * Created by bl2312 on 28/11/15.
 */
public interface SMT {
    SMT asBoolean();
    SMT asBitVector();

    boolean isBoolean();

    boolean isEmpty();
}
