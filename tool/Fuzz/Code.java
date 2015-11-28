package tool.Fuzz;

/**
 * Created by bl2312 on 28/11/15.
 */
public interface Code {
    Code indent();

    boolean hasMainFunction();

    Code ensureMainFunction();

    boolean isEmpty();
}
