package tool.Fuzz;

/**
 * Created by bl2312 on 28/11/15.
 */
public class SingleCode implements Code {
    private String text;
    private boolean isFunction = false;
    private boolean isMainFunction = false;

    public SingleCode(String text) {
        this.text = text;
    }

    public SingleCode(String text, boolean isFunction, boolean isMainFunction) {
        this.text = text;
        this.isFunction = isFunction;
        this.isMainFunction = isMainFunction;
    }

    @Override
    public String toString() {
        return text;
    }

    @Override
    public Code indent() {
        return isEmpty() ? this : new SingleCode("  " + text);
    }

    @Override
    public boolean hasMainFunction() {
        return isMainFunction;
    }

    @Override
    public Code ensureMainFunction() {
        return isFunction ? CodeFactory.createFunctionHeader("main") : this;
    }

    @Override
    public boolean isEmpty() {
        return text.isEmpty();
    }

    @Override
    public int countFunctions() {
        return isFunction ? 1 : 0;
    }
}
