package tool.SMTs;

public class SingleSMT implements SMT {
    private String expression = "";
    private boolean isBoolean = false;

    SingleSMT() {}

    SingleSMT(String expression) {
        this.expression = expression;
    }

    SingleSMT(String expression, boolean isBoolean) {
        this.expression = expression;
        this.isBoolean = isBoolean;
    }

    public boolean isEmpty() {
        return expression.isEmpty();
    }

    public SingleSMT asBoolean() {
        return isEmpty() || isBoolean() ? this : new SingleSMT(String.format("(tobool %s)", expression), true);
    }

    public SingleSMT asBitVector() {
        return isEmpty() || !isBoolean() ? this : new SingleSMT(String.format("(tobv32 %s)", expression), false);
    }


    public boolean isBoolean() {
        return isBoolean;
    }

    @Override
    public String toString() {
        return expression;
    }

}
