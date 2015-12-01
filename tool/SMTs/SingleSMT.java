package tool.SMTs;

public class SingleSMT implements SMT {
    private String expression = "";
    private boolean isBoolean = false;
    private boolean isCandidate = false;

    SingleSMT() {}

    SingleSMT(String expression) {
        this.expression = expression;
    }

    SingleSMT(String expression, boolean isBoolean) {
        this.expression = expression;
        this.isBoolean = isBoolean;
    }

    SingleSMT(String expression, boolean isBoolean, boolean isCandidate) {
        this.expression = expression;
        this.isBoolean = isBoolean;
        this.isCandidate = isCandidate;
    }


    public boolean isEmpty() {
        return expression.isEmpty();
    }

    @Override
    public boolean isCandidate() {
        return isCandidate;
    }

    @Override
    public SingleSMT asBoolean() {
        return isEmpty() || isBoolean() ? this : new SingleSMT(String.format("(tobool %s)", expression), true);
    }

    @Override
    public SingleSMT asBitVector() {
        return isEmpty() || !isBoolean() ? this : new SingleSMT(String.format("(tobv32 %s)", expression), false);
    }

    @Override
    public int getCandidateId() {
        return 0; //todo
    }

    @Override
    public SMT withoutCandidate(int failingCandidate) {
        return getCandidateId() == failingCandidate ? SMTFactory.createEmpty() : this;
    }


    @Override
    public boolean isBoolean() {
        return isBoolean;
    }

    @Override
    public String toString() {
        return expression;
    }

    @Override
    public void toString(StringBuilder stringBuilder) {
        stringBuilder.append(expression);
    }
}
