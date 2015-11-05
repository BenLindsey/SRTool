package tool;

public class SMT {
    private String expression = "";
    private boolean isBoolean = false;

    public SMT() {}

    public SMT(String expression) {
        this.expression = expression;
    }

    public SMT(String expression, boolean isBoolean) {
        this.expression = expression;
        this.isBoolean = isBoolean;
    }

    public boolean isEmpty() {
        return expression.isEmpty();
    }

    public SMT asBoolean() {
        return isBoolean() ? this : new SMT(String.format("(tobool %s)", expression), true);
    }

    public SMT asBitVector() {
        return !isBoolean() ? this : new SMT(String.format("(tobv32 %s)", expression), true);
    }


    public boolean isBoolean() {
        return isBoolean;
    }

    @Override
    public String toString() {
        return expression;
    }

    // Factory Methods

    public static SMT createEmpty() {
        return new SMT();
    }

    public static SMT merge(SMT aggregate, SMT nextResult) {
        return new SMT(aggregate.toString() + nextResult.toString(), aggregate.isBoolean() || nextResult.isBoolean());
    }

    public static SMT createNumber(String text) {
        return new SMT("(_ bv" + text + " 32)");
    }

    public static SMT createVariable(String text) {
        return new SMT(text);
    }

    public static SMT createAnd(SMT left, SMT right) {
        return new SMT("(and " + left.asBoolean() + " " + right.asBoolean() + ")\n", true);
    }

    public static SMT createAssign(String freshVariable, SMT expression) {
        return new SMT("(assert (= " + freshVariable + " " + expression.asBitVector() + "))\n");
    }

    public static SMT createImplication(SMT pred, SMT assertion) {
        return new SMT("(=> " + pred.asBoolean() + " " + assertion.asBoolean() + ")", true);
    }


    public static SMT createAssert(String currentVariable, SMT ite) {
        return new SMT("(assert (= " + currentVariable + " " + ite + "))\n");
    }

    public static SMT createITE(SMT predicate, SMT ifVariable, SMT elseVariable) {
        return new SMT(String.format("(ite %s %s %s)", predicate.asBoolean(), ifVariable, elseVariable),
                ifVariable.isBoolean() || elseVariable.isBoolean());
    }

    public static SMT createDeclaration(String variable) {
        return new SMT("(declare-fun " + variable + " () (_ BitVec 32))\n");
    }

    public static SMT createProcedureDecl(SMT declarations, SMT result) {
        return new SMT("\n" + declarations.toString() + "\n" + result.toString());
    }

    public static SMT createAssertNot(SMT fullCondition) {
        return new SMT("(assert (not " + fullCondition.asBoolean() + "))\n");
    }

    public static SMT createNot(SMT predicate) {
        return new SMT("(not " + predicate.asBoolean() + ")", true);
    }

    public static SMT createPrefix(String operator, SMT left, SMT right, boolean isBoolean) {
        return new SMT(String.format("(%s %s %s)", operator, left, right), isBoolean);
    }

    public static SMT createIsZero(SMT value) {
        return new SMT(String.format("(= %s (_ bv0 32))", value.asBitVector()), true);
    }

    public static SMT createUnary(String operator, SMT value, boolean isBoolean) {
        return new SMT(String.format("(%s %s)", operator, value), isBoolean);
    }

    public static SMT createBool(boolean bool) {
        return new SMT(Boolean.toString(bool), true);
    }
}
