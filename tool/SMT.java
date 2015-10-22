package tool;

public class SMT {
    private String expression = "";

    public SMT() {}

    public SMT(String expression) {
        this.expression = expression;
    }

    public boolean isEmpty() {
        return expression.isEmpty();
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
        return new SMT(aggregate.toString() + nextResult.toString());
    }

    public static SMT createNumber(String text) {
        return new SMT("(_ bv" + text + " 32)");
    }

    public static SMT createVariable(String text) {
        return new SMT(text);
    }

    public static SMT createRequires(SMT condition) {
        return new SMT("(assert " + condition + ")\n");
    }

    public static SMT createAnd(SMT left, SMT right) {
        return new SMT("(and " + left + " " + right + ")\n");
    }

    public static SMT createAssign(String freshVariable, SMT expression) {
        return new SMT("(assert (= " + freshVariable + " " + expression + "))\n");
    }

    public static SMT createImplication(SMT pred, SMT assertion) {
        return new SMT("(=> " + pred + " " + assertion + ")");
    }


    public static SMT createAssert(String currentVariable, SMT ite) {
        return new SMT("(assert (= " + currentVariable + " " + ite + "))\n");
    }

    public static SMT createITE(SMT predicate, SMT ifVariable, SMT elseVariable) {
        return new SMT(String.format("(ite %s %s %s)", predicate, ifVariable, elseVariable));
    }

    public static SMT createDeclaration(String variable) {
        return new SMT("(declare-fun " + variable + " () (_ BitVec 32))\n");
    }

    public static SMT createProcedureDecl(SMT declarations, SMT result) {
        return new SMT("\n" + declarations.toString() + "\n" + result.toString());
    }

    public static SMT createAssertNot(SMT fullCondition) {
        return new SMT("(assert (not " + fullCondition + "))\n");
    }

    public static SMT createNot(SMT predicate) {
        return new SMT("(not " + predicate + ")");
    }

    public static SMT createPrefix(String operator, SMT left, SMT right) {
        return new SMT(String.format("(%s %s %s)", operator, left, right));
    }

    public static SMT createIsZero(SMT value) {
        return new SMT(String.format("(= %s (_ bv0 32))", value));
    }

    public static SMT createUnary(String operator, SMT value) {
        return new SMT(String.format("(%s %s)", operator, value));
    }
}
