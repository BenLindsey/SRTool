package tool.SMTs;

import java.util.Arrays;
import java.util.List;

/**
 * Created by bl2312 on 28/11/15.
 */
public class SMTFactory {


    public static SMT createEmpty() {
        return new SingleSMT();
    }

    public static SMT merge(SMT aggregate, SMT nextResult) {
        return new CompositeSMT(aggregate, nextResult);
        //todo return new SingleSMT(aggregate.toString() + nextResult.toString(), aggregate.isBoolean() || nextResult.isBoolean());
    }

    public static SMT createNumber(String text) {
        return new SingleSMT("(_ bv" + text + " 32)");
    }

    public static SMT createVariable(String text) {
        return new SingleSMT(text);
    }

    public static SMT createBooleanVariable(String text) {
        return new SingleSMT(text, true);
    }

    public static SMT createAnd(List<SMT> expressions) {
        assert (expressions.size() >= 2);

        StringBuilder result = new StringBuilder();
        result.append("(and");

        for( SMT smt : expressions ) {
            result.append(" ").append(smt.asBoolean());
        }

        result.append(")");
        return new SingleSMT(result.toString(), true);
    }

    public static SMT createAnd(SMT... expressions) {
        return createAnd(Arrays.asList(expressions));
    }

    public static SMT createBitVectorAssign(String freshVariable, SMT expression) {
        return new SingleSMT("(assert (= " + freshVariable + " " + expression.asBitVector() + "))\n");
    }

    public static SMT createBoolAssign(String variable, SMT expression) {
        return new SingleSMT("(assert (= " + variable + " " + expression.asBoolean() + "))\n");
    }

    public static SMT createImplication(SMT pred, SMT assertion) {
        return new SingleSMT("(=> " + pred.asBoolean() + " " + assertion.asBoolean() + ")", true);
    }


    public static SMT createAssert(String currentVariable, SMT ite) {
        return new SingleSMT("(assert (= " + currentVariable + " " + ite + "))\n");
    }

    public static SMT createITE(SMT predicate, SMT ifVariable, SMT elseVariable) {
        return new SingleSMT(String.format("(ite %s %s %s)", predicate.asBoolean(), ifVariable, elseVariable),
                ifVariable.isBoolean() || elseVariable.isBoolean());
    }

    public static SMT createBitVectorDeclaration(String variable) {
        return new SingleSMT("(declare-fun " + variable + " () (_ BitVec 32))\n");
    }

    public static SMT createBooleanDeclaration(String variable) {
        return new SingleSMT("(declare-fun " + variable + " () Bool)\n");
    }

    public static SMT createProcedureDecl(SMT declarations, SMT result) {
        return new SingleSMT("\n" + declarations.toString() + "\n" + result.toString());
    }

    public static SMT createAssertNot(SMT fullCondition) {
        return new SingleSMT("(assert (not " + fullCondition.asBoolean() + "))\n");
    }

    public static SMT createNot(SMT predicate) {
        return new SingleSMT("(not " + predicate.asBoolean() + ")", true);
    }

    public static SMT createPrefix(String operator, SMT left, SMT right, boolean isBoolean) {
        return new SingleSMT(String.format("(%s %s %s)", operator, left, right), isBoolean);
    }

    public static SMT createIsZero(SMT value) {
        return new SingleSMT(String.format("(= %s (_ bv0 32))", value.asBitVector()), true);
    }

    public static SMT createUnary(String operator, SMT value, boolean isBoolean) {
        return new SingleSMT(String.format("(%s %s)", operator, value), isBoolean);
    }

    public static SMT createBool(boolean bool) {
        return new SingleSMT(Boolean.toString(bool), true);
    }

    public static SMT createIsOverOrEqual(SMT smt, int i) {
        return new SingleSMT(String.format("(bvsge %s %s)", smt.asBitVector(), createNumber(Integer.toString(i))), true);
    }



//    public static SMTs createCandidateInvariant(SMTs condition) {
//        return new SingleSMT(condition, true);
//    }

}
