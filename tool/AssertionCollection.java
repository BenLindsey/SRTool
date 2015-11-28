package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import tool.SMTs.SMT;
import tool.SMTs.SMTFactory;

import java.util.ArrayList;
import java.util.List;

public class AssertionCollection {
    private List<SMT> assertions = new ArrayList<>();

    public int push(SMT assertion) {
        assertions.add(assertion);
        return assertions.size() - 1;
    }

    public static String getAssertionName(int i) {
        return "--assertion" + i;
    }

    public SMT addAssertionDeclarations() {
        SMT declarations = SMTFactory.createEmpty();

        for(int i = 0; i < assertions.size(); i++ ) {
            declarations = SMTFactory.merge(declarations, SMTFactory.createBooleanDeclaration(getAssertionName(i)));
        }

        return declarations;
    }

    public SMT getAssignments() {
        SMT result = SMTFactory.createEmpty();

        for (int i = 0; i < assertions.size(); i++) {
            result = SMTFactory.merge(result, SMTFactory.createBoolAssign(getAssertionName(i), assertions.get(i)));
        }

        return result;
    }

    public SMT getAssertions() {

        if (assertions.isEmpty()) {
            return SMTFactory.createBool(true);
        }

        List<SMT> smts = new ArrayList<>();

        for(int i = 0; i < this.assertions.size(); i++ ) {
            String assertionName = getAssertionName(i);

            smts.add(SMTFactory.createBooleanVariable(assertionName));
        }

        return SMTFactory.createAnd(smts);
    }

    public boolean isEmpty() {
        return assertions.isEmpty();
    }

    public int size() {
        return assertions.size();
    }

    public SMT get(int i) {
        return assertions.get(i);
    }
}
