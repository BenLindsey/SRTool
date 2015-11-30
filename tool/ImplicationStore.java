package tool;

import tool.SMTs.SMTFactory;
import tool.SMTs.SMT;

import java.util.ArrayDeque;
import java.util.Deque;

public class ImplicationStore {

    private ConditionStore assumes = new ConditionStore();
    private ConditionStore predicates = new ConditionStore();

    public ImplicationStore() {
    }

    public void enterScope(SMT predicate) {
        predicates.push(predicate);
    }

    public void exitScope() {
        predicates.pop();
    }

    public void addAssume(SMT assume) {
        assumes.push(SMTFactory.createImplication(predicates.getFullCondition(), assume));
    }

    public SMT getFullImplication() {

        if(assumes.isEmpty()) return predicates.getFullCondition();
        if(predicates.isEmpty()) return assumes.getFullCondition();

        return SMTFactory.createAnd(predicates.getFullCondition(), assumes.getFullCondition());

        /*
        SMT result = SMTFactory.createEmpty();

        for (ConditionStore conditions : predicates) {
            if (result.isEmpty()) {
                result = conditions.getFullCondition();
            } else {
                result = SMTFactory.createAnd(result, conditions.getFullCondition());
            }
        }

        for (ConditionStore conditions : assumes) {
            if (result.isEmpty()) {
                result = conditions.getFullCondition();
            } else {
                result = SMTFactory.createAnd(result, conditions.getFullCondition());
            }
        }

        return result;
        */
    }
}
