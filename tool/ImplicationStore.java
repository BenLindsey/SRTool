package tool;

import tool.SMTs.SMTFactory;
import tool.SMTs.SMT;

import java.util.ArrayDeque;
import java.util.Deque;

public class ImplicationStore {
    private Deque<ConditionStack> implicationsStack = new ArrayDeque<>();
    private Deque<SMT> predicate = new ArrayDeque<>();

    public ImplicationStore() {
        implicationsStack.push(new ConditionStack());
    }

    public void enterScope(SMT predicate) {
        this.predicate.push(predicate);
        implicationsStack.push(new ConditionStack());
    }

    public void exitScope() {
        if (!predicate.isEmpty()) {
            ConditionStack predicatedConditions = implicationsStack.pop();
            implicationsStack.peek().pushConditions(predicatedConditions, predicate.pop());
        } else {
            implicationsStack.pop();
        }
    }

    public void pushImplication(SMT implication) {
        implication = (!predicate.isEmpty() && implication != predicate.peek()) ? SMTFactory.createImplication(predicate.peek(), implication) : implication;
        implicationsStack.peek().push(implication);
    }

    public SMT getFullImplication() {
        SMT result = SMTFactory.createEmpty();

        for (ConditionStack conditions : implicationsStack) {
            if (result.isEmpty()) {
                result = conditions.getFullCondition();
            } else {
                result = SMTFactory.createAnd(result, conditions.getFullCondition());
            }
        }
        return result;
    }
}
