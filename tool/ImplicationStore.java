package tool;

import java.util.ArrayDeque;
import java.util.Deque;

public class ImplicationStore {
    private Deque<ConditionStack> implicationsStack = new ArrayDeque<>();
    private SMT predicate;

    public ImplicationStore() {
        enterScope(null);
    }

    public void enterScope(SMT predicate) {
        this.predicate = predicate;
        implicationsStack.push(new ConditionStack());
    }

    public void exitScope() {
        if (predicate != null) {
            ConditionStack predicatedConditions = implicationsStack.pop();
            implicationsStack.peek().pushConditions(predicatedConditions, predicate);
        } else {
            implicationsStack.pop();
        }
        predicate = null;
    }

    public void pushImplication(SMT implication) {
        implication = (predicate != null && implication != predicate) ? SMT.createImplication(predicate, implication) : implication;
        implicationsStack.peek().push(implication);
    }

    public SMT getFullImplication() {
        SMT result = SMT.createEmpty();

        for (ConditionStack conditions : implicationsStack) {
            if (result.isEmpty()) {
                result = conditions.getFullCondition();
            } else {
                result = SMT.createAnd(result, conditions.getFullCondition());
            }
        }

        return result;
    }
}
