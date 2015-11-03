package tool;

import java.util.ArrayDeque;
import java.util.Deque;

public class ImplicationStore {
    private Deque<ConditionStack> implicationsStack = new ArrayDeque<>();

    public ImplicationStore() {
        enterScope();
    }

    public void enterScope() {
        implicationsStack.push(new ConditionStack());
    }

    public void exitScope() {
        implicationsStack.pop();
    }

    public void pushImplication(SMT implication) {
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
