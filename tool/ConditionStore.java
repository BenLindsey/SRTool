package tool;

import tool.SMTs.SMT;
import tool.SMTs.SMTFactory;

import java.util.*;

public class ConditionStore {
    private Deque<SMT> conditions = new ArrayDeque<>();

    private SMT fullCondition = SMTFactory.createEmpty();
    private boolean scratched = false;

    public void push(SMT condition) {
        scratched = true;
        conditions.push(condition);
    }

    public void pop() {
        scratched = true;
        conditions.pop();
    }

    public void pushConditions(ConditionStore conditions, SMT predicate) {
        scratched = true;
        for (SMT condition : conditions.conditions) {
            if (condition != predicate) {
                this.conditions.add(condition);
            }
        }
    }

    public SMT getFullCondition() {
        if( scratched ) {
            scratched = false;
            fullCondition = buildCondition(conditions.iterator());
        }

        if (fullCondition.isEmpty()) {
            return SMTFactory.createBool(true);
        }

        return fullCondition;
    }

    private SMT buildCondition(Iterator<SMT> it) {
        if( !it.hasNext() ) return SMTFactory.createEmpty();

        SMT current = it.next();
        if( !it.hasNext() ) return current;


        return SMTFactory.createAnd(current, buildCondition(it));
    }

    public boolean isEmpty() {
        return conditions.isEmpty();
    }

    public int size() {
        return conditions.size();
    }
}
