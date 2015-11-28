package tool;

import tool.SMTs.SMT;
import tool.SMTs.SMTFactory;

import java.util.*;

public class ConditionStore {
    private List<SMT> conditions = new ArrayList<>();

    private SMT fullCondition = SMTFactory.createEmpty();
    private boolean scratched = false;

    public void push(SMT condition) {
        scratched = true;
        conditions.add(condition);
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

    public SMT get(int i) {
        return conditions.get(i);
    }
}
