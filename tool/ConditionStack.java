package tool;

import java.util.*;

public class ConditionStack {
    private Deque<SMT> conditions = new ArrayDeque<>();

    private SMT fullCondition = SMT.createEmpty();
    private boolean scratched = false;

    public void push(SMT condition) {
        scratched = true;
        conditions.push(condition);
    }

    public SMT pop() {
        scratched = true;
        return conditions.pop();
    }

    public SMT getFullCondition() {
        if( !scratched ) return fullCondition;

        scratched = false;
        fullCondition = buildCondition(conditions.iterator());

        return fullCondition;
    }

    private SMT buildCondition( Iterator<SMT> it) {
        if( !it.hasNext() ) return SMT.createEmpty();

        SMT current = it.next();
        if( !it.hasNext() ) return current;


        return SMT.createAnd(current, buildCondition(it));
    }

    public boolean isEmpty() {
        return conditions.isEmpty();
    }
}
