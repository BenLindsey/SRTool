package tool;

import java.util.*;

public class ConditionStack {
    private Deque<String> conditions = new ArrayDeque<>();

    private String fullCondition = "";
    private boolean scratched = false;

    public void push(String condition) {
        scratched = true;
        conditions.push(condition);
    }

    public String pop() {
        scratched = true;
        return conditions.pop();
    }

    public String getFullCondition() {
        if( !scratched ) return fullCondition;

        scratched = false;
        fullCondition = buildCondition(conditions.iterator());

        return fullCondition;
    }

    private String buildCondition( Iterator<String> it) {
        if( !it.hasNext() ) return "";

        String current = it.next();
        if( !it.hasNext() ) return current;

        return "(and " + current + " " + buildCondition(it) + ")";
    }

    public boolean isEmpty() {
        return conditions.isEmpty();
    }
}
