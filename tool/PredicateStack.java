package tool;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Iterator;


public class PredicateStack {
    private Deque<String> stack = new ArrayDeque<>();

    private String fullPredicate = "";
    private boolean scratched = false;

    public void push(String predicate) {
        scratched = true;
        stack.push(predicate);
    }

    public String pop() {
        scratched = true;
        return stack.pop();
    }

    public String getFullPredicate() {
        if( !scratched ) return fullPredicate;

        scratched = false;
        fullPredicate = buildPredicate( stack.iterator() );

        return fullPredicate;
    }

    private String buildPredicate( Iterator<String> it) {
        if( !it.hasNext() ) return "";

        String current = it.next();
        if( !it.hasNext() ) return current;

        return "(and " + current + " " + buildPredicate(it) + ")";
    }
}
