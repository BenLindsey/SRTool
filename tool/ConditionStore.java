package tool;

import java.util.*;


public class ConditionStore {
    private Deque<String> predicates = new ArrayDeque<>();
    private List<String> assumptions = new ArrayList<>();

    private String fullPredicate = "";
    private boolean scratched = false;

    public void pushPredicate(String predicate) {
        scratched = true;
        predicates.push(predicate);
    }

    public String popPredicate() {
        scratched = true;
        return predicates.pop();
    }

    public void addAssumption(String assumption) {
        scratched = true;

        if(!predicates.isEmpty()) {
            assumption = String.format("(and %s %s)",
                    buildCondition(predicates.iterator()),
                    assumption
            );
        }

        assumptions.add(assumption);
    }

    public String getFullPredicate() {
        if( !scratched ) return fullPredicate;

        scratched = false;

        fullPredicate = predicates.isEmpty() ? buildCondition(assumptions.iterator()) :
                        assumptions.isEmpty() ? buildCondition(predicates.iterator()) :
                        String.format("(and %s %s)",
                                buildCondition(predicates.iterator()),
                                buildCondition(assumptions.iterator())
                        );

        return fullPredicate;
    }

    private String buildCondition( Iterator<String> it) {
        if( !it.hasNext() ) return "";

        String current = it.next();
        if( !it.hasNext() ) return current;

        return "(and " + current + " " + buildCondition(it) + ")";
    }
}
