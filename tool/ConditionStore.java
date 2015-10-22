package tool;

import java.util.*;


public class ConditionStore {
    private ConditionStack predicates = new ConditionStack();
    private ConditionStack assumptions = new ConditionStack();

    private String fullCondition = "";
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
                    predicates.getFullCondition(),
                    assumption
            );
        }

        assumptions.push(assumption);
    }

    public String getFullCondition() {
        if( !scratched ) return fullCondition;

        scratched = false;

        fullCondition = predicates.isEmpty() ? assumptions.getFullCondition() :
                        assumptions.isEmpty() ? predicates.getFullCondition() :
                        String.format("(and %s %s)",
                                assumptions.getFullCondition(),
                                predicates.getFullCondition()
                        );

        return fullCondition;
    }
}
