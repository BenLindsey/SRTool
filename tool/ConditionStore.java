package tool;

import java.util.*;


public class ConditionStore {
    private ConditionStack predicates = new ConditionStack();
    private ConditionStack assumptions = new ConditionStack();

    private SMT fullCondition = SMT.createEmpty();
    private boolean scratched = false;

    public void pushPredicate(SMT predicate) {
        scratched = true;
        predicates.push(predicate);
    }

    public SMT popPredicate() {
        scratched = true;
        return predicates.pop();
    }

    public void addAssumption(SMT assumption) {
        scratched = true;

        if(!predicates.isEmpty()) {
            assumption = SMT.createAnd(
                    predicates.getFullCondition(),
                    assumption
            );
        }

        assumptions.push(assumption);
    }

    public SMT getFullCondition() {
        if( !scratched ) return fullCondition;

        scratched = false;

        fullCondition = predicates.isEmpty() ? assumptions.getFullCondition() :
                        assumptions.isEmpty() ? predicates.getFullCondition() :
                        SMT.createAnd(
                                assumptions.getFullCondition(),
                                predicates.getFullCondition()
                        );

        return fullCondition;
    }
}
