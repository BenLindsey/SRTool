package tool;

import java.util.*;

public class Scope {
    private Deque<List<String>> SMTDeclaredVariables = new ArrayDeque<>();
    private Deque<Set<String>> actualDeclaredVariables = new ArrayDeque<>();

    public Set<String> getActualDeclaredVariables() {
        if (actualDeclaredVariables.isEmpty()) {
            actualDeclaredVariables.push(new HashSet<String>());
        }
        return actualDeclaredVariables.peek();
    }

    public List<String> getSMTDeclaredVariables() {
        if (SMTDeclaredVariables.isEmpty()) {
            SMTDeclaredVariables.push(new ArrayList<String>());
        }
        return SMTDeclaredVariables.peek();
    }

    public void push() {
        SMTDeclaredVariables.push(new ArrayList<String>());
        actualDeclaredVariables.push(new HashSet<String>());
    }

    public void pop() {
        ensureScopeNotEmpty();

        List<String> newVars = SMTDeclaredVariables.pop();
        getSMTDeclaredVariables().addAll(newVars);

        actualDeclaredVariables.pop();
    }

    public Scope clone() {
        Scope clone = new Scope();

        for (List<String> smtDeclaredVariables : SMTDeclaredVariables) {
            List<String> newList = new ArrayList<>(smtDeclaredVariables);
            clone.SMTDeclaredVariables.add(newList);
        }

        for (Set<String> actualDeclaredVariable : actualDeclaredVariables) {
            Set<String> newSet = new HashSet<>(actualDeclaredVariable);
            clone.actualDeclaredVariables.add(newSet);
        }

        return clone;
    }

    private void ensureScopeNotEmpty() {
        getSMTDeclaredVariables();
        getActualDeclaredVariables();
    }
}
