package tool;

import java.util.*;

public class Variables {
    private static Map<String, Integer> nextIds = new HashMap<>();
    private static SMT declarations = SMT.createEmpty();
    private Deque<List<String>> SMTDeclaredVariables = new ArrayDeque<>();
    private Deque<Set<String>> actualDeclaredVariables = new ArrayDeque<>();
    private Map<String, Deque<Integer>> idMap = new HashMap<>();
    private Deque<Set<String>> modset = new ArrayDeque<>();

    public Variables() {}

    private String fresh(String variable) {

        Integer id = getNextId(variable);

        Deque<Integer> varScope = getScope(variable);
        varScope.push(id);

        idMap.put(variable, varScope);

        return variable + id;
    }

    private int getNextId(String var) {
        Integer id = nextIds.get(var);

        if( id == null ) id = 0;

        nextIds.put(var, id + 1);

        return id;
    }

    public String getCurrentVariable(String variable) {
        Deque<Integer> scope = idMap.get(variable);
        return (scope == null || scope.peek() == null) ? addSMTDeclaration(variable, false) : variable + scope.peek();
    }

    public Variables clone() {
        Variables clone = new Variables();

        for (Map.Entry<String, Deque<Integer>> idEntry : idMap.entrySet()) {
            Deque<Integer> newStack = new ArrayDeque<>();
            newStack.addAll(idEntry.getValue());
            clone.idMap.put(idEntry.getKey(), newStack);
        }

        for (Set<String> var : modset) {
            Set<String> newSet = new HashSet<>(var);
            clone.modset.add(newSet);
        }

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

    private Deque<Integer> getScope(String variable) {
        return idMap.get(variable) == null ? new ArrayDeque<Integer>() : idMap.get(variable);
    }

    public void pushScope() {
        SMTDeclaredVariables.push(new ArrayList<String>());
        actualDeclaredVariables.push(new HashSet<String>());
        modset.push(new HashSet<String>());
    }

    public Variables popScope() {
        Variables variables = clone();
        Iterator declaredVariableIterator = SMTDeclaredVariables.peek().iterator();

        while (declaredVariableIterator.hasNext()) {
            String declaredVariable = (String) declaredVariableIterator.next();
            if (idMap.containsKey(declaredVariable) && !idMap.get(declaredVariable).isEmpty()) {
                idMap.get(declaredVariable).pop();
            }
            declaredVariableIterator.remove();
        }

        List<String> newVars = SMTDeclaredVariables.pop();
        SMTDeclaredVariables.peek().addAll(newVars);

        modset.pop();
        actualDeclaredVariables.pop();
        return variables;
    }

    public static SMT getDeclarations() {
        return declarations;
    }

    public String addSMTDeclaration(String variable, boolean isActualDeclaration) {
        if (SMTDeclaredVariables.isEmpty()) {
            SMTDeclaredVariables.push(new ArrayList<String>());
        }
        SMTDeclaredVariables.peek().add(variable);
        if (isActualDeclaration) {
            if (actualDeclaredVariables.isEmpty()) {
                actualDeclaredVariables.push(new HashSet<String>());
            }
            actualDeclaredVariables.peek().add(variable);
        }

        String freshVariable = fresh(variable);

        declarations = SMT.merge(declarations, SMT.createDeclaration(freshVariable));
        return freshVariable;
    }

    public void addModsetVariable(String variable) {
        getModset().add(variable);
    }

    public Set<String> getModset() {
        if (modset.isEmpty()) {
            modset.push(new HashSet<String>());
        }
        return modset.peek();
    }

    public Set<String> getActualDeclaredVariables() {
        return actualDeclaredVariables.peek();
    }
}
