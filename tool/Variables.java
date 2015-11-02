package tool;

import java.util.*;

public class Variables {
    private static Map<String, Integer> nextIds = new HashMap<>();
    private static SMT declarations = SMT.createEmpty();
    private static Set<String> usedVariables = new HashSet<>();
    private Map<String, Deque<Integer>> idMap = new HashMap<>();
    private Stack stack = new Stack();

    public Variables() {}

    private String fresh(String variable) {

        Integer id = getNextId(variable);

        Deque<Integer> varScope = getScope(variable);
        varScope.push(id);

        idMap.put(variable, varScope);

        String variableName = variable + id;

        if (usedVariables.contains(variableName)) {
            return fresh(variable);
        }

        usedVariables.add(variableName);
        return variableName;

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

        clone.stack = stack.clone();

        return clone;
    }

    private Deque<Integer> getScope(String variable) {
        return idMap.get(variable) == null ? new ArrayDeque<Integer>() : idMap.get(variable);
    }

    public void pushScope() {
        stack.push();
    }

    public Variables popScope() {
        Variables variables = clone();
        Iterator declaredVariableIterator = stack.getSMTDeclaredVariables().iterator();

        while (declaredVariableIterator.hasNext()) {
            String declaredVariable = (String) declaredVariableIterator.next();
            if (idMap.containsKey(declaredVariable) && !idMap.get(declaredVariable).isEmpty()) {
                idMap.get(declaredVariable).pop();
            }
            declaredVariableIterator.remove();
        }

        stack.pop();

        return variables;
    }

    public static SMT getDeclarations() {
        return declarations;
    }

    public String addSMTDeclaration(String variable, boolean isActualDeclaration) {
        stack.getSMTDeclaredVariables().add(variable);

        if (isActualDeclaration) {
            stack.getActualDeclaredVariables().add(variable);
        }

        String freshVariable = fresh(variable);

        declarations = SMT.merge(declarations, SMT.createDeclaration(freshVariable));
        return freshVariable;
    }

    public void addModsetVariable(String variable) {
        getModset().add(variable);
    }

    public Set<String> getModset() {
        return stack.getModset();
    }

    public Set<String> getActualDeclaredVariables() {
        return stack.getActualDeclaredVariables();
    }
}
