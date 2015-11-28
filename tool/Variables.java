package tool;

import tool.SMTs.SMT;
import tool.SMTs.SMTFactory;

import java.util.*;

public class Variables {
    private static Map<String, Integer> nextIds = new HashMap<>();
    private static SMT declarations = SMTFactory.createEmpty();
    private Map<String, Deque<Integer>> idMap = new HashMap<>();
    private Scope scope = new Scope();

    public Variables() {}

    private String fresh(String variable) {

        Integer id = getNextId(variable);

        Deque<Integer> varScope = getScope(variable);
        varScope.push(id);

        idMap.put(variable, varScope);

        return variable + "-" + id;

    }

    private int getNextId(String var) {
        Integer id = nextIds.get(var);

        if( id == null ) id = 0;

        nextIds.put(var, id + 1);

        return id;
    }

    public String getCurrentVariable(String variable) {
        Deque<Integer> scope = idMap.get(variable);
        return (scope == null || scope.peek() == null) ? addSMTDeclaration(variable, false) : variable + "-" + scope.peek();
    }

    public Variables clone() {
        Variables clone = new Variables();

        for (Map.Entry<String, Deque<Integer>> idEntry : idMap.entrySet()) {
            Deque<Integer> newStack = new ArrayDeque<>();
            newStack.addAll(idEntry.getValue());
            clone.idMap.put(idEntry.getKey(), newStack);
        }

        clone.scope = scope.clone();

        return clone;
    }

    private Deque<Integer> getScope(String variable) {
        return idMap.get(variable) == null ? new ArrayDeque<Integer>() : idMap.get(variable);
    }

    public void enterScope() {
        scope.push();
    }

    public Variables exitScope() {
        Variables variables = clone();
        Iterator declaredVariableIterator = scope.getSMTDeclaredVariables().iterator();

        while (declaredVariableIterator.hasNext()) {
            String declaredVariable = (String) declaredVariableIterator.next();
            if (idMap.get(declaredVariable) != null && !idMap.get(declaredVariable).isEmpty()) {
                idMap.get(declaredVariable).pop();
            }
            declaredVariableIterator.remove();
        }

        scope.pop();

        return variables;
    }

    public static SMT getDeclarations() {
        return declarations;
    }

    public String addSMTDeclaration(String variable, boolean isActualDeclaration) {
        scope.getSMTDeclaredVariables().add(variable);

        if (isActualDeclaration) {
            scope.getActualDeclaredVariables().add(variable);
        }

        String freshVariable = fresh(variable);

        declarations = SMTFactory.merge(declarations, SMTFactory.createDeclaration(freshVariable));
        return freshVariable;
    }

    public Set<String> getActualDeclaredVariables() {
        return scope.getActualDeclaredVariables();
    }

    public static void refresh() {
        nextIds = new HashMap<>();
        declarations = SMTFactory.createEmpty();
    }
}
