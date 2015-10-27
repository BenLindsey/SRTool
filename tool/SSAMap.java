package tool;

import java.util.*;

public class SSAMap  {
    private static Map<String, Integer> nextIds = new HashMap<>();
    private static SMT declarations = SMT.createEmpty();
    private static List<String> SMTDeclaredVariables = new ArrayList<>();
    private static Set<String> actualDeclaredVariables = new HashSet<>();
    private Map<String, Deque<Integer>> idMap = new HashMap<>();
    private Deque<Set<String>> modset = new ArrayDeque<>();

    public SSAMap () {}

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

    public SSAMap clone() {
        SSAMap clone = new SSAMap();

        for (Map.Entry<String, Deque<Integer>> idEntry : idMap.entrySet()) {
            Deque<Integer> newStack = new ArrayDeque<>();
            newStack.addAll(idEntry.getValue());
            clone.idMap.put(idEntry.getKey(), newStack);
        }

        for (Set<String> var : modset) {
            Set<String> newSet = new HashSet<>(var);
            clone.modset.add(newSet);
        }

        return clone;
    }

    private Deque<Integer> getScope(String variable) {
        return idMap.get(variable) == null ? new ArrayDeque<Integer>() : idMap.get(variable);
    }

    public void pushScope() {
        SMTDeclaredVariables.clear();
        actualDeclaredVariables.clear();
        modset.push(new HashSet<String>());
    }

    public SSAMap popScope() {
        SSAMap ssaMap = clone();
        for (String declaredVariable : SMTDeclaredVariables) {
            if (idMap.containsKey(declaredVariable) && !idMap.get(declaredVariable).isEmpty()) {
                idMap.get(declaredVariable).pop();
            }
        }
        modset.pop();
        return ssaMap;
    }

    public static SMT getDeclarations() {
        return declarations;
    }

    public String addSMTDeclaration(String variable, boolean isActualDeclaration) {
        SMTDeclaredVariables.add(variable);
        if (isActualDeclaration) actualDeclaredVariables.add(variable);

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

    public static Set<String> getActualDeclaredVariables() {
        return actualDeclaredVariables;
    }
}
