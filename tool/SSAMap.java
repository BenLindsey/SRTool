package tool;

import java.util.HashMap;
import java.util.Map;

public class SSAMap  {
    private static Map<String, Integer> nextIds = new HashMap<>();

    private Map<String, Integer> idMap = new HashMap<>();

    public SSAMap () {}

    public String fresh(String variable) {

        Integer id = getNextId(variable);

        idMap.put(variable, id);

        return variable + id;
    }

    private int getNextId(String var) {
        Integer id = nextIds.get(var);

        if( id == null ) id = 0;

        nextIds.put(var, id + 1);

        return id;
    }

    public String getCurrentVariable(String variable) {
        Integer id = idMap.get(variable);
        return id == null ? fresh(variable) : variable + id;
    }

    public SSAMap clone() {
        SSAMap clone = new SSAMap();
        clone.idMap.putAll( this.idMap );
        return clone;
    }
}
