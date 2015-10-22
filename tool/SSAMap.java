package tool;

import java.util.HashMap;
import java.util.Map;

public class SSAMap  {
    private Map<String, Integer> idMap = new HashMap<>();

    public SSAMap () {}

    public String fresh(String variable) {
        Integer id = idMap.get(variable);

        id = id == null ? 0 : id + 1;

        idMap.put(variable, id);

        return variable + id;
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
