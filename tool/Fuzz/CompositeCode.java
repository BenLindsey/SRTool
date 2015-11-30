package tool.Fuzz;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CompositeCode implements Code {
    List<Code> codes;

    public CompositeCode(Code... codes) {
        this.codes = Arrays.asList(codes);
    }

    public CompositeCode(List<Code> codes) {
        this.codes = codes;
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();

        for(Code code : codes) {
            builder.append(code);
        }

        return builder.toString();
    }

    @Override
    public Code indent() {
        List<Code> codes = new ArrayList<>();

        for(Code code : this.codes) {
            codes.add(code.indent());
        }

        return new CompositeCode(codes);
    }

    @Override
    public boolean hasMainFunction() {
        for(Code code : codes) {
            if(code.hasMainFunction()) {
                return true;
            }
        }

        return false;
    }

    @Override
    public Code ensureMainFunction() {
        boolean hasMainFunction = hasMainFunction();

        List<Code> codes = new ArrayList<>();

        for(Code code : this.codes) {
            if(!hasMainFunction) {
                code = code.ensureMainFunction();
                hasMainFunction = code.hasMainFunction();
            }

            codes.add(code);
        }

        return new CompositeCode(codes);
    }

    @Override
    public boolean isEmpty() {
        for(Code code : codes) {
            if(!code.isEmpty()) {
                return false;
            }
        }

        return true;
    }

    @Override
    public int countFunctions() {
        int acc = 0;

        for(Code code : codes) {
            acc += code.countFunctions();
        }

        return acc;
    }

}
