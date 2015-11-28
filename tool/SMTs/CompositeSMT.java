package tool.SMTs;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CompositeSMT implements SMT {
    List<SMT> SMTs = new ArrayList<>();

    public CompositeSMT(SMT... SMTs) {
        this.SMTs = Arrays.asList(SMTs).stream().filter(SMT -> !SMT.isEmpty()).collect(Collectors.toList());
    }

    public CompositeSMT(List<SMT> SMTs) {
        this.SMTs = SMTs;
    }

    @Override
    public SMT asBoolean() {
        return new CompositeSMT(SMTs.stream().map(SMT::asBoolean).collect(Collectors.toList()));
    }

    @Override
    public SMT asBitVector() {
        return new CompositeSMT(SMTs.stream().map(SMT::asBitVector).collect(Collectors.toList()));
    }

    @Override
    public boolean isBoolean() {
        return SMTs.stream().anyMatch(SMT::isBoolean);
    }

    @Override
    public boolean isEmpty() {
        return SMTs.stream().allMatch(SMT::isEmpty);
    }

    @Override
    public String toString() {
        return SMTs.stream().map(Object::toString).reduce("", String::concat);
    }
}
