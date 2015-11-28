package tool.SMTs;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CompositeSMT implements SMT {
    List<SMT> SMTs = new ArrayList<>();

    public CompositeSMT(SMT... SMTs) {
        this.SMTs = Arrays.asList(SMTs);
    }

    public CompositeSMT(List<SMT> SMTs) {
        this.SMTs = SMTs;
    }

    @Override
    public SMT asBoolean() {
        List<SMT> newSMTList = new ArrayList<>();
        for(SMT smt : SMTs ) {
            newSMTList.add(smt.asBoolean());
        }
        return new CompositeSMT(newSMTList);
    }

    @Override
    public SMT asBitVector() {
        List<SMT> newSMTList = new ArrayList<>();
        for(SMT smt : SMTs ) {
            newSMTList.add(smt.asBitVector());
        }
        return new CompositeSMT(newSMTList);
    }

    @Override
    public int getCandidateId() {
        return -1;
    }

    @Override
    public SMT withoutCandidate(int failingCandidate) {
        List<SMT> toKeep = new ArrayList<>();

        for(SMT smt: toKeep) {
            SMT smtWithoutCandidate = smt.withoutCandidate(failingCandidate);

            if(!smtWithoutCandidate.isEmpty()) {
                toKeep.add(smtWithoutCandidate);
            }
        }

        return new CompositeSMT(toKeep);
    }

    @Override
    public boolean isBoolean() {
        for( SMT smt : SMTs ) {
            if( !smt.isBoolean() ) return false;
        }
        return true;
    }

    @Override
    public boolean isEmpty() {
        for( SMT smt : SMTs ) {
            if( !smt.isEmpty() ) return false;
        }
        return true;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        for( SMT smt : SMTs ) {
            result.append(smt.toString());
        }
        return result.toString();
    }

    @Override
    public boolean isCandidate() {
        for( SMT smt : SMTs ) {
            if( !smt.isCandidate() ) return true;
        }
        return false;
    }
}
