package tool;

import parser.SimpleCParser;

import java.util.List;
import java.util.Set;

public class ProcedureSummarisation {
    private List<SimpleCParser.ExprContext> preconditions;
    private List<SimpleCParser.ExprContext> postconditions;
    private List<SimpleCParser.ExprContext> candidatePreconditions;
    private List<SimpleCParser.ExprContext> candidatePostconditions;
    private Set<String> modset;
    private List<String> parameters;

    public List<SimpleCParser.ExprContext> getPreconditions() {
        return preconditions;
    }

    public void setPreconditions(List<SimpleCParser.ExprContext> preconditions) {
        this.preconditions = preconditions;
    }

    public List<SimpleCParser.ExprContext> getPostconditions() {
        return postconditions;
    }

    public void setPostconditions(List<SimpleCParser.ExprContext> postconditions) {
        this.postconditions = postconditions;
    }

    public List<SimpleCParser.ExprContext> getCandidatePreconditions() {
        return candidatePreconditions;
    }

    public void setCandidatePreconditions(List<SimpleCParser.ExprContext> candidatePreconditions) {
        this.candidatePreconditions = candidatePreconditions;
    }

    public List<SimpleCParser.ExprContext> getCandidatePostconditions() {
        return candidatePostconditions;
    }

    public void setCandidatePostconditions(List<SimpleCParser.ExprContext> candidatePostconditions) {
        this.candidatePostconditions = candidatePostconditions;
    }

    public Set<String> getModset() {
        return modset;
    }

    public void setModset(Set<String> modset) {
        this.modset = modset;
    }

    public List<String> getParameters() {
        return parameters;
    }

    public void setParameters(List<String> parameters) {
        this.parameters = parameters;
    }
}
