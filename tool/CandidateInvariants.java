package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import parser.SimpleCParser;

import java.io.IOException;
import java.util.*;

public class CandidateInvariants {

    private Set<SimpleCParser.CandidateInvariantContext> eliminatedCandidateInvariants;
    private static Map<SimpleCParser.WhileStmtContext, List<SimpleCParser.LoopInvariantContext>> currentInvariantsForLoop = new HashMap<>();

    public CandidateInvariants(Set<SimpleCParser.CandidateInvariantContext> eliminatedCandidateInvariants) {
        this.eliminatedCandidateInvariants = eliminatedCandidateInvariants;
    }

    public void addInferredInvariants(SimpleCParser.WhileStmtContext whileStmtContext) {
        List<SimpleCParser.LoopInvariantContext> currentInvariants = currentInvariantsForLoop.get(whileStmtContext);

        if (currentInvariants == null) {
            currentInvariants = generateInvariants(whileStmtContext);
            currentInvariantsForLoop.put(whileStmtContext, currentInvariants);
        }

        Set<SimpleCParser.LoopInvariantContext> invariants = new HashSet<>();
        invariants.addAll(currentInvariants);

        Iterator<SimpleCParser.LoopInvariantContext> invariantIterator = currentInvariants.iterator();
        while (invariantIterator.hasNext()) {
            if (eliminatedCandidateInvariants.contains(invariantIterator.next().candidateInvariant())) {
                invariantIterator.remove();
            }
        }

        whileStmtContext.invariantAnnotations.addAll(invariants);
    }

    private List<SimpleCParser.LoopInvariantContext> generateInvariants(SimpleCParser.WhileStmtContext whileStmtContext) {
        Set<String> modset = whileStmtContext.body.accept(new ModSetVisitor());
        Set<String> conditionVariables = whileStmtContext.condition.accept(new VariableVisitor());
        Set<String> numbers = findProcedureContext(whileStmtContext).accept(new NumberVisitor());

        List<String> candidateInvariants = new ArrayList<>();

        for (String var : modset) {
            candidateInvariants.addAll(createInequalityCandidates(var, "0"));

            for (String number : numbers) {
                candidateInvariants.addAll(createInequalityCandidates(var, number));
            }

            for (String conditionVar : conditionVariables) {
                candidateInvariants.addAll(createInequalityCandidates(var, conditionVar));
            }

            for (String var2 : modset) {
                for (String number : numbers) {
                    candidateInvariants.addAll(createArithmeticCandidates(var, number, var2));
                }
            }
        }

        Set<String> variables = new HashSet<>();
        variables.addAll(modset);
        variables.addAll(conditionVariables);


        SimpleCParser.ProgramContext program = createSimpleProgram(variables, candidateInvariants);
        return parseSimpleProgram(program);
    }

    private List<String> createInequalityCandidates(String var, String rhs) {
        List<String> candidates = new ArrayList<>();
        candidates.add(createBinopCandidate(var, "<", rhs));
        candidates.add(createBinopCandidate(var, "<=", rhs));
        candidates.add(createBinopCandidate(var, ">", rhs));
        candidates.add(createBinopCandidate(var, ">=", rhs));
        return candidates;
    }

    private String createBinopCandidate(String lhs, String op, String rhs) {
        return "candidate_invariant " + lhs + " " + op + " " + rhs;
    }

    private List<String> createArithmeticCandidates(String lhs, String number, String rhs) {
        List<String> candidates = new ArrayList<>();
        candidates.addAll(createArithmeticCandidate(lhs, "+", number, rhs));
        candidates.addAll(createArithmeticCandidate(lhs, "-", number, rhs));
        candidates.addAll(createArithmeticCandidate(lhs, "*", number, rhs));
        candidates.addAll(createArithmeticCandidate(lhs, "/", number, rhs));
        return candidates;
    }

    private List<String> createArithmeticCandidate(String lhs, String arithmeticOp, String number, String rhs) {
        List<String> candidates = new ArrayList<>();
        candidates.add("candidate_invariant " + lhs + " == " + number + " " + arithmeticOp + " " + rhs);
        candidates.add("candidate_invariant " + lhs + " == " + rhs+ " " + arithmeticOp + " " + number);
        return candidates;
    }

    private SimpleCParser.ProgramContext createSimpleProgram(Set<String> variables, List<String> candidateInvariants) {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("int main() {");

        for (String var : variables) {
            stringBuilder.append("int ").append(var).append(";");
        }

        stringBuilder.append("while (1) ");

        for (int i = 0; i < candidateInvariants.size(); i++) {
            stringBuilder.append(candidateInvariants.get(i));
            if (i != candidateInvariants.size() - 1) {
                stringBuilder.append(",");
            }
        }

        stringBuilder
                .append("{}")
                .append("return 0;")
                .append("}");

        String program = stringBuilder.toString();

        try {
            return Antlr.getProgramContextFromText(program);
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }

    private List<SimpleCParser.LoopInvariantContext> parseSimpleProgram(SimpleCParser.ProgramContext program) {
        int whileStatementIndex = program.procedures.get(0).stmts.size() - 1;
        return program != null ? program.procedures.get(0).stmts.get(whileStatementIndex).whileStmt().invariantAnnotations : Collections.<SimpleCParser.LoopInvariantContext>emptyList();
    }

    private SimpleCParser.ProcedureDeclContext findProcedureContext(SimpleCParser.WhileStmtContext whileStmtContext) {
        ParserRuleContext currentContext = whileStmtContext;

        while (!(currentContext instanceof SimpleCParser.ProcedureDeclContext)) {
            currentContext = currentContext.getParent();
        }

        return (SimpleCParser.ProcedureDeclContext) currentContext;
    }

}
