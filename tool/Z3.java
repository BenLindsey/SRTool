package tool;

import parser.SimpleCParser;
import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Created by bl2312 on 28/11/15.
 */
public class Z3 {
    private static final int TIMEOUT = 30;
    private static final int MIN_LOOP_UNROLLING_DEPTH = 1;
    private static final int MAX_LOOP_UNROLLING_DEPTH = 1024;

    private boolean verbose = SRTool.verbose;

    private ProcessExec z3;

    public Z3() {
        final List<String> z3Locations = new ArrayList<>();
        z3Locations.add("z3");
        z3Locations.add("./z3");
        z3Locations.add("../../z3");
        z3Locations.add("../../../z3");
        z3Locations.add("../../../../z3");

        this.z3 = findZ3Location(z3Locations);
    }

    private ProcessExec findZ3Location(List<String> z3Locations) {
        for (String z3Location : z3Locations) {
            ProcessExec processExec = new ProcessExec(z3Location, "-smt2", "-in");
            try {
                processExec.execute("", 5);
                return processExec;
            } catch (ProcessTimeoutException | InterruptedException | IOException ignored) {
            }
        }

        return null;
    }

    public Z3Result getResult(String vc) {
        if (verbose) {
            System.out.println("Running:\n" + vc);
        }

        String queryResult;

        try {
            queryResult = z3.execute(vc, TIMEOUT);
        } catch (ProcessTimeoutException | IOException | InterruptedException e) {
            if (verbose) e.printStackTrace();
            return Z3Result.UNKNOWN;
        }

        if (verbose) {
            System.out.println("Result:\n" + queryResult);
        }

        if (queryResult.startsWith("sat")) {

            List<Integer> failingAssertionIds = new ArrayList<>();
            for (String line : queryResult.split("\n")) {
                if (line.contains("--assertion") && line.contains("false")) {
                    String number = "";
                    for (char c : line.toCharArray()) {
                        if (Character.isDigit(c)) {
                            number += c;
                        }
                    }
                    failingAssertionIds.add(Integer.parseInt(number));
                }
            }

            return Z3Result.incorrectWithFailingAssertions(failingAssertionIds);
        }

        if (!queryResult.startsWith("unsat")) {
            System.err.println(queryResult);
            return Z3Result.UNKNOWN;
        }

        return Z3Result.CORRECT;
    }

    void handleResult(Z3Result result) {
        switch (result) {
            case UNKNOWN:
                System.out.println("UNKNOWN");
                System.exit(1);

            case INCORRECT:
                System.out.println("INCORRECT");
                System.exit(0);
        }
    }

    void validate(SimpleCParser.ProgramContext ctx, boolean useLoopUnrolling) throws IOException, InterruptedException {

//		assert ctx.procedures.size() == 1; // For Part 1 of the coursework, this can be assumed

        if (useLoopUnrolling) {
            int unwindingDepth = MIN_LOOP_UNROLLING_DEPTH;
            while (true) {

                HoudiniProcedureRunner procedureRunner = new HoudiniProcedureRunner(ctx, unwindingDepth);

                boolean allCorrect = true;

                for (VerificationResult verificationResult : procedureRunner.verify()) {

                    Z3Result z3Result = verificationResult.getZ3Result();

                    if (z3Result == Z3Result.CORRECT) continue;
                    allCorrect = false;

                    boolean failedUnwindingAssertion = false;
                    for( int i : verificationResult.getUnwindingAssertionIds()) {
                        if(z3Result.getFailingAssertions().contains(i)) {
                            failedUnwindingAssertion = true;
                            break;
                        }
                    }

                    if( failedUnwindingAssertion ) {
                        // Exponentially increase depth
                        unwindingDepth *= 2;
                        if (unwindingDepth > MAX_LOOP_UNROLLING_DEPTH) handleResult(Z3Result.UNKNOWN);
                        break;
                    } else {
                        handleResult(z3Result);
                    }
                }

                if( allCorrect ) break;
            }
        } else {
            HoudiniProcedureRunner procedureRunner = new HoudiniProcedureRunner(ctx);
            for (VerificationResult verificationResult : procedureRunner.verify()) {
                handleResult(verificationResult.getZ3Result());
            }
        }

        System.out.println("CORRECT");
        System.exit(0);
    }
}
