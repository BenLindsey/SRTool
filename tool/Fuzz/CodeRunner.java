package tool.Fuzz;

import tool.SRTool;
import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.*;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CodeRunner {
    public static final String SOURCE_NAME = "code.c";
    public static final String EXECUTABLE_NAME = "code";

    private Code code;

    public CodeRunner(Code code) {
        if(!code.hasMainFunction() && code.countFunctions() > 1) {
            throw new RuntimeException("Invalid fuzz program");
        }

        this.code = CodeFactory.createExecutable(code);
    }

    public int execute() throws IOException, InterruptedException, ProcessTimeoutException {
        writeSourceFile();

        compileSourceFile();

        return executeOutputFile();
    }

    private void writeSourceFile() throws FileNotFoundException {
        if(SRTool.verbose) {
            System.out.println("Compiling:\n" + code);
        }

        try(PrintWriter out = new PrintWriter(SOURCE_NAME)) {
            out.println(code);
        }
    }

    private void compileSourceFile() throws IOException, InterruptedException {
        Process process = Runtime.getRuntime().exec(String.format("gcc %s -o %s", SOURCE_NAME, EXECUTABLE_NAME));

        process.waitFor();

        int returnCode = process.exitValue();


        if(returnCode > 0) {
            if(SRTool.verbose) {
                printErrorStream(process, returnCode, "compile");
            }

            throw(new IOException("Failed to compile:"));
        }
    }

    private int executeOutputFile() throws IOException, InterruptedException {
        Process process = Runtime.getRuntime().exec(String.format("./%s", EXECUTABLE_NAME));

        process.waitFor();

        int returnCode = process.exitValue();

        if(SRTool.verbose && returnCode > 0) {
            printErrorStream(process, returnCode, "execute");
        }

        return returnCode;
    }

    private void printErrorStream(Process process, int returnCode, String stage) throws IOException {
        BufferedReader reader = new BufferedReader(new InputStreamReader(process.getErrorStream()));
        String line;

        System.out.println(String.format("%s with error %d:", stage, returnCode));
        while((line = reader.readLine()) != null) {
            System.out.println(line);
        }

        System.out.println("");
    }
}
