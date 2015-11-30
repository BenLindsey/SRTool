package tool.Fuzz;

import tool.SRTool;
import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.*;
import java.util.UUID;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CodeRunner {
    private static final String OUTPUT_DIR = "/tmp";
    public String SOURCE_NAME = UUID.randomUUID().toString() + ".c";
    public String EXECUTABLE_NAME = UUID.randomUUID().toString();

    private Code code;

    public CodeRunner(Code code) {
        if(code.countFunctions() > 1) {
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

        try(PrintWriter out = new PrintWriter(OUTPUT_DIR + "/" + SOURCE_NAME)) {
            out.println(code);
        }
    }

    private void compileSourceFile() throws IOException, InterruptedException {
        Process process = Runtime.getRuntime().exec(String.format("gcc %s/%s -o %s/%s", OUTPUT_DIR, SOURCE_NAME, OUTPUT_DIR, EXECUTABLE_NAME));

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
        Process process = Runtime.getRuntime().exec(String.format("%s/%s", OUTPUT_DIR, EXECUTABLE_NAME));

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
