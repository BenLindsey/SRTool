package tool;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.apache.commons.cli.*;
import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import tool.Fuzz.Code;
import tool.Fuzz.CodeRunner;
import tool.Fuzz.CodeVisitor;
import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.rmi.server.ExportException;
import java.util.*;

public class SRTool {
	public static boolean verbose = false;
	public static boolean guessCandidates;

	public static void main(String[] args) throws IOException, InterruptedException {
		CommandLineParser parser = new DefaultParser();

		Options options = getCommandLineOptions();

		try {
			CommandLine commandLine = parser.parse(options, args);

			if(commandLine.hasOption("h")) {
				printHelp();
			} else {
				verbose = commandLine.hasOption("v");
				try {
					guessCandidates = commandLine.hasOption("g");
					boolean fuzz = commandLine.hasOption("z");
					String fileName = commandLine.getOptionValue("f");
					ProgramContext ctx = Antlr.getProgramContextFromFile(fileName);

					if(!fuzz) {
						new Z3().validate(ctx, commandLine.hasOption("lu"));
					} else {
						List<List<Integer>> fuzzes = Arrays.asList(
								Collections.singletonList(0),
								Collections.singletonList(10000),
								Collections.singletonList(64000),
								Arrays.asList(200, 60),
								Arrays.asList(1000, 60),
								Arrays.asList(5, 1000)
						);

						for(List<Integer> fuzzVariables : fuzzes) {
							Code code = new CodeVisitor(fuzzVariables).visitProgram(ctx);
							CodeRunner runner = new CodeRunner(code);

							if(runner.execute() > 0) {
								System.out.println("INCORRECT");
								System.exit(0);
							}
						}

					}
				} catch (Exception e) {
					if (verbose) e.printStackTrace();
					System.out.println("UNKNOWN");
					System.exit(1);
				}
			}
		}
		catch(ParseException exp) {
			System.err.println( "Failed to parse command line arguments: " + exp.getMessage());

			printHelp();
		}
    }

	private static Options getCommandLineOptions() {
		Options options = new Options();

		options.addOption(Option.builder("v")
						.desc("enable verbose logging, by default only CORRECT/INCORRECT is printed.")
						.build()
		);

		options.addOption(Option.builder("f")
						.hasArg()
						.argName("path to file")
						.required()
						.desc("file to validate")
						.build()
		);

		options.addOption(Option.builder("h")
						.longOpt("help")
						.desc("display usage")
						.build()
		);

		options.addOption(Option.builder("lu")
						.longOpt("loop-unwinding")
						.desc("enable loop unwinding")
						.build()
		);

		options.addOption(Option.builder("g")
						.longOpt("generation")
						.desc("enable candidate generation")
						.build()
		);

		options.addOption(Option.builder("z")
				.longOpt("fuzz")
				.desc("enable fuzzing")
				.build()
		);

		return options;
	}

	private static void printHelp() {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp("SRTool", getCommandLineOptions());
	}
}
