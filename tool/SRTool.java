package tool;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.apache.commons.cli.*;
import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.FileInputStream;
import java.io.IOException;

public class SRTool {

    private static final int TIMEOUT = 30;

	public static void main(String[] args) throws IOException, InterruptedException {
		CommandLineParser parser = new DefaultParser();

		Options options = getCommandLineOptions();

		try {
			CommandLine commandLine = parser.parse(options, args);

			if(commandLine.hasOption("h")) {
				printHelp();
			} else {
				validateFile(commandLine.getOptionValue("f"), commandLine.hasOption("v"));
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

		return options;
	}

	private static void printHelp() {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp("SRTool", getCommandLineOptions());
	}

	private static void validateFile(String filename, Boolean verbose) throws IOException, InterruptedException {
		ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
		SimpleCLexer lexer = new SimpleCLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SimpleCParser parser = new SimpleCParser(tokens);
		ProgramContext ctx = parser.program();
		if(parser.getNumberOfSyntaxErrors() > 0) {
			System.exit(1);
		}
		Typechecker tc = new Typechecker();
		tc.visit(ctx);
		tc.resolve();
		if(tc.hasErrors()) {
			System.err.println("Errors were detected when typechecking " + filename + ":");
			for(String err : tc.getErrors()) {
				System.err.println("  " + err);
			}
			System.exit(1);
		}

		assert ctx.procedures.size() == 1; // For Part 1 of the coursework, this can be assumed

		for(ProcedureDeclContext proc : ctx.procedures) {
			VCGenerator vcgen = new VCGenerator(proc, ctx.globals);
			String vc = vcgen.generateVC().toString();

			if(verbose) {
				System.out.println("Running:\n" + vc);
			}

			ProcessExec process = new ProcessExec("./z3", "-smt2", "-in");

			String queryResult = "";
			try {
				queryResult = process.execute(vc, TIMEOUT);
			} catch (ProcessTimeoutException e) {
				System.out.println("UNKNOWN");
				System.exit(1);
			} catch (IOException e) {
				//todo Probably get rid of this/make it nicer. Tests don't seem to find z3 currently.

				// If working directory is a test, search up to find z3
				process = new ProcessExec("../../z3", "-smt2", "-in");

				try {
					queryResult = process.execute(vc, TIMEOUT);
				} catch (ProcessTimeoutException p) {
					System.out.println("UNKNOWN");
					System.exit(1);
				} catch (IOException e2) {

					// todo: for new tests
					process = new ProcessExec("../../../z3", "-smt2", "-in");

					try {
						queryResult = process.execute(vc, TIMEOUT);
					} catch (ProcessTimeoutException p) {
						System.out.println("UNKNOWN");
						System.exit(1);
					} catch (IOException e3) {

						// todo: for online tests
						process = new ProcessExec("z3", "-smt2", "-in");
						try {
							queryResult = process.execute(vc, TIMEOUT);
						} catch (ProcessTimeoutException p) {
							System.out.println("UNKNOWN");
							System.exit(1);
						}
					}
				}
			}

			if(verbose) {
				System.out.println("Result:\n" + queryResult);
			}

			if (queryResult.startsWith("sat")) {
				System.out.println("INCORRECT");
				System.exit(0);
			}

			if (!queryResult.startsWith("unsat")) {
				System.out.println("UNKNOWN");
				System.out.println(queryResult);
				System.exit(1);
			}
		}

		System.out.println("CORRECT");
		System.exit(0);
	}
}
