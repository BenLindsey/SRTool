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

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.rmi.server.ExportException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class SRTool {

    private static final int TIMEOUT = 30;
	private static boolean verbose = false;

	private static final int LOOP_UNROLLING_DEPTH = 1000000;

	public static void main(String[] args) throws IOException, InterruptedException {
		CommandLineParser parser = new DefaultParser();

		Options options = getCommandLineOptions();

		try {
			CommandLine commandLine = parser.parse(options, args);

			if(commandLine.hasOption("h")) {
				printHelp();
			} else {
				verbose = commandLine.hasOption("v");
				validateFile(commandLine.getOptionValue("f"), commandLine.hasOption("lu"));
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

		return options;
	}

	private static void printHelp() {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp("SRTool", getCommandLineOptions());
	}

	private static ProcessExec findZ3Location(List<String> z3Locations) {
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

	private static void getResult(VCGenerator vcgen, ProcessExec z3) throws InterruptedException {
		String vc = vcgen.generateVC().toString();

		if (verbose) {
			System.out.println("Running:\n" + vc);
		}

		String queryResult = "";
		try {
			queryResult = z3.execute(vc, TIMEOUT);
		} catch (ProcessTimeoutException | IOException | NullPointerException e) {
			if (verbose) e.printStackTrace();
			System.out.println("UNKNOWN");
			System.exit(1);
		}

		if (verbose) {
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

	private static void validateFile(String filename, boolean useLoopUnrolling) throws IOException, InterruptedException {
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

		ProcedureVisitor procedureVisitor = new ProcedureVisitor();
		Map<String, ProcedureSummarisation> summarisationMap = ctx.accept(procedureVisitor);

//		assert ctx.procedures.size() == 1; // For Part 1 of the coursework, this can be assumed

		final List<String> z3Locations = new ArrayList<>();
		z3Locations.add("z3");
		z3Locations.add("./z3");
		z3Locations.add("../../z3");
		z3Locations.add("../../../z3");

		ProcessExec z3 = findZ3Location(z3Locations);

		if (useLoopUnrolling) {
			int unwindingDepth = 1;
			while (unwindingDepth < LOOP_UNROLLING_DEPTH) {
				for (ProcedureDeclContext proc : ctx.procedures) {
					VCGenerator vcgen = new VCGenerator(proc, ctx.globals, summarisationMap, unwindingDepth);
					getResult(vcgen, z3);
				}

				// Exponentially increase depth
				unwindingDepth *= 2;
			}
		} else {
			for (ProcedureDeclContext proc : ctx.procedures) {
				VCGenerator vcgen = new VCGenerator(proc, ctx.globals, summarisationMap);
				getResult(vcgen, z3);
			}
		}

		System.out.println("CORRECT");
		System.exit(0);
	}
}
