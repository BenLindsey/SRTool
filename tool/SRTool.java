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
	static boolean verbose = false;

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
					new Z3().validateFile(commandLine.getOptionValue("f"), commandLine.hasOption("lu"));
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

		return options;
	}

	private static void printHelp() {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp("SRTool", getCommandLineOptions());
	}
}
