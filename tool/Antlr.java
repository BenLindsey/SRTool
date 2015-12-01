package tool;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import parser.SimpleCLexer;
import parser.SimpleCParser;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;

public class Antlr {
    private static SimpleCParser.ProgramContext getProgamContext(String name, InputStream inputStream) throws IOException {
        ANTLRInputStream input = new ANTLRInputStream(inputStream);
        SimpleCLexer lexer = new SimpleCLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SimpleCParser parser = new SimpleCParser(tokens);
        SimpleCParser.ProgramContext ctx = parser.program();
        if(parser.getNumberOfSyntaxErrors() > 0) {
            System.exit(1);
        }
        Typechecker tc = new Typechecker();
        tc.visit(ctx);
        tc.resolve();
        if(tc.hasErrors()) {
            System.err.println("Errors were detected when typechecking " + name + ":");
            for(String err : tc.getErrors()) {
                System.err.println("  " + err);
            }
            System.exit(1);
        }

        return ctx;
    }

    public static SimpleCParser.ProgramContext getProgramContextFromFile(String fileName) throws IOException {
        return getProgamContext(fileName, new FileInputStream(fileName));
    }

    public static SimpleCParser.ProgramContext getProgramContextFromText(String text) throws IOException {
        return getProgamContext("<text input>", new ByteArrayInputStream(text.getBytes(Charset.defaultCharset())));
    }



}


