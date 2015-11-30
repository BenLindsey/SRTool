package tool.Fuzz;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CodeFactory {
    public static Code createEmpty() {
        return new SingleCode("");
    }

    public static Code merge(Code left, Code right) {
        return new CompositeCode(left, right);
    }

    public static Code createFromFormat(String format, Object... args) {
        return new SingleCode(String.format(format, args));
    }

    public static Code createBlock(Code code) {
        return new CompositeCode(
                new SingleCode("{\n"),
                code.indent(),
                new SingleCode("}\n")
        );
    }

    public static Code createFunction(String name, List<String> params, List<Code> statements) {
        return new CompositeCode(
                createFunctionHeader(name, params),
                createBlock(new CompositeCode(statements))
        );
    }
    public static SingleCode createFunctionHeader(String name) {
        return createFunctionHeader(name, new ArrayList<String>());
    }


    public static SingleCode createFunctionHeader(String name, List<String> params) {
        String paramList = "";

        if(!name.equals("main")) {
            for(String param: params) {
                paramList += (paramList.length() > 0 ? ", " : "") + "int " + param;
            }
        }

        return new SingleCode(
                String.format("int %s(%s)\n", name, paramList),
                true,
                name.equals("main")
        );
    }

    public static Code createAssert(Code code) {
        return createFromFormat("assert(%s);\n", code);
    }

    public static Code createExecutable(Code code) {
        return new CompositeCode(
                new SingleCode("#include <assert.h>\n"),
                code.ensureMainFunction()
        );
    }

    public static Code createDeclaration(String text, int fuzz) {
        return createFromFormat("int %s = %d;\n", text, fuzz);
    }

    public static Code createAssign(String lhs, Code rhs) {
        return createFromFormat("%s = %s;\n", lhs, rhs);
    }

    public static Code createReturn(Code code, boolean main) {
        return createFromFormat("return %s;\n", main? "0" : code);
    }

    public static Code createExit() {
        return createFromFormat("exit(0);\n");
    }

    public static Code createWhile(Code condition, Code body, Code invarient) {
        return new CompositeCode(
                invarient,
                createFromFormat("while(%s)\n", condition),
                createBlock(
                        new CompositeCode(
                                body,
                                invarient
                        )
                )
        );
    }

    public static Code createAssume(Code condition) {
        return createIf(createNot(condition), createExit());
    }

    private static Code createNot(Code condition) {
        return createFromFormat("!(%s)", condition);
    }

    public static Code createIf(Code condition, Code then) {
        return new CompositeCode(
                createFromFormat("if(%s)\n", condition),
                createBlock(then)
        );
    }

    public static Code createIf(Code condition, Code thenBlock, Code elseBlock) {
        if(elseBlock == null) {
            return createIf(condition, thenBlock);
        }

        return new CompositeCode(
                createFromFormat("if(%s)\n", condition),
                createBlock(thenBlock),
                createFromFormat("else\n"),
                createBlock(elseBlock)
        );
    }

    private static Code createNumber(int i) {
        return new SingleCode(Integer.toString(i));
    }

    public static Code createNumber(String s) {
        return new SingleCode(s);
    }

    public static Code createVariable(String result) {
        return new SingleCode(result);
    }

    public static Code createTernary(Code condition, Code thenBlock, Code elseBlock) {
        return createFromFormat("((%s) ? (%s) : (%s))", condition, thenBlock, elseBlock);
    }

    public static Code createUnary(String operator, Code value) {
        return createFromFormat("%s(%s)", operator, value);
    }

    public static Code createInfix(String operator, Code left, Code right) {
        return createFromFormat("%s %s %s", left, operator, right);
    }

    public static Code createHavoc(String text, int fuzz) {
        return createFromFormat("%s = %d;\n", text, fuzz); //todo
    }


    public static Code createParenthesis(Code visit) {
        return createFromFormat("(%s)", visit);
    }
}
