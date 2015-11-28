package tool.Fuzz;

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

    public static Code createFunction(String name, List<Code> statements) {
        return new CompositeCode(
                createFunctionHeader(name),
                createBlock(new CompositeCode(statements))
        );
    }

    public static SingleCode createFunctionHeader(String name) {
        return new SingleCode(
                String.format("int %s()\n", name),
                true,
                name.equals("main")
        );
    }

    public static Code createAssert(String text) {
        return createFromFormat("assert(%s);\n", text);
    }

    public static Code createExecutable(Code code) {
        return new CompositeCode(
                new SingleCode("#include <assert.h>\n"),
                code.ensureMainFunction()
        );
    }

    public static Code createDeclaration(String text) {
        return createFromFormat("int %s;\n", text);
    }

    public static Code createAssign(String lhs, Code rhs) {
        return createFromFormat("%s = %s;\n", lhs, rhs);
    }

    public static Code createReturn(Code code) {
        return createFromFormat("return %s;\n", code);
    }

    public static Code createWhile(Code condition, Code body) {
        return new CompositeCode(
                createFromFormat("while(%s)\n", condition),
                createBlock(body)
        );
    }
}
