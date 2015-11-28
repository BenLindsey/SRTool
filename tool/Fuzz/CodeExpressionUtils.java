package tool.Fuzz;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCParser;

import java.util.List;

/**
 * Created by bl2312 on 28/11/15.
 */
public class CodeExpressionUtils {
    private CodeVisitor visitor;

    public CodeExpressionUtils(CodeVisitor visitor) {
        this.visitor = visitor;
    }

    public Code ternaryToCode(List<? extends ParserRuleContext> args) {
        return ternaryToCode(args, 0);
    }

    public Code ternaryToCode(List<? extends ParserRuleContext> args, int i) {
        return (i == args.size() - 1) ? visitor.visit(args.get(i)) :  // Recursive base case
                CodeFactory.createTernary(
                        visitor.visit(args.get(i)),
                        visitor.visit(args.get(i + 1)),
                        ternaryToCode(args, i + 2)
                );
    }

    public Code infixToCode(List<Token> ops, List<? extends ParserRuleContext> args) {
        return infixToCode(ops, args, args.size() - 1);
    }

    public Code infixToCode(List<Token> ops, List<? extends ParserRuleContext> args, int i) {
        final Code current = visitor.visit(args.get(i));

        if (i == 0) {
            return current;
        }

        final String operator = ops.get(i - 1).getText();

        final Code next = infixToCode(ops, args, i - 1);

        //todo special cases?

        return CodeFactory.createInfix(operator, next, current);
    }

    public Code unaryToCode(List<Token> ops, SimpleCParser.AtomExprContext arg) {
        return unaryToCode(ops, arg, 0);
    }

    public Code unaryToCode(List<Token> ops, SimpleCParser.AtomExprContext arg, int i) {
        if (i == ops.size()) {
            return visitor.visit(arg);
        }

        final String operator = ops.get(i).getText();

        // Operator special cases
        switch (operator) {
            case "+":
                return unaryToCode(ops, arg, i + 1);

            default:
                Code value = unaryToCode(ops, arg, i + 1);

                return CodeFactory.createUnary(operator, value);
        }
    }
}
