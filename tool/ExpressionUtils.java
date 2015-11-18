package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCParser;

import java.util.List;

public class ExpressionUtils {
    private SimpleCSMTVisitor visitor;

    public ExpressionUtils(SimpleCSMTVisitor visitor) {
        this.visitor = visitor;
    }

    public SMT infixToSMT(List<Token> ops, List<? extends ParserRuleContext> args) {
        return infixToSMT(ops, args, args.size() - 1);
    }

    public SMT infixToSMT(List<Token> ops, List<? extends ParserRuleContext> args, int i) {
        final SMT current = visitor.visit(args.get(i));

        if (i == 0) {
            return current;
        }

        final String operator = ops.get(i - 1).getText();

        final SMT next = infixToSMT(ops, args, i - 1);

        final SMT prefix = SMT.createPrefix(
                infixOperatorToPrefix(operator),
                operatorRequiresBoolean(operator) ? next.asBoolean() : next.asBitVector(),
                operatorRequiresBoolean(operator) ? current.asBoolean() : current.asBitVector(),
                operatorCreatesBoolean(operator)
        );

        // Operator special cases
        switch (operator) {
            case "!=":
                return SMT.createNot(prefix.asBoolean());
            //case "%": todo is this behaviour defined by default?
            case "/":
                return SMT.createITE(
                        SMT.createIsZero(current.asBitVector()),
                        next.asBitVector(),
                        prefix.asBitVector()
                );

            case ">>":
                return SMT.createITE(
                        SMT.createIsOverOrEqual(current.asBitVector(), 32),
                        SMT.createNumber("0"),
                        prefix.asBitVector()
                );

            default:
                return prefix;
        }
    }

    public SMT ternaryToSMT(List<? extends ParserRuleContext> args) {
        return ternaryToSMT(args, 0);
    }

    public SMT ternaryToSMT(List<? extends ParserRuleContext> args, int i) {
        return (i == args.size() - 1) ? visitor.visit(args.get(i)) :  // Recursive base case
                SMT.createITE(
                        visitor.visit(args.get(i)),
                        visitor.visit(args.get(i + 1)).asBitVector(),
                        ternaryToSMT(args, i + 2).asBitVector()
                );
    }

    public SMT unaryToSMT(List<Token> ops, SimpleCParser.AtomExprContext arg) {
        return unaryToSMT(ops, arg, 0);
    }

    public SMT unaryToSMT(List<Token> ops, SimpleCParser.AtomExprContext arg, int i) {
        if (i == ops.size()) {
            return visitor.visit(arg);
        }

        final String operator = ops.get(i).getText();

        // Operator special cases
        switch (operator) {
            case "+":
                return unaryToSMT(ops, arg, i + 1).asBitVector();

            default:
                SMT value = unaryToSMT(ops, arg, i + 1);

                if(operatorRequiresBoolean(operator)) {
                    value = value.asBoolean();
                } else {
                    value = value.asBitVector();
                }

                return SMT.createUnary(
                        unaryOperatorToPrefix(operator),
                        value,
                        operatorCreatesBoolean(operator)
                );
        }
    }

    private boolean operatorCreatesBoolean(String operator) {
        switch(operator) {
            case "&&":
            case "||":
            case ">":
            case "<":
            case ">=":
            case "<=":
            case "!=":
            case "==":
            case "!":
                return true;
            default:
                return false;
        }
    }

    private boolean operatorRequiresBoolean(String operator) {
        switch(operator) {
            case "&&":
            case "||":
            case "!":
                return true;
            default:
                return false;
        }
    }

    private String unaryOperatorToPrefix(String operator) {
        switch (operator) {
            case "-":
                return "bvneg";

            case "!":
                return "not";

            case "~":
                return "bvnot";

            default:
                return operator;
        }
    }

    private String infixOperatorToPrefix(String operator) {
        switch (operator) {
            case "==":
                return "=";

            case "!=":
                return "=";

            case "+":
                return "bvadd";

            case "-":
                return "bvsub";

            case "*":
                return "bvmul";

            case "/":
                return "bvsdiv";

            case "%":
                return "bvsmod";  //todo should this be signed or unsigned?

            case "<<":
                return "bvshl";

            case ">>":
                return "bvashr";  //todo should this be signed or unsigned?

            case "<":
                return "bvslt";   //todo should this be signed or unsigned?

            case ">":
                return "bvsgt";   //todo should this be signed or unsigned?

            case ">=":
                return "bvsge";   //todo should this be signed or unsigned?

            case "<=":
                return "bvsle";   //todo should this be signed or unsigned?

            case "&&":
                return "and";

            case "||":
                return "or";

            case "|":
                return "bvor";    //todo do these work with bitvectors?

            case "&":
                return "bvand";    //todo do these work with bitvectors?

            case "^":
                return "bvxor";    //todo do these work with bitvectors?

            default:
                return operator;
        }
    }

}
