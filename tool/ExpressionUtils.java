package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCParser;

import java.util.List;

public class ExpressionUtils {
    private SimpleCSMTVistor visitor;

    public ExpressionUtils(SimpleCSMTVistor visitor) {
        this.visitor = visitor;
    }

    public String infixToPrefix(List<Token> ops, List<? extends ParserRuleContext> args) {
        return infixToPrefix(ops, args, 0);
    }

    public String infixToPrefix(List<Token> ops, List<? extends ParserRuleContext> args, int i) {
        return (i == args.size() - 1) ? visitor.visit(args.get(i)) :  // Recursive base case
                String.format("(%s %s %s)",
                        cOperatorToSMT(ops.get(i).getText()),         // Add the operator (* or + etc)
                        visitor.visit(args.get(i)),                   // Handle this expression
                        infixToPrefix(ops, args, i + 1)               // Recurse for next expression
                );
    }

    public String ternaryToITE(List<? extends ParserRuleContext> args) {
        return ternaryToITE(args, 0);
    }

    public String ternaryToITE(List<? extends ParserRuleContext> args, int i) {
        return (i == args.size() - 1) ? visitor.visit(args.get(i)) :  // Recursive base case
                String.format("(ite %s %s %s)",
                        visitor.visit(args.get(i)),
                        visitor.visit(args.get(i + 1)),
                        ternaryToITE(args, i + 2)
                );
    }

    public String cOperatorToSMT(String operator) {
        switch (operator) {
            case "==":
                return "=";

            case "!=":
                return "!=";    //todo is there a !=?

            case "+":
                return "bvadd";

            case "-":
                return "bvsub";

            case "*":
                return "bvmul";

            case "/":
                return "div";

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

            default:
                return operator;
        }
    }
}
