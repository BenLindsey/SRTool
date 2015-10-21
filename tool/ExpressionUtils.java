package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCVisitor;

import java.util.List;

public class ExpressionUtils {
    private SimpleCSMTVistor vistor;

    public ExpressionUtils(SimpleCSMTVistor vistor) {
        this.vistor = vistor;
    }

    public String infixToPrefix(List<Token> ops, List<? extends ParserRuleContext> args) {
        return infixToPrefix(ops, args, 0);
    }

    public String infixToPrefix(List<Token> ops, List<? extends ParserRuleContext> args, int i) {
        return (i == args.size() - 1) ? vistor.visit(args.get(i)) :  // Recursive base case
                String.format("(%s %s %s)",
                        cOperatorToSMT(ops.get(i).getText()),        // Add the operator (* or + etc)
                        vistor.visit(args.get(i)),                   // Handle this expression
                        infixToPrefix(ops, args, i + 1)      // Recurse for next expression
                );
    }

    private String cOperatorToSMT(String operator) {
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

            default:
                return operator;
        }
    }
}
