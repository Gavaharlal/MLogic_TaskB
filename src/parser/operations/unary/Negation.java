package parser.operations.unary;

import parser.Expression;
import parser.ExpressionType;

public class Negation extends UnaryOperation {

    public Negation(Expression operand) {
        super(operand);
    }

    @Override
    public String getToken() {
        return "!";
    }

    @Override
    public ExpressionType getType() {
        return ExpressionType.NEGATION;
    }
}
