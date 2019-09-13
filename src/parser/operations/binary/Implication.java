package parser.operations.binary;

import parser.Expression;
import parser.ExpressionType;

public class Implication extends BinaryOperation {


    public Implication(Expression leftOperand, Expression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public String getToken() {
        return "->";
    }

    @Override
    public ExpressionType getType() {
        return ExpressionType.IMPLICATION;
    }
}
