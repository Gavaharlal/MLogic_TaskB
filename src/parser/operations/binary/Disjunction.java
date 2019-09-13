package parser.operations.binary;

import parser.Expression;
import parser.ExpressionType;

public class Disjunction extends BinaryOperation {

    public Disjunction(Expression leftOperand, Expression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public String getToken() {
        return "|";
    }

    @Override
    public ExpressionType getType() {
        return ExpressionType.DISJUNCTION;
    }
}
