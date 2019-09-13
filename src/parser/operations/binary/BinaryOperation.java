package parser.operations.binary;

import parser.Expression;
import parser.operations.Operation;

import java.util.Objects;

public abstract class BinaryOperation implements Expression, Operation {
    private final Expression leftOp;
    private final Expression rightOp;

    BinaryOperation(Expression left, Expression right) {
        this.leftOp = left;
        this.rightOp = right;
    }

    @Override
    public String getTree() {
        return "(" + getToken() + "," + leftOp.getTree() + "," + rightOp.getTree() + ")";
    }

    @Override
    public String toString() {
        return "(" + leftOp.toString() + " " + getToken() + " " + rightOp.toString() + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        BinaryOperation that = (BinaryOperation) o;
        return Objects.equals(leftOp, that.leftOp) &&
                Objects.equals(rightOp, that.rightOp);
    }

    @Override
    public int hashCode() {
        return Objects.hash(leftOp, rightOp);
    }

    @Override
    public Expression getLeftOperand() {
        return leftOp;
    }

    @Override
    public Expression getRightOperand() {
        return rightOp;
    }
}