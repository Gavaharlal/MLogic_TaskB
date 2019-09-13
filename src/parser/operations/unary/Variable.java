package parser.operations.unary;

import parser.Expression;
import parser.ExpressionType;

import java.util.Objects;

public class Variable implements Expression {

    private final String name;

    public Variable(String name) {
        this.name = name;
    }

    @Override
    public String getTree() {
        return name;
    }

    @Override
    public ExpressionType getType() {
        return ExpressionType.VARIABLE;
    }

    @Override
    public Expression getLeftOperand() {
        return null;
    }

    @Override
    public Expression getRightOperand() {
        return null;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Variable variable = (Variable) o;
        return Objects.equals(name, variable.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }
}
