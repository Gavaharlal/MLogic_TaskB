package parser;

public interface Expression {
    String getTree();

    ExpressionType getType();

    Expression getLeftOperand();

    Expression getRightOperand();

}