package proofParser;

import parser.Expression;

import java.util.Objects;

public class LineOfEvidence {
    private final Expression expression;
    private final Expression from;
    private final Expression fromTo;
    private final StringType stringType;
    private final int numberInList;
    private int linePosition = 0;
    private int usageCounter;


    LineOfEvidence(Expression expression, StringType type, int number) {
        this.expression = expression;
        this.stringType = type;
        this.numberInList = number;
        this.from = null;
        this.fromTo = null;
        this.usageCounter = 0;
    }

    LineOfEvidence(Expression expression, StringType type, Expression from, Expression fromTo) {
        this.expression = expression;
        this.stringType = type;
        this.from = from;
        this.fromTo = fromTo;
        this.usageCounter = 0;
        this.numberInList = -1;

    }

    Expression getExpression() {
        return expression;
    }

    Expression getFrom() {
        return from;
    }

    Expression getFromTo() {
        return fromTo;
    }

    StringType getStringType() {
        return stringType;
    }

    int getNumberInList() {
        return numberInList;
    }

    int getLinePosition() {
        return linePosition;
    }

    void setLinePosition(int linePosition) {
        this.linePosition = linePosition;
    }

    int getUsageCounter() {
        return usageCounter;
    }

    void incrementUsageCounter() {
        usageCounter++;
    }

    void decrementUsageCounter() {
        usageCounter--;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof LineOfEvidence)) return false;
        LineOfEvidence that = (LineOfEvidence) o;
        return expression.equals(that.expression);
    }

    @Override
    public int hashCode() {
        return Objects.hash(expression);
    }

    public enum StringType {
        AXIOM, HYPOTHESIS, MODUS_PONENS;
    }
}