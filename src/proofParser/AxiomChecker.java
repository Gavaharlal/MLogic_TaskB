package proofParser;

import parser.Expression;
import parser.ExpressionParser;
import parser.ExpressionType;

import java.util.HashMap;

class AxiomChecker {
    private static final ExpressionParser EXPRESSION_PARSER = new ExpressionParser();
    private static final Expression AX1_EXPR = EXPRESSION_PARSER.parse("A -> B -> A");
    private static final Expression AX2_EXPR = EXPRESSION_PARSER.parse("(A -> B) -> (A -> B -> C) -> (A -> C)");
    private static final Expression AX3_EXPR = EXPRESSION_PARSER.parse("A -> B -> A & B");
    private static final Expression AX4_EXPR = EXPRESSION_PARSER.parse("A & B -> A");
    private static final Expression AX5_EXPR = EXPRESSION_PARSER.parse("A & B -> B");
    private static final Expression AX6_EXPR = EXPRESSION_PARSER.parse("A -> A | B");
    private static final Expression AX7_EXPR = EXPRESSION_PARSER.parse("B -> A | B");
    private static final Expression AX8_EXPR = EXPRESSION_PARSER.parse("(A -> C) -> (B -> C) -> (A | B -> C)");
    private static final Expression AX9_EXPR = EXPRESSION_PARSER.parse("(A -> B) -> (A -> !B) -> !A");
    private static final Expression AX10_EXPR = EXPRESSION_PARSER.parse("!!A -> A");

    static int check(Expression expression) {
        if (checkMatching(expression, AX1_EXPR, new HashMap<>())) return 1;
        if (checkMatching(expression, AX2_EXPR, new HashMap<>())) return 2;
        if (checkMatching(expression, AX3_EXPR, new HashMap<>())) return 3;
        if (checkMatching(expression, AX4_EXPR, new HashMap<>())) return 4;
        if (checkMatching(expression, AX5_EXPR, new HashMap<>())) return 5;
        if (checkMatching(expression, AX6_EXPR, new HashMap<>())) return 6;
        if (checkMatching(expression, AX7_EXPR, new HashMap<>())) return 7;
        if (checkMatching(expression, AX8_EXPR, new HashMap<>())) return 8;
        if (checkMatching(expression, AX9_EXPR, new HashMap<>())) return 9;
        if (checkMatching(expression, AX10_EXPR, new HashMap<>())) return 10;
        return -1;
    }

    private static boolean checkMatching(Expression expression, Expression pattern, HashMap<String, Expression> values) {
        if (expression == null) return false;
        if (pattern.getType() == ExpressionType.VARIABLE) {
            if (values.containsKey(pattern.toString())) {
                return values.get(pattern.toString()).equals(expression);
            } else {
                values.put(pattern.toString(), expression);
                return true;
            }
        } else {
            if (expression.getType() == ExpressionType.VARIABLE) return false;
            if (expression.getType() != pattern.getType()) return false;
            return checkMatching(expression.getLeftOperand(), pattern.getLeftOperand(), values) && checkMatching(expression.getRightOperand(), pattern.getRightOperand(), values);
        }
    }

    private AxiomChecker() {
    }
}
