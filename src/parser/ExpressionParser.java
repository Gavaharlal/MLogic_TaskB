package parser;

import parser.operations.binary.Conjunction;
import parser.operations.binary.Disjunction;
import parser.operations.binary.Implication;
import parser.operations.unary.Negation;
import parser.operations.unary.Variable;
import parser.tokenozer.Token;
import parser.tokenozer.TokenType;
import parser.tokenozer.Tokenizer;

public class ExpressionParser {
    private Tokenizer tokens;

    public Expression parse(String expression) {
        tokens = new Tokenizer(expression);
        return expression();
    }

    private Expression expression() {
        Expression acc = implication();

        if (tokens.hasNext()) {
            tokens.next();
        }

        return acc;
    }


    private Expression implication() {
        Expression acc = disjunction();
        while (tokens.hasNext()) {
            Token operation = tokens.next();
            if (operation.getType() == TokenType.IMPL) {
                acc = new Implication(acc, implication());
            } else {
                tokens.prev();
                return acc;
            }
        }
        return acc;
    }

    private Expression disjunction() {
        Expression acc = conjunction();
        while (tokens.hasNext()) {
            Token operation = tokens.next();
            if (operation.getType() == TokenType.DISJ) {
                acc = new Disjunction(acc, conjunction());
            } else {
                tokens.prev();
                return acc;
            }
        }
        return acc;
    }

    private Expression conjunction() {
        Expression acc = primary();
        while (tokens.hasNext()) {
            Token operation = tokens.next();
            if (operation.getType() == TokenType.CONJ) {
                acc = new Conjunction(acc, primary());
            } else {
                tokens.prev();
                return acc;
            }
        }
        return acc;
    }

    private Expression primary() {
        Token token = tokens.next();
        Expression primary = null;

        switch (token.getType()) {
            case VARIABLE:
                primary = new Variable(token.getValue());
                break;

            case NEG:
                primary = new Negation(primary());
                break;

            case LEFT_BR:
                primary = expression();
                return primary;

            default:
                tokens.prev();
        }

        return primary;
    }
}