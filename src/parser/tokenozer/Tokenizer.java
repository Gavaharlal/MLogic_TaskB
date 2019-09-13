package parser.tokenozer;

import java.util.ArrayList;
import java.util.List;


public class Tokenizer {
    private List<Token> tokens = new ArrayList<>();
    private int curr;
    private String expr;

    public Tokenizer(String expr) {
        this.expr = expr;
        curr = -1;
        tokenize();
        tokens.add(new Token(TokenType.END, "end of parser"));
    }

    public boolean hasNext() {
        return curr < tokens.size() - 1;
    }

    public Token next() {
        return tokens.get(++curr);
    }

    public Token prev() {
        return tokens.get(--curr);
    }

    public Token current() {
        return tokens.get(curr);
    }

    public boolean isFirst() {
        return curr == 0;
    }

    private void tokenize() {
        for (int i = 0; i < expr.length(); i++) {
            if (Character.isWhitespace(expr.charAt(i))) {
                continue;
            }
            switch (expr.charAt(i)) {
                case '(':
                    tokens.add(new Token(TokenType.LEFT_BR, "("));
                    break;

                case ')':
                    tokens.add(new Token(TokenType.RIGHT_BR, ")"));
                    break;

                case '&':
                    tokens.add(new Token(TokenType.CONJ, "&"));
                    break;

                case '|':
                    tokens.add(new Token(TokenType.DISJ, "|"));
                    break;

                case '!':
                    tokens.add(new Token(TokenType.NEG, "!"));
                    break;

                case '-':
                    tokens.add(new Token(TokenType.IMPL, "->"));
                    i++;
                    break;

                default:
                    int j = i;
                    while (j < expr.length() && isVariablePart(expr.charAt(j))) {
                        j++;
                    }
                    String variable = expr.substring(i, j);
                    tokens.add(new Token(TokenType.VARIABLE, variable));
                    i = j - 1;
            }
        }
    }

    private boolean isVariablePart(char c) {
        if ('A' <= c && c <= 'Z') return true;
        if ('a' <= c && c <= 'z') return true;
        if ('0' <= c && c <= '9') return true;
        if (c =='’') return true;
        return c == '\'';
    }

}