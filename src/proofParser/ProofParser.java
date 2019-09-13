package proofParser;

import parser.Expression;
import parser.ExpressionParser;
import parser.ExpressionType;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

public class ProofParser {

    private final ExpressionParser expressionParser = new ExpressionParser();
    private final List<Expression> hypotheses = new ArrayList<>();
    private final Map<Expression, Set<Expression>> modusPonensResult = new HashMap<>();
    private final Map<Expression, LineOfEvidence> expressionToLine = new HashMap<>();
    private final Set<Expression> proofSet = new HashSet<>();
    private final ArrayList<LineOfEvidence> evidenceArrayList = new ArrayList<>();
    private final BufferedReader in;

    private boolean isEvidenceCorrect;
    private String heading;


    public ProofParser() throws FileNotFoundException {
//        in = new BufferedReader(new InputStreamReader(new FileInputStream("in.txt")));
        in = new BufferedReader(new InputStreamReader(System.in));
    }

    public void parse() throws IOException {
        heading = in.readLine();
        Expression theorem = parseHeading(heading);
        isEvidenceCorrect = true;
        String curLine;
        Expression lastStatement = null;
        while ((curLine = in.readLine()) != null) {
            Expression expression = expressionParser.parse(curLine);
            lastStatement = expression;

            if (isNotAxiom(expression, true) && isNotHypothesis(expression, true) && isNotModusPonens(expression, true)) {
                isEvidenceCorrect = false;
                break;
            }

            if (expression.equals(theorem)) {
                ResultPair result = scanRest(lastStatement);
                isEvidenceCorrect = result.isCorrect;
                lastStatement = result.lastExpression;
                break;
            }
        }

        if (!evidenceArrayList.isEmpty()) {
            evidenceArrayList.get(evidenceArrayList.size() - 1).incrementUsageCounter();
        }

        if (lastStatement == null || !lastStatement.equals(theorem)) {
            isEvidenceCorrect = false;
        }
    }

    public void printEvidence(Writer out) throws IOException {
        if (isEvidenceCorrect) {
            minimizeEvidence();
            out.write(heading + System.lineSeparator());
            int curLineNumber = 1;
            for (LineOfEvidence lineOfEvidence : evidenceArrayList) {
                if (lineOfEvidence.getUsageCounter() > 0) {
                    out.write("[" + curLineNumber + ". ");
                    switch (lineOfEvidence.getStringType()) {
                        case AXIOM:
                            out.write("Ax. sch. " + lineOfEvidence.getNumberInList());
                            break;
                        case HYPOTHESIS:
                            out.write("Hypothesis " + lineOfEvidence.getNumberInList());
                            break;
                        case MODUS_PONENS:
                            out.write("M.P. " + expressionToLine.get(lineOfEvidence.getFromTo()).getLinePosition()
                                    + ", " + expressionToLine.get(lineOfEvidence.getFrom()).getLinePosition());
                            break;
                    }
                    out.write("] ");
                    out.write(lineOfEvidence.getExpression() + "\n");
                    lineOfEvidence.setLinePosition(curLineNumber++);
                }
            }
        } else {
            out.write("Proof is incorrect" + System.lineSeparator());
        }
        out.close();
    }

    private ResultPair scanRest(Expression last) throws IOException {
        Expression lastExpression = last;
        String curLine;
        while ((curLine = in.readLine()) != null) {

            lastExpression = expressionParser.parse(curLine);

            if (isNotAxiom(lastExpression, false) && isNotHypothesis(lastExpression, false) && isNotModusPonens(lastExpression, false)) {
                return new ResultPair(false, lastExpression);
            }
        }
        return new ResultPair(true, lastExpression);
    }

    private static class ResultPair {
        boolean isCorrect;
        Expression lastExpression;

        ResultPair(boolean isCorrect, Expression lastOne) {
            this.isCorrect = isCorrect;
            this.lastExpression = lastOne;
        }
    }


    private boolean isNotAxiom(Expression expression, boolean addToEvidence) {
        int num = AxiomChecker.check(expression);
        if (num == -1) {
            return true;
        } else {
            if (add(expression)) {
                LineOfEvidence lineOfEvidence = new LineOfEvidence(expression, LineOfEvidence.StringType.AXIOM, num);
                if (addToEvidence) {
                    evidenceArrayList.add(lineOfEvidence);
                }
                expressionToLine.putIfAbsent(expression, lineOfEvidence);
            }
            return false;
        }
    }

    private boolean isNotHypothesis(Expression expression, boolean addToEvidence) {
        for (int i = 0; i < hypotheses.size(); i++) {
            Expression hypothesis = hypotheses.get(i);
            if (hypothesis.equals(expression)) {
                if (add(expression)) {
                    LineOfEvidence lineOfEvidence = new LineOfEvidence(expression, LineOfEvidence.StringType.HYPOTHESIS, i + 1);
                    if (addToEvidence) {
                        evidenceArrayList.add(lineOfEvidence);
                    }
                    expressionToLine.putIfAbsent(expression, lineOfEvidence);
                }
                return false;
            }
        }

        return true;
    }

    private boolean isNotModusPonens(Expression expression, boolean addToEvidence) {
        if (!modusPonensResult.containsKey(expression)) return true;
        for (Expression implication : modusPonensResult.get(expression)) {
            if (proofSet.contains(implication.getLeftOperand())) {
                if (add(expression)) {
                    LineOfEvidence lineOfEvidence = new LineOfEvidence(expression, LineOfEvidence.StringType.MODUS_PONENS, implication.getLeftOperand(), implication);
                    expressionToLine.putIfAbsent(expression, lineOfEvidence);
                    if (addToEvidence) {
                        evidenceArrayList.add(lineOfEvidence);
                        expressionToLine.get(implication.getLeftOperand()).incrementUsageCounter();
                        expressionToLine.get(implication).incrementUsageCounter();
                    }
                }
                return false;
            }
        }
        return true;
    }

    private boolean add(Expression expression) {
        if (expression.getType() == ExpressionType.IMPLICATION) {
            modusPonensResult.putIfAbsent(expression.getRightOperand(), new HashSet<>());
            modusPonensResult.get(expression.getRightOperand()).add(expression);
        }
        return proofSet.add(expression);
    }

    private Expression parseHeading(String heading) {
        int turnstileIdx = heading.indexOf("|-");
        String hypsList = heading.substring(0, turnstileIdx);
        if (turnstileIdx > 0) {
            List<Expression> hyps = Arrays.stream(hypsList.split(","))
                    .map(expressionParser::parse)
                    .collect(Collectors.toList());
            hypotheses.addAll(hyps);
        }
        return expressionParser.parse(heading.substring(turnstileIdx + 2));
    }


    private void minimizeEvidence() {
        ListIterator<LineOfEvidence> listIterator = evidenceArrayList.listIterator(evidenceArrayList.size());
        while (listIterator.hasPrevious()) {
            LineOfEvidence curLine = listIterator.previous();
            if (curLine.getUsageCounter() == 0 && curLine.getStringType() == LineOfEvidence.StringType.MODUS_PONENS) {
                expressionToLine.get(curLine.getFrom()).decrementUsageCounter();
                expressionToLine.get(curLine.getFromTo()).decrementUsageCounter();
            }
        }
    }

}
