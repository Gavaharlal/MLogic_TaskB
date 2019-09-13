import proofParser.ProofParser;

import java.io.*;

public class Main {

    public static void main(String[] args) throws IOException {
        ProofParser proofParser = new ProofParser();
        proofParser.parse();
        proofParser.printEvidence(new OutputStreamWriter(System.out));
    }
}
