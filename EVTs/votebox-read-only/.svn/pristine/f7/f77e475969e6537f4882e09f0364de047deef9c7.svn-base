package edu.uconn.cse.adder;

import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.StringExpression;

public class Vote {
    private List<ElgamalCiphertext> cipherList;

    public Vote() {

    }

    public Vote(List<ElgamalCiphertext> cipherList) {
        this.cipherList = cipherList;
    }

    public List<ElgamalCiphertext> getCipherList() {
        return cipherList;
    }

    Vote multiply(Vote vote) {
        List<ElgamalCiphertext> vec
            = new ArrayList<ElgamalCiphertext>(this.getCipherList().size());

        for (int i = 0; i < this.getCipherList().size(); i++) {
            ElgamalCiphertext ciphertext1
                = (ElgamalCiphertext) this.getCipherList().get(i);
            ElgamalCiphertext ciphertext2
                = (ElgamalCiphertext) vote.getCipherList().get(i);
            vec.add(ciphertext1.multiply(ciphertext2));
        }

        return new Vote(vec);
    }

    public String shortHash() {
        return "added"; // FIXME
    }

    public static Vote fromString(String s) {
        StringTokenizer st = new StringTokenizer(s, " ");
        List<ElgamalCiphertext> cList
            = new ArrayList<ElgamalCiphertext>(25); // XXX: what size?

        while (st.hasMoreTokens()) {
            String s2 = st.nextToken();

            try {
                ElgamalCiphertext ciphertext = ElgamalCiphertext.fromString(s2);
                cList.add(ciphertext);
            } catch (InvalidElgamalCiphertextException iece) {
                throw new InvalidVoteException(iece.getMessage());
            }
        }

        Vote vote = new Vote(cList);

        return vote;
    }

    public String toString() {
        StringBuffer sb = new StringBuffer(4096);

        for (int i = 0; i < cipherList.size(); i++) {
            ElgamalCiphertext ciphertext
                = (ElgamalCiphertext) cipherList.get(i);
            sb.append(ciphertext.toString());
            sb.append(" ");
        }

        return sb.toString().trim();
    }
 
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @return the S-Expression equivalent of this Vote
     */
    public ASExpression toASE(){
    	List<ASExpression> cList = new ArrayList<ASExpression>();
    	for(ElgamalCiphertext text : cipherList)
    		cList.add(text.toASE());
    	
    	return new ListExpression(StringExpression.makeString("vote"), new ListExpression(cList));
    }
    
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @param ase - S-Expression representation of a Vote
     * @return the Vote equivalent of ase
     */
    public static Vote fromASE(ASExpression ase){
    	ListExpression exp = (ListExpression)ase;
    	if(!(exp.get(0)).toString().equals("vote"))
    		throw new RuntimeException("Not vote");
    	
    	ListExpression cListE = (ListExpression)exp.get(1);
    	List<ElgamalCiphertext> cList = new ArrayList<ElgamalCiphertext>();
    	for(int i = 0; i < cListE.size(); i++)
    		cList.add(ElgamalCiphertext.fromASE(cListE.get(i)));
    	
    	return new Vote(cList);
    }
}
