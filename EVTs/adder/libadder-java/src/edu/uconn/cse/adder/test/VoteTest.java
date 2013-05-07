package edu.uconn.cse.adder.test;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import junit.textui.TestRunner;
import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.ElgamalCiphertext;
import edu.uconn.cse.adder.InvalidVoteException;
import edu.uconn.cse.adder.Vote;

/**
 * Vote test.
 *
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 * @author David Walluck
 */
public class VoteTest extends TestCase {
    /**
     * Constructs a new vote test.
     *
     * @param name the name of the test
     */
    public VoteTest(String name) {
        super(name);
    }

    /**
     * The test.
     */
    public void test() {
        try {
            Vote vote = Vote.fromString("p123G135H246");

            assertEquals(new AdderInteger("123"),
                         ((ElgamalCiphertext) vote.getCipherList().get(0)).getP());
            assertEquals(new AdderInteger("135",
                         ((ElgamalCiphertext) vote.getCipherList().get(0)).getP()),
                         ((ElgamalCiphertext) vote.getCipherList().get(0)).getG());
            assertEquals(new AdderInteger("246",
                         ((ElgamalCiphertext) vote.getCipherList().get(0)).getP()),
                         ((ElgamalCiphertext) vote.getCipherList().get(0)).getH());
        } catch (InvalidVoteException ive) {
            fail();
        }

        ElgamalCiphertext ciphertext1 = new ElgamalCiphertext(new AdderInteger("135"),
                              new AdderInteger("246"),
                              new AdderInteger("111"),
                              new AdderInteger("123"));

        List/*<ElgamalCiphertext>*/ cipherList = new ArrayList/*<ElgamalCiphertext>*/(1);
        cipherList.add(ciphertext1);
        Vote vote1 = new Vote(cipherList);

        assertEquals(new AdderInteger("123"),
                     ((ElgamalCiphertext) vote1.getCipherList().get(0)).getP());
        assertEquals(new AdderInteger("135",
                     ((ElgamalCiphertext) vote1.getCipherList().get(0)).getP()),
                     ((ElgamalCiphertext) vote1.getCipherList().get(0)).getG());
        assertEquals(new AdderInteger("246",
                     ((ElgamalCiphertext) vote1.getCipherList().get(0)).getP()),
                     ((ElgamalCiphertext) vote1.getCipherList().get(0)).getH());
        assertEquals(new AdderInteger("111"),
                     ((ElgamalCiphertext) vote1.getCipherList().get(0)).getR());

        ElgamalCiphertext ciphertext2
            = new ElgamalCiphertext(new AdderInteger("135"),
                                    new AdderInteger("246"),
                                    new AdderInteger("111"),
                                    new AdderInteger("123"));
        cipherList.clear();
        cipherList.add(ciphertext2);
        Vote vote2 = new Vote(cipherList);

        assertEquals("p123G12H0",
                     ((ElgamalCiphertext) vote2.getCipherList().get(0)).toString());

        ElgamalCiphertext ciphertext3
            = new ElgamalCiphertext(new AdderInteger("135"),
                                    new AdderInteger("246"),
                                    new AdderInteger("111"),
                                    new AdderInteger("123"));
        cipherList.clear();
        cipherList.add(ciphertext3);
        Vote vote3 = new Vote(cipherList);

        assertEquals("3b589",
                     ((ElgamalCiphertext) vote3.getCipherList().get(0)).shortHash());

        try {
            Vote.fromString("p123G123");
            fail();
        } catch (InvalidVoteException ive) {

        }

        try {
            Vote.fromString("qGH");
            fail();
        } catch (InvalidVoteException ive) {

        }

        try {
            Vote.fromString("p123H123H123");
            fail();
        } catch (InvalidVoteException ive) {

        }
        try {
            Vote.fromString("p123G123G123");
            fail();
        } catch (InvalidVoteException ive) {

        }

        try {
            Vote.fromString("p123G123H12a");
            fail();
        } catch (InvalidVoteException ive) {

        }

        try {
            Vote.fromString("p123G123H123p123");
            fail();
        } catch (InvalidVoteException ive) {

        }

        try {
            Vote.
                fromString("p1045854189839G17609338705H264688728687 q10458541"
                           + "89839y634399786697y449024425938y211966529664z4986"
                           + "42099355z161654952943z408688746982s50028254339s40"
                           + "5915557693s360340621934c222506129443c148756415697"
                           + "c387464678922");
            fail();
        } catch (InvalidVoteException ive) {

        }

        try {
            Vote.
                  fromString("p1045854189839G17609338705H264688728687 p104585"
                             + "4189839y634399786697y449024425938y211966529664z"
                             + "498642099355z161654952943z408688746982s50028254"
                             + "339s405915557693s360340621934c222506129443c1487"
                             + "56415697c387464678922 xyz");
            fail();
        } catch (InvalidVoteException ive) {

        }

        try {
            Vote vote
                = Vote.fromString("p1045854189839G17609338705H264688728687 p1"
                                  + "045854189839y634399786697y449024425938y211"
                                  + "966529664z498642099355z161654952943z408688"
                                  + "746982s50028254339s405915557693s3603406219"
                                  + "34c222506129443c148756415697c387464678922"
                                  );
            assertTrue(vote != null);
            fail();
        } catch (InvalidVoteException ive) {

        }

        try {
            Vote.
                  fromString("p1045854189839G17609338705H264688728687 p104585"
                             + "4189839y634399786697y449024425938y211966529664z"
                             + "498642099355z161654952943z408688746982s50028254"
                             + "339s405915557693s360340621934c222506129443c1487"
                             + "56415697c387464678922 xyz");
            fail();
        } catch (InvalidVoteException ive) {

        }

        //try {
            //Vote vote
            //    = Vote.fromString("p1045854189839G17609338705H264688728687 p1"
            //                      + "045854189839y634399786697y449024425938y211"
            //                      + "966529664z498642099355z161654952943z408688"
            //                      + "746982s50028254339s405915557693s3603406219"
            //                     + "34c222506129443c148756415697c387464678922"
            //                      );

            //assertEquals("p1045854189839G17609338705H264688728687 p1045854189"
            //             + "839y634399786697y449024425938y211966529664z49864209"
            //             + "9355z161654952943z408688746982s50028254339s40591555"
            //             + "7693s360340621934c222506129443c148756415697c3874646"
            //             + "78922",
            //             ((ElgamalCiphertext) vote.getCipherList().get(0)).toString());
            //assertEquals("p1045854189839y634399786697y449024425938y2119665296"
            //             + "64z498642099355z161654952943z408688746982s500282543"
            //             + "39s405915557693s360340621934c222506129443c148756415"
            //             + "697c387464678922",
            //             ((ElgamalCiphertext) vote.getCipherList().get(0)).
            //                                  getProof().toString());
            //System.out.println("PROOF: " + ((ElgamalCiphertext) vote.getCipherList().get(0)).
            //                                getProof().toString());
        //} catch (InvalidVoteException ive) {
        //    fail();
        //}
    }
    /**
     * The main method.
     *
     * @param args the main parameters
     */
    public static void main(String[] args) {
        TestRunner.run(VoteTest.class);
    }
}
