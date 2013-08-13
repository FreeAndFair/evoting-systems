package votebox.events;

import java.math.BigInteger;

import edu.uconn.cse.adder.PublicKey;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.NoMatch;
import sexpression.StringExpression;
import sexpression.StringWildcard;
import sexpression.WildcardWildcard;
import votebox.crypto.interop.AdderKeyManipulator;

/**
 * We need a way to send the final public key to the VoteBoxes (as well as preserve such a key
 * in the record, as it changes from run to run).  Alongside the ballot seems as good a place as any
 * other.
 * 
 * @author Montrose
 *
 */
public class AuthorizedToCastWithNIZKsEvent extends AuthorizedToCastEvent {
	/**
     * The matcher for the AuthorizedToCastEvent.
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "authorized-to-cast-with-nizks" ), StringWildcard.SINGLETON,
                StringWildcard.SINGLETON, StringWildcard.SINGLETON, WildcardWildcard.SINGLETON );

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                int node = Integer.parseInt( ((ListExpression) res).get( 0 )
                        .toString() );
                /*byte[] nonce = ((StringExpression) ((ListExpression) res)
                        .get( 1 )).getBytesCopy();*/
                byte[] nonce = new BigInteger(((StringExpression) ((ListExpression) res)
                        .get( 1 )).toString()).toByteArray();
                byte[] ballot = ((StringExpression) ((ListExpression) res)
                        .get( 2 )).getBytesCopy();
                //PublicKey finalPubKey = PublicKey.fromString(((ListExpression) res).get(3).toString());
                PublicKey finalPubKey = PublicKey.fromASE(((ListExpression) res).get(3));
                
                return new AuthorizedToCastWithNIZKsEvent( serial, node, nonce, ballot, finalPubKey );
            }
            return null;
        };
    };

    /**
     * 
     * @return a MatcherRule for parsing this event type.
     */
    public static MatcherRule getMatcher(){
    	return MATCHER;
    }//getMatcher
    
    private PublicKey _finalPubKey;
    
    public AuthorizedToCastWithNIZKsEvent(int serial, int node, byte[] nonce, byte[] ballot, PublicKey finalPubKey){
    	super(serial, node, nonce, ballot);
    	
    	//System.out.println("AuthorizedToCastWithNIZKsEvent created: "+finalPubKey.toString());
    	
    	_finalPubKey = finalPubKey;
    	
    	//This is a global value, on both the VoteBox and Supervisor side.
    	AdderKeyManipulator.setCachedKey(finalPubKey);
    }
    
    public ASExpression toSExp() {
        /*return new ListExpression( StringExpression
                .makeString( "authorized-to-cast" ), StringExpression
                .makeString( Integer.toString( node ) ), StringExpression
                .makeString( nonce ), StringExpression.makeString( ballot ) );*/
    	return new ListExpression( 
    			StringExpression.makeString( "authorized-to-cast-with-nizks" ), 
                StringExpression.makeString( Integer.toString( getNode() ) ), 
                StringExpression.makeString( new BigInteger(getNonce()).toString() ), 
                StringExpression.makeString( getBallot() ),
                //StringExpression.makeString(_finalPubKey.toString()));
                _finalPubKey.toASE());
    }
}
