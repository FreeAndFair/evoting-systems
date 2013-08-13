package votebox.events;

import java.util.ArrayList;
import java.util.List;

import edu.uconn.cse.adder.AdderInteger;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.ListWildcard;
import sexpression.NoMatch;
import sexpression.StringExpression;
import sexpression.StringWildcard;

public class AdderChallengeEvent extends ChallengeEvent {
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "adder-challenge" ), StringWildcard.SINGLETON,
                new ListWildcard(new ListWildcard(StringWildcard.SINGLETON)));

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                StringExpression nonce = ((StringExpression) ((ListExpression) res)
                        .get( 0 ));
                ListExpression list = (ListExpression) ((ListExpression) res).get(1);
                return new AdderChallengeEvent( serial, nonce,  list);
            }
            return null;
        };
    };
    
    /**
     * 
     * @param serial
     * @param nonce
     * @param randomList
     */
    public AdderChallengeEvent(int serial, ASExpression nonce, ListExpression randomList){
    	super(serial, nonce, randomList);
    	
    	System.out.println("Allocated AdderChallengeEvent\n\t"+this);
    }
    
    /**
     * 
     * @param serial
     * @param nonce
     * @param randomList
     */
    public AdderChallengeEvent(int serial, ASExpression nonce, List<List<AdderInteger>> randomList){
    	this(serial, nonce, convertRandomList(randomList));
    }
    
    /**
     * Utility method to convert a more traditional list to an sexpression.
     * 
     * @param rList - List of lists of random values
     * @return the SExpression equivalent
     */
    private static ListExpression convertRandomList(List<List<AdderInteger>> rList){
    	List<ASExpression> lists = new ArrayList<ASExpression>();
    	for(List<AdderInteger> list : rList){
    		List<ASExpression> copy = new ArrayList<ASExpression>();
    		for(AdderInteger i : list){
    			//copy.add(StringExpression.makeString(i.toString()));
    			copy.add(i.toASE());
    		}
    		
    		lists.add(new ListExpression(copy));
    	}
    	
    	return new ListExpression(lists);
    }
    
    /**
     * 
     * @return a MatcherRule for parsing this type of event.
     */
    public static MatcherRule getMatcher(){
    	return MATCHER;
    }//getMatcher
    
    public ASExpression toSExp() {
        return new ListExpression(StringExpression
                .makeString("adder-challenge"), getNonce(), getRandom());
    }
}
