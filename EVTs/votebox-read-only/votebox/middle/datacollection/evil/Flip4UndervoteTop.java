//#ifdef EVIL
package votebox.middle.datacollection.evil;

import java.util.ArrayList;
import java.util.List;
import java.util.Observable;

import votebox.middle.Properties;
import votebox.middle.ballot.Ballot;
import votebox.middle.ballot.Card;
import votebox.middle.driver.IAdapter;

public class Flip4UndervoteTop implements EvilObserver {
	//private IAdapter _ballotAdapter = null;
	private Ballot _ballot = null;
	
	private boolean _notRun = true;
	
	public void update(Observable o, Object arg) {
		if(_notRun){
			//System.out.println("Flipping");
			List<Card> cards = _ballot.getCards();
			List<Card> first8 = new ArrayList<Card>();

			//System.out.println("Getting first 8 cards...");
			for(int i = 0; i < 8; i++)
				first8.add(cards.get(i));

			//System.out.println("Selecting 4 to flip...");
			List<Card> toFlip = new ArrayList<Card>();
			for(int i = 0; i < 4; i++){
				int p = (int)(Math.random() * first8.size());
				toFlip.add(first8.remove(p));
			}

			//System.out.println("Adding LIE property...");
			for(Card card : toFlip){
				try {
					card.getProperties().add(Properties.LIE, "non", "String");
				} catch (Exception e){
					System.out.println("Marking card dishonest failed!");
					e.printStackTrace();
				}
			}
		}

		_notRun = false;
	}

	public void setAdapter(IAdapter ballotAdapter, IAdapter viewAdapter, Ballot ballot) {
		//_ballotAdapter = ballotAdapter;
		_ballot = ballot;
	}

}
//#endif