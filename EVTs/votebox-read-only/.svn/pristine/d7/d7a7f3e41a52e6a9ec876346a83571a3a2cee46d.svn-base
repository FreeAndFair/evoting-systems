package votebox.crypto;

import java.io.File;
import java.security.SecureRandom;
import java.util.ArrayList;
import java.util.List;

import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import sexpression.ASExpression;
import sexpression.ListExpression;
import votebox.middle.Properties;
import votebox.middle.ballot.Ballot;
import votebox.middle.ballot.BallotParser;
import votebox.middle.ballot.Card;
import votebox.middle.ballot.SelectableCardElement;
import votebox.middle.driver.DeselectionException;
import votebox.middle.driver.Driver;
import votebox.middle.driver.GlobalVarsReader;
import votebox.middle.driver.IAdapter;
import votebox.middle.driver.SelectionException;
import votebox.middle.driver.UnknownUIDException;
import auditorium.Key;
import auditorium.SimpleKeyStore;
import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.PublicKey;

public class PiecemealEncrypterTest {
	class Pair{
		public Object first  = null;
		public Object second = null;

		public Pair(){}

		public Pair(Object f, Object s){
			first  = f;
			second = s;
		}
	}

	public static final String BALLOT_PATH = "votebox"+File.separatorChar+"crypto"+File.separatorChar+"interop"+File.separatorChar+"NIZK test ballot.zip";
	public static final int TRIAL_COUNT = 10;

	public static Ballot _ballot = null;

	private static File _folderPath = null;

	private static  List<byte[]> _seeds = null;
	private static  Key _publicKey = null;
	private static PublicKey _adderPublicKey = null;

	protected static void generateRandom(){
		assert _seeds == null;

		_seeds = new ArrayList<byte[]>();

		SecureRandom r = new SecureRandom();
		for(int i = 0; i < TRIAL_COUNT; i++){
			byte[] seed = new byte[128];
			r.nextBytes(seed);

			_seeds.add(seed);
		}
	}

	@BeforeClass
	public static void loadBallotBeforeTest() throws Exception{
		if(_seeds == null)
			generateRandom();

		SimpleKeyStore store = new SimpleKeyStore("keys");

		_publicKey = store.loadKey("public");
		_adderPublicKey = (PublicKey)store.loadAdderKey("public");

		File tempBallotPath = File.createTempFile("ballot", "path");
		tempBallotPath.delete();
		tempBallotPath = new File(tempBallotPath,"data");
		tempBallotPath.mkdirs();

		Driver.unzip(BALLOT_PATH, tempBallotPath.getAbsolutePath());

		_folderPath = tempBallotPath;

		BallotParser parser = new BallotParser();
		_ballot = parser.getBallot(new GlobalVarsReader(_folderPath.getAbsolutePath()).parse());
		_ballot.setViewAdapter(new IAdapter(){
			public boolean deselect(String uid) throws UnknownUIDException, DeselectionException {
				return true;
			}

			public Properties getProperties() {
				return new Properties();
			}

			public boolean select(String uid) throws UnknownUIDException, SelectionException {
				return true;
			}

		});
	}

	@AfterClass
	public static void deleteTemporaryFiles() throws Exception{
		List<File> toDelete = new ArrayList<File>();
		toDelete.add(_folderPath);

		while(toDelete.size() > 0){
			File del = toDelete.remove(0);

			if(del == null)
				continue;

			if(del.isFile()){
				if(!del.delete())
					del.deleteOnExit();
				continue;
			}//if

			File[] child = del.listFiles();

			if(child != null){
				if(child.length == 0){
					if(!del.delete())
						del.deleteOnExit();
					continue;
				}

				for(File c : child)
					toDelete.add(c);

				toDelete.add(del);
			}else{
				if(!del.delete())
					del.deleteOnExit();
				continue;
			}
		}
	}

	@Test
	public void standardTest() throws Exception{
		System.out.println("standardTest:");

		List<Card> cards = _ballot.getCards();

		for(byte[] seed : _seeds){
			System.out.println("Trail...");

			SecureRandom rand = new SecureRandom(seed);

			for(Card card : cards)
				for(SelectableCardElement elem : card.getElements())
					elem.deselect();

			for(Card card : cards){
				List<SelectableCardElement> elems = card.getElements();

				SelectableCardElement toSelect = elems.get(rand.nextInt(elems.size()));
				toSelect.select();

				PiecemealBallotEncrypter.SINGELTON.update(card.getUniqueID(), card.getCastBallot(), _publicKey);
			}

			ListExpression ballot = PiecemealBallotEncrypter.SINGELTON.getEncryptedBallot();
			ListExpression random = PiecemealBallotEncrypter.SINGELTON.getRecentRandom(); 

			PiecemealBallotEncrypter.SINGELTON.clear();

			ListExpression decrypted = BallotEncrypter.SINGLETON.decrypt(ballot, random, _publicKey);
			ListExpression expected  = _ballot.getCastBallot();

			Assert.assertEquals("Decrypted ballot same size as original", expected.size(), decrypted.size());

			for(int i = 0; i < expected.size(); i++){
				boolean found = false;

				for(int j = 0; j < decrypted.size(); j++){
					if(expected.get(i).equals(decrypted.get(j))){
						found = true;
					}
				}

				if(!found){
					System.out.println("Encrypted: "+expected);
					System.out.println("Decrypted: "+decrypted);

					Assert.fail("Could not find <"+expected.get(i)+"> in decrypted ballot.");
				}
			}
		}
	}

	@Test
	public void adderTest() throws Exception{
		System.out.println("adderTest:");
		List<Card> cards = _ballot.getCards();

		List<List<String>> raceGroups = _ballot.getRaceGroups();

		for(byte[] seed : _seeds){
			System.out.println("Trial...");
			SecureRandom rand = new SecureRandom(seed);

			for(Card card : cards){
				List<String> contained = new ArrayList<String>();

				for(SelectableCardElement elem : card.getElements())
					contained.add(elem.getUniqueID());
				
				List<String> raceGroup = null;

				for(List<String> group : raceGroups){
					boolean notIn = false;

					for(String id : contained){
						if(!group.contains(id)){
							notIn = true;
						}
					}

					if(!notIn){
						raceGroup = group;
						break;
					}
				}

				if(raceGroup == null){
					System.out.println("Groups  : "+raceGroups);
					System.out.println("Elements: "+card.getElements());
					Assert.fail("Could not determine RaceGroup for card");
				}

				List<SelectableCardElement> elems = card.getElements();

				SelectableCardElement toSelect = elems.get(rand.nextInt(elems.size()));
				toSelect.select();

				String uid = card.getUniqueID();
				List<ASExpression> castBallot = card.getCastBallot();
				
				PiecemealBallotEncrypter.SINGELTON.adderUpdate(uid, castBallot, raceGroup,  _adderPublicKey);
			}

			ListExpression ballot = PiecemealBallotEncrypter.SINGELTON.getEncryptedBallot();
			List<List<AdderInteger>> random = PiecemealBallotEncrypter.SINGELTON.getRecentAdderRandom(); 

			PiecemealBallotEncrypter.SINGELTON.clear();

			ListExpression decrypted = BallotEncrypter.SINGLETON.adderDecrypt(ballot, random);
			ListExpression expected  = _ballot.getCastBallot();

			Assert.assertEquals("Decrypted ballot same size as original", expected.size(), decrypted.size());

			for(int i = 0; i < expected.size(); i++){
				boolean found = false;

				for(int j = 0; j < decrypted.size(); j++){
					AdderInteger orig = new AdderInteger(((ListExpression)expected.get(i)).get(1).toString());
					AdderInteger newI = AdderInteger.fromASE(((ListExpression)decrypted.get(j)).get(1));

					if(orig.equals(newI)){
						found = true;
					}
				}

				if(!found){
					System.out.println("Encrypted: "+expected);
					System.out.println("Decrypted: "+decrypted);

					Assert.fail("Could not find <"+expected.get(i)+"> in decrypted ballot.");
				}
			}
		}
	}
}