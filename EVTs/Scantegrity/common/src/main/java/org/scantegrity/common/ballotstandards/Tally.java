// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   Tally.java

package org.scantegrity.common.ballotstandards;

import java.io.*;
import java.util.*;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import org.scantegrity.common.ballotstandards.basic.Answer;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.basic.Section;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.filledInBallot.FilledInBallot;
import org.scantegrity.common.ballotstandards.filledInBallot.exceptions.FBException;
import org.scantegrity.common.ballotstandards.results.Results;
import org.scantegrity.common.ballotstandards.results.exceptions.RException;
import org.w3c.dom.Document;
import org.w3c.dom.Node;

// Referenced classes of package org.scantegrity.common.ballotstandards:
//            TallyFatalException, TallyException, Constants

public class Tally
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = -1973811733536781109L;
	protected Tally()
    {
        specPath = null;
        results = null;
        electionSpecification = null;
        factory = null;
        docBuilder = null;
        sectionNamesToBeTallied = null;
        recursive = false;
        tallyOtherResults = false;
    }

    public Tally(ElectionSpecification es)
        throws TallyFatalException, Exception
    {
        specPath = null;
        results = null;
        this.electionSpecification = null;
        factory = null;
        docBuilder = null;
        sectionNamesToBeTallied = null;
        recursive = false;
        tallyOtherResults = false;
        this.electionSpecification = es;
        FileOutputStream fos = new FileOutputStream("t.tmp");
        ObjectOutputStream oos = new ObjectOutputStream(fos);
        oos.writeObject(es);
        oos.close();
        ObjectInputStream ois = new ObjectInputStream(new FileInputStream("t.tmp"));
        ElectionSpecification electionSpecification = (ElectionSpecification)ois.readObject();
        results = new Results();
        Hashtable resultsSections = electionSpecification.getSections();
        for(Enumeration e = resultsSections.elements(); e.hasMoreElements();)
        {
            Section s = (Section)e.nextElement();
            Hashtable questions = s.getQuestions();
            Enumeration eq = questions.elements();
            while(eq.hasMoreElements()) 
            {
                Question q = (Question)eq.nextElement();
                q.setTypeOfAnswer(null);
                q.setMin(-1);
                q.setMax(-1);
            }
        }

        results.setSections(electionSpecification.getSections());
        addUndervotes();
        sectionNamesToBeTallied = filter(null);
    }

    public Tally(String specPath)
        throws TallyFatalException, Exception
    {
        this.specPath = null;
        results = null;
        this.electionSpecification = null;
        factory = null;
        docBuilder = null;
        sectionNamesToBeTallied = null;
        recursive = false;
        tallyOtherResults = false;
        File f = new File(specPath);
        if(!f.exists())
            throw new TallyFatalException((new StringBuilder()).append("The specifications file |").append(specPath).append("| does not exist").toString());
        if(!f.isFile())
            throw new TallyFatalException((new StringBuilder()).append("The specifications file |").append(f.getAbsolutePath()).append("| is not a file").toString());
        if(!f.canRead())
            throw new TallyFatalException((new StringBuilder()).append("The specifications file |").append(f.getAbsolutePath()).append("| cannot be read").toString());
        this.specPath = specPath;
        factory = DocumentBuilderFactory.newInstance();
        docBuilder = factory.newDocumentBuilder();
        Document doc = docBuilder.parse(new File(specPath));
        this.electionSpecification = new ElectionSpecification(doc.getFirstChild());
        ElectionSpecification electionSpecification = new ElectionSpecification(doc.getFirstChild());
        results = new Results();
        Hashtable resultsSections = electionSpecification.getSections();
        for(Enumeration e = resultsSections.elements(); e.hasMoreElements();)
        {
            Section s = (Section)e.nextElement();
            Hashtable questions = s.getQuestions();
            Enumeration eq = questions.elements();
            while(eq.hasMoreElements()) 
            {
                Question q = (Question)eq.nextElement();
                q.setTypeOfAnswer(null);
                q.setMin(-1);
                q.setMax(-1);
            }
        }

        results.setSections(electionSpecification.getSections());
        addUndervotes();
        sectionNamesToBeTallied = filter(null);
    }

    private void setUp()
    {
        results = new Results();
        Hashtable resultsSections = electionSpecification.getSections();
        for(Enumeration e = resultsSections.elements(); e.hasMoreElements();)
        {
            Section s = (Section)e.nextElement();
            Hashtable questions = s.getQuestions();
            Enumeration eq = questions.elements();
            while(eq.hasMoreElements()) 
            {
                Question q = (Question)eq.nextElement();
                q.setTypeOfAnswer(null);
                q.setMin(-1);
                q.setMax(-1);
            }
        }

        results.setSections(electionSpecification.getSections());
        addUndervotes();
        sectionNamesToBeTallied = filter(null);
    }

    public void tally(Vector<String> sectionNames, String pathToBallots, boolean recursive)
        throws TallyFatalException
    {
        sectionNamesToBeTallied = filter(sectionNames);
        if(sectionNamesToBeTallied.size() == 0)
            return;
        this.recursive = recursive;
        File f = new File(pathToBallots);
        if(!f.exists())
            throw new TallyFatalException((new StringBuilder()).append("The path |").append(pathToBallots).append("| does not exist").toString());
        try
        {
            if(f.isDirectory())
                tallyDirectory(f);
            else
                tallyFile(f);
        }
        catch(TallyException ge)
        {
            ge.printStackTrace();
        }
    }

    public void tally(FilledInBallot fib)
        throws TallyException
    {
        Hashtable ballotSections = fib.getSections();
        for(Enumeration<String> e = sectionNamesToBeTallied.elements(); e.hasMoreElements(); tallySection((Section)ballotSections.get(e.nextElement())));
    }

    private void tallyDirectory(File dir)
        throws TallyException
    {
        if(!dir.canRead())
            throw new TallyException((new StringBuilder()).append("The ballots directory |").append(dir.getAbsolutePath()).append("| cannot be read").toString());
        String children[] = dir.list();
        for(int i = 0; i < children.length;)
        {
            File f = new File((new StringBuilder()).append(dir.getAbsolutePath()).append(System.getProperty("file.separator")).append(children[i]).toString());
            try
            {
                if(f.isFile())
                {
                    tallyFile(f);
                    continue;
                }
                if(recursive)
                    tallyDirectory(f);
                continue;
            }
            catch(TallyException ge)
            {
                System.out.println((new StringBuilder()).append("Error Tallying file |").append(f.getAbsolutePath()).append("|").toString());
                ge.printStackTrace();
                i++;
            }
        }

    }

    private void tallyFile(File f)
        throws TallyException
    {
        if(!f.canRead())
            throw new TallyException((new StringBuilder()).append("The ballots directory |").append(f.getAbsolutePath()).append("| cannot be read").toString());
        Document doc;
        try
        {
            doc = docBuilder.parse(f);
        }
        catch(Exception e)
        {
            throw new TallyException(e);
        }
        Node rootNode = doc.getFirstChild();
        String rootNodeName = rootNode.getNodeName();
        Hashtable ballotSections = null;
        try
        {
            if(rootNodeName.compareTo(Constants.TAG_FILLED_IN_BALLOT) == 0)
            {
                tallyOtherResults = false;
                FilledInBallot ballot = new FilledInBallot(rootNode);
                ballotSections = ballot.getSections();
            } else
            if(rootNodeName.compareTo(Constants.TAG_RESULTS) == 0)
            {
                tallyOtherResults = true;
                Results r = new Results(rootNode);
                ballotSections = r.getSections();
            } else
            {
                throw new TallyException((new StringBuilder()).append("Don't know how to tally elements of type |").append(rootNodeName).append("|").toString());
            }
        }
        catch(FBException fbe)
        {
            fbe.printStackTrace();
        }
        catch(RException re)
        {
            re.printStackTrace();
        }
        for(Enumeration<String> e = sectionNamesToBeTallied.elements(); e.hasMoreElements(); tallySection((Section)ballotSections.get(e.nextElement())));
    }

    private void tallySection(Section ballotSec)
        throws TallyException
    {
        if(ballotSec == null)
            return;
        Hashtable ballotQs = ballotSec.getQuestions();
        if(ballotQs == null)
            return;
        for(Enumeration e = ballotQs.keys(); e.hasMoreElements();)
            try
            {
                String ballotQId = (String)e.nextElement();
                Question resultQ = (Question)((Section)results.getSections().get(ballotSec.getId())).getQuestions().get(ballotQId);
                Question specQ = (Question)((Section)electionSpecification.getSections().get(ballotSec.getId())).getQuestions().get(ballotQId);
                if(specQ == null)
                    throw new TallyException((new StringBuilder()).append("Spoiled ballot. In the specifications file |").append(getspecPath()).append("| there is no question with ID |").append(ballotQId).append("| in section |").append(ballotSec.getId()).append("| as it appears in the ballot").toString());
                tallyQuestion((Question)ballotQs.get(ballotQId), resultQ, specQ);
            }
            catch(TallyException te)
            {
                te.printStackTrace();
            }

    }

    private void tallyQuestion(Question tallyQ, Question resultQ, Question specQ)
        throws TallyException
    {
        if(tallyQ == null)
            return;
        Hashtable tallyAs = tallyQ.getAnswers();
        Hashtable<String, Answer> resultAs = resultQ.getAnswers();
        Hashtable specAs = specQ.getAnswers();
        int nOfAs = tallyAs.size();
        if(nOfAs < specQ.getMin() && !tallyOtherResults)
        {
            Answer specUnderVote = resultAs.get(Constants.UNDERVOTE);
            specUnderVote.addPoints(1.0F);
        }
        if(nOfAs > specQ.getMax() && !tallyOtherResults)
        {
            Answer specOverVote = resultAs.get(Constants.OVERVOTE);
            specOverVote.addPoints(1.0F);
        }
        Enumeration e = tallyAs.keys();
        do
        {
            if(!e.hasMoreElements())
                break;
            String tallyAId = (String)e.nextElement();
            Answer resultA = resultAs.get(tallyAId);
            Answer specA = (Answer)specAs.get(tallyAId);
            if(specA == null && !tallyOtherResults)
                throw new TallyException((new StringBuilder()).append("Spoiled ballot. The answer with ID |").append(tallyAId).append("| from he question with ID |").append(tallyQ.getId()).append("| does non apear in the specification question").toString());
            Answer tallyA = (Answer)tallyAs.get(tallyAId);
            if(tallyAId.startsWith(Constants.WRITEIN))
            {
                String writeInText = null;
                String newId = null;
                if(tallyOtherResults)
                {
                    writeInText = tallyA.getId();
                    newId = writeInText;
                } else
                {
                    writeInText = (String)tallyA.getTexts().get(new Integer(0));
                    newId = (new StringBuilder()).append(Constants.WRITEIN).append(writeInText).toString();
                }
                Answer specAWriteIn = resultAs.get((new StringBuilder()).append(Constants.WRITEIN).append(writeInText).toString());
                if(specAWriteIn == null)
                {
                    resultA = new Answer(newId);
                    resultAs.put(resultA.getId(), resultA);
                } else
                {
                    resultA = specAWriteIn;
                }
            }
            String typeOfAnswer = specQ.getTypeOfAnswer();
            float pointsToBeAdded = 0.0F;
            if(tallyOtherResults)
                pointsToBeAdded = tallyA.getPoints();
            else
            if(typeOfAnswer.compareTo(Constants.DISTRIBUTE_POINTS) == 0)
                pointsToBeAdded = tallyA.getPoints();
            else
                pointsToBeAdded = 1.0F;
            if(typeOfAnswer.compareTo(Constants.RANK) != 0)
                resultA.addPoints(pointsToBeAdded);
        } while(true);
    }

    private Vector<String> filter(Vector<String> sections)
    {
        Vector<String> retVal = new Vector<String>();
        if(sections == null || sections.size() == 0)
        {
            for(Enumeration e = results.getSections().keys(); e.hasMoreElements(); retVal.add((String) e.nextElement()));
        } else
        {
            for(int i = 0; i < sections.size(); i++)
                if(results.getSections().get(sections.get(i)) != null)
                    retVal.add(sections.get(i));

        }
        return retVal;
    }

    private void addUndervotes()
    {
        Answer undervote = new Answer(Constants.UNDERVOTE);
        Answer overvote = new Answer(Constants.OVERVOTE);
        for(Enumeration e = results.getSections().elements(); e.hasMoreElements();)
        {
            Section s = (Section)e.nextElement();
            Enumeration f = s.getQuestions().elements();
            while(f.hasMoreElements()) 
            {
                Question q = (Question)f.nextElement();
                q.getAnswers().put(undervote.getId(), undervote);
                q.getAnswers().put(overvote.getId(), overvote);
            }
        }

    }

    public boolean isRecursive()
    {
        return recursive;
    }

    public void setRecursive(boolean recursive)
    {
        this.recursive = recursive;
    }

    public Vector<String> getSectionNamesToBeTallied()
    {
        return sectionNamesToBeTallied;
    }

    public void setSectionNamesToBeTallied(Vector<String> sectionNamesToBeTallied)
    {
        this.sectionNamesToBeTallied = sectionNamesToBeTallied;
    }

    public String getSpecPath()
    {
        return specPath;
    }

    public void setSpecPath(String specPath)
    {
        this.specPath = specPath;
    }

    public Results getResults()
    {
        return results;
    }

    public String getspecPath()
    {
        return specPath;
    }

    public ElectionSpecification getElectionSpecification()
    {
        return electionSpecification;
    }

    public static void main(String argv[])
        throws Exception
    {
        if(argv.length < 2)
        {
            System.out.println((new StringBuilder()).append("invalid number of parameters |").append(argv.length).append("|. The parameters are:").toString());
            System.out.println("path to the election specification");
            System.out.println("path to he directory containing the ballots");
            System.out.println("[name of the section to be tallyed]+");
            return;
        }
        Tally tally = new Tally(argv[0]);
        Vector<String> sectionNames = new Vector<String>();
        for(int i = 2; i < argv.length; i++)
            sectionNames.add(argv[i]);

        for(int i = 0; i < 1; i++)
        {
            System.out.println(new Date());
            tally.tally(sectionNames, argv[1], true);
            System.out.println((new StringBuilder()).append(new Date()).append("\n").toString());
        }

        System.out.println(tally.getResults());
    }

    String specPath;
    Results results;
    ElectionSpecification electionSpecification;
    private DocumentBuilderFactory factory;
    private DocumentBuilder docBuilder;
    private Vector<String> sectionNamesToBeTallied;
    private boolean recursive;
    private boolean tallyOtherResults;
}
