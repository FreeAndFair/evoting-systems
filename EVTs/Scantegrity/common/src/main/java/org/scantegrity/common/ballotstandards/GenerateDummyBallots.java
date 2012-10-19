// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   GenerateDummyBallots.java

package org.scantegrity.common.ballotstandards;

import java.io.*;
import java.util.*;
import javax.xml.parsers.*;
import org.scantegrity.common.ballotstandards.basic.Answer;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.basic.Section;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.electionSpecification.exceptions.ESException;
import org.scantegrity.common.ballotstandards.filledInBallot.FilledInBallot;
import org.w3c.dom.Document;
import org.xml.sax.SAXException;

// Referenced classes of package org.scantegrity.common.ballotstandards:
//            Constants

public class GenerateDummyBallots
{

    public GenerateDummyBallots(ElectionSpecification electionSpecification)
        throws ESException, SAXException, IOException, ParserConfigurationException
    {
        this.electionSpecification = null;
        this.electionSpecification = electionSpecification;
        eliminateWriteIns(electionSpecification);
    }

    public GenerateDummyBallots(String pathToSpec)
        throws ESException, SAXException, IOException, ParserConfigurationException
    {
        electionSpecification = null;
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = factory.newDocumentBuilder().parse(new File(pathToSpec));
        electionSpecification = new ElectionSpecification(doc.getFirstChild());
        eliminateWriteIns(electionSpecification);
    }

    public void generateBallots(int nOfBallots, String pathToBallots)
        throws Exception
    {
        if(pathToBallots != null)
        {
            File f = new File(pathToBallots);
            if(!f.exists())
                f.mkdirs();
        }
        ByteArrayOutputStream baos = writeESToBaos();
        for(int i = 0; i < nOfBallots; i++)
        {
            FilledInBallot fib = generateOneBallot(baos);
            if(pathToBallots != null)
            {
                FileOutputStream fos = new FileOutputStream((new StringBuilder()).append(pathToBallots).append(System.getProperty("file.separator")).append(i).append(".xml").toString());
                fos.write(fib.toString().getBytes());
                fos.close();
            }
        }

    }

    private ByteArrayOutputStream writeESToBaos()
    {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        try
        {
            ObjectOutputStream oos = new ObjectOutputStream(baos);
            oos.writeObject(electionSpecification);
            oos.close();
        }
        catch(Exception e)
        {
            e.printStackTrace();
        }
        return baos;
    }

    public FilledInBallot generateOneBallot()
    {
        ByteArrayOutputStream baos = writeESToBaos();
        return generateOneBallot(baos);
    }

    public FilledInBallot generateOneBallot(ByteArrayOutputStream baos)
    {
        ElectionSpecification localES = null;
        try
        {
            ObjectInputStream ois = new ObjectInputStream(new ByteArrayInputStream(baos.toByteArray()));
            localES = (ElectionSpecification)ois.readObject();
        }
        catch(Exception e)
        {
            e.printStackTrace();
        }
        Hashtable sections = localES.getSections();
        for(Enumeration s = sections.elements(); s.hasMoreElements();)
        {
            Section currentSection = (Section)s.nextElement();
            Hashtable questions = currentSection.getQuestions();
            Enumeration q = questions.elements();
            while(q.hasMoreElements()) 
            {
                Question currentQuestion = (Question)q.nextElement();
                Hashtable answers = currentQuestion.getAnswers();
                String toa = currentQuestion.getTypeOfAnswer();
                Vector answersToBeKeept = generateRandomNumbers(Math.min(currentQuestion.getMin(), answers.size()), Math.min(currentQuestion.getMax(), answers.size()), answers.size());
                if(toa.compareTo(Constants.ONE_ANSWER) == 0 || toa.compareTo(Constants.MULTIPLE_ANSWERS) == 0)
                {
                    int i = 0;
                    for(Enumeration a = answers.keys(); a.hasMoreElements();)
                    {
                        Object key = a.nextElement();
                        if(!contains(answersToBeKeept, i))
                            answers.remove(key);
                        i++;
                    }

                } else
                if(toa.compareTo(Constants.DISTRIBUTE_POINTS) == 0)
                {
                    float points[] = pointDistribution(currentQuestion.getPoints(), answersToBeKeept.size());
                    int i = 0;
                    int j = 0;
                    for(Enumeration a = answers.keys(); a.hasMoreElements();)
                    {
                        Object key = a.nextElement();
                        if(!contains(answersToBeKeept, i))
                        {
                            answers.remove(key);
                        } else
                        {
                            Answer answer = (Answer)answers.get(key);
                            answer.setPoints(points[j++]);
                        }
                        i++;
                    }

                }
                currentQuestion.setMax(-1);
                currentQuestion.setMin(-1);
                currentQuestion.setTypeOfAnswer(null);
            }
        }

        FilledInBallot fb = new FilledInBallot();
        fb.setId(localES.getId());
        fb.setSections(localES.getSections());
        return fb;
    }

    private boolean contains(Vector v, int n)
    {
        for(int i = 0; i < v.size(); i++)
            if(((Integer)v.get(i)).intValue() == n)
                return true;

        return false;
    }

    private Vector generateRandomNumbers(int min, int max, int n)
    {
        int numberOfAnswers = (int)((double)min + Math.random() * (double)((max - min) + 1));
        Vector answersToBeKeept = new Vector();
        int randomAnswerNumber = 0;
        for(int i = 0; i < numberOfAnswers; i++)
        {
            boolean duplicate = true;
            do
            {
                if(!duplicate)
                    break;
                duplicate = false;
                randomAnswerNumber = (int)(Math.random() * (double)n);
                if(contains(answersToBeKeept, randomAnswerNumber))
                    duplicate = true;
            } while(true);
            answersToBeKeept.add(new Integer(randomAnswerNumber));
        }

        return answersToBeKeept;
    }

    private float[] pointDistribution(float numberOfPoints, int numberOfCandidates)
    {
        float quota = numberOfPoints / (float)numberOfCandidates;
        float ret[] = new float[numberOfCandidates];
        float bucket = 0.0F;
        for(int i = 1; i < numberOfCandidates; i++)
        {
            float currentPoints = (int)((double)quota * Math.random());
            bucket += currentPoints;
            ret[i] = currentPoints;
        }

        ret[0] = numberOfPoints - bucket;
        return ret;
    }

    private void eliminateWriteIns(ElectionSpecification fib)
    {
        Hashtable sections = fib.getSections();
        for(Enumeration s = sections.elements(); s.hasMoreElements();)
        {
            Section currentSection = (Section)s.nextElement();
            Hashtable questions = currentSection.getQuestions();
            Enumeration q = questions.elements();
            while(q.hasMoreElements()) 
            {
                Question currentQuestion = (Question)q.nextElement();
                Hashtable answers = currentQuestion.getAnswers();
                Enumeration a = answers.keys();
                while(a.hasMoreElements()) 
                {
                    String currentAnswerId = (String)a.nextElement();
                    if(currentAnswerId.startsWith(Constants.WRITEIN))
                        answers.remove(currentAnswerId);
                }
            }
        }

    }

    public static void main(String argv[])
        throws Exception
    {
        if(argv.length < 3)
        {
            System.out.println((new StringBuilder()).append("invalid number of parameters |").append(argv.length).append("|. The parameters are:").toString());
            System.out.println("path to the election specification");
            System.out.println("number of ballots to be generated");
            System.out.println("path to where to put the ballots");
            return;
        } else
        {
            int noBallot = 1000;
            long start = System.currentTimeMillis();
            GenerateDummyBallots gdb = new GenerateDummyBallots("D:\\PunchScan2.0\\PunchScan2.0\\Elections\\POLK COUNTY, FLORIDA NOVEMBER 7, 2000\\version4\\top\\ElectionSpec.xml");
            gdb.generateBallots(noBallot, null);
            System.out.println((new StringBuilder()).append("Generating ").append(noBallot).append(" ballots took ").append((System.currentTimeMillis() - start) / 1000L).append(" seconds").toString());
            return;
        }
    }

    ElectionSpecification electionSpecification;
}
