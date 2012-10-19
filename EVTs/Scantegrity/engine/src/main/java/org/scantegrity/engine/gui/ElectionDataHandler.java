package org.scantegrity.engine.gui;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.security.*;
import java.security.spec.PKCS8EncodedKeySpec;
import java.util.Arrays;
import java.util.Vector;

import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.MessageDigest;
import javax.crypto.BadPaddingException;
import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.spec.SecretKeySpec;
import javax.xml.parsers.ParserConfigurationException;
import org.bouncycastle.jce.provider.BouncyCastleProvider;
import java.security.Security;
import org.bouncycastle.util.encoders.Base64;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import org.scantegrity.common.Util;

/*
 * ElectionDataHandler.java
 *
 * Created on October 2, 2006, 3:45 AM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */



/**
 *
 * @author rick
 */
public class ElectionDataHandler {

    static {
         Security.addProvider(new BouncyCastleProvider());
    }	
    
    /** Creates a new instance of ElectionDataHandler */
    public ElectionDataHandler(String pub, String priv, int meeting) 
        throws SecurityException, IOException, Exception
    {
        publicED = pub;
        privateED = priv;
        passHashes = new Vector<byte[]>();
        userList = new Vector<String>();
        passwordList = new Vector<String>();
        encryptedPasswords = new Vector<String>();
        passOrder = new Vector<Integer>();
        keyFactor = 0;
        privateKey = null;
        publicKey = null;
        superKey = null;

        this.meeting = meeting;
        
        
        //Sanity Check
        switch(meeting)
        {
            case 4:
                //MeetingThreeInPub.xml
                //MeetingTwoOut.xml
            case 3:
                //MeetingTwoInPub.xml
                //MeetingTwoOut.xml
            case 2:
                //Encrypted Keys File                                
                //MeetingOneOut.xml
                //Password File
                LoadPasswd(privateED + "/passwd");
            case 1:
                /* I thought this would work, but it doesn't.
                AccessController.checkPermission(
                        new FilePermission(privateED + "/-", "read,write"));
                AccessController.checkPermission(
                        new FilePermission(publicED + "/-", "read,write"));
                */

                File passwd = new File(privateED + "/passwd");
                passwd.createNewFile();
                File keys = new File(privateED + "/keystore.xml");
                keys.createNewFile();


                File MeetingOneInPre = new File(publicED + "/MeetingOneIn.xml");
                if (!MeetingOneInPre.exists()) {
                    	Meeting1InputScreen m1io=new Meeting1InputScreen(publicED + "/MeetingOneIn.xml");
                    	m1io.setVisible(true);                		
                }

                break;
            default:
                throw new Exception("Invalid Meeting Type!\n");
        }
        
    }
    
    public boolean AddUser(String username, String password)
        throws SAXException, IOException, NoSuchAlgorithmException,
            NoSuchProviderException, NoSuchPaddingException, InvalidKeyException, IllegalBlockSizeException,
            BadPaddingException
    {
        if (username != "" && password != "")
        {
            //If we have election data loaded, make sure this user exists,
            //then add him to the appropriate position in the list.
            if (meeting > 1 && meeting <= 4)
            {
                //Get the public constant from MeetingOneIn.xml        
                byte[] constant = Base64.decode("No Value");

                Document doc = Util.DomParse(publicED + "/MeetingOneIn.xml");
                Node node = doc.getElementsByTagName("constant").item(0);
                node = node.getChildNodes().item(0);
                if (node != null) constant = Base64.decode(node.getNodeValue());

                Cipher cipher = Cipher.getInstance("AES/ECB/NoPadding");
                SecretKeySpec aesKeySpec;

                aesKeySpec = new SecretKeySpec(GetHash(password, username), "AES");
                cipher.init(Cipher.DECRYPT_MODE, aesKeySpec);            

                for (int i = 0; i < encryptedPasswords.size(); i++)
                {
                    byte[] data = Base64.decode( (String) encryptedPasswords.get(i));
                    byte[] test = cipher.doFinal(data);
                    String tst = new String(Base64.encode(test));
                    String datastr = new String(Base64.encode(constant));

                    if (tst.equals(datastr))
                    {
                        userList.add(username);
                        passwordList.add(password);
                        passHashes.add(GetHash(password, username));
                        passOrder.add(i);
                        return true;
                    }
                }
            }
            else if (meeting == 1)
            {                
                userList.add(username);
                passwordList.add(password);
                passHashes.add(GetHash(password, username));   
                return true;
            }
        }
        return false;
    }
    
    public void CleanUp()
    {
        //Delete the private MeetingOneIn.xml
        new File(privateED + "MeetingOneInput.xml").delete();
    }
    
    public void ProcessKeys() throws Exception
    {
        //System.out.println("Processing Keys!");
        if (meeting == 1)
        {
            //Concatenate keys in order
            String passwds = "";
            String salt = "";
            for (int i = 0; i < passwordList.size(); i++)
            {
                passwds += passwordList.get(i);
                salt += userList.get(i);
            }
            
            /*
             * Note: Getting rid of the random salt here allows for regeneration
             * in case of catastrophic data failure.
            try {                
                //Get some salt
                SecureRandom salt = SecureRandom.getInstance("SHA256PRNG", "BC");
                
            } catch (NoSuchProviderException ex) {
                ex.printStackTrace();
            } catch (NoSuchAlgorithmException ex) {
                ex.printStackTrace();
            }
             */
            
            //Hash it up, the first 128 bits are S_1 and the second are S_2
            superKey = GetHash(passwds, salt);
            
            //Generate RSA key pair with superKey as the seed to a
            //secure PRNG

            SecureRandom rng = SecureRandom.getInstance("SHA1PRNG");
            rng.setSeed(superKey);

            KeyPairGenerator kpg = KeyPairGenerator.getInstance("RSA", "BC");
            kpg.initialize(2048, rng);

            KeyPair kp = kpg.genKeyPair();

            privateKey = kp.getPrivate();
            publicKey = kp.getPublic();

        //Save all our files

            GenerateKeyStore();
            GeneratePasswdFile();
        }
        else if (meeting > 1 && meeting <= 4)
        {   
            //System.out.println("Entering Meeting " + meeting + "!");
            //Make sure that we have enough keys to process.
            if (passHashes.size() < encryptedPasswords.size()-this.GetKeyFactor())
                throw new Exception( "Not Enough Passwords!\n");

            //Properly Order the passwords
            Vector<byte[]> newHashList = new Vector<byte[]>();
            Vector<Integer> newOrder = new Vector<Integer>();
            Vector<String> newPassList = new Vector<String>();
            Vector<String> newUserList = new Vector<String>();
            /*
            System.out.println(userList.toString());
            System.out.println(passwordList.toString());
            System.out.println(passOrder.toString());
            */
            for (int i = 0; i < encryptedPasswords.size(); i++)
            {
                for (int j = 0; j < passOrder.size(); j++)
                {
                    if ((passOrder.get(j).equals(i)))
                    {
                        newOrder.add(passOrder.get(j));
                        newPassList.add(passwordList.get(j));
                        newUserList.add(userList.get(j));
                        newHashList.add(passHashes.get(j));                        
                    }
                }
            }

            
            passwordList = newPassList;
            userList = newUserList;
            passHashes = newHashList;
            passOrder = newOrder;
            /*
            System.out.println(userList.toString());
            System.out.println(passwordList.toString());
            System.out.println(passOrder.toString());
            */
            Document doc = Util.DomParse(privateED + "/keystore.xml");
            
            //System.out.println("got passwords?");
            //Retrieve/Regenerate the superkey
            if (encryptedPasswords.size() == userList.size())
            {
                //Read Keys from XML
                byte[] testSuperKey = new byte[32];
                byte[] testPrivateKey = new byte[128];
                String threshhold = "";

                //Concatenate keys in order
                String passwds = "";
                String salt = "";
                for (int i = 0; i < passwordList.size(); i++)
                {
                    passwds += passwordList.get(i);
                    salt += userList.get(i);
                }

                //Hash it up, the first 128 bits are S_1 and the second are S_2
                superKey = GetHash(passwds, salt);
                
                Node node = doc.getElementsByTagName("keyset").item(0);
                threshhold = new String(node.getAttributes().getNamedItem("threshhold").getNodeValue());
                String test = userList.size() + "";

                if (!threshhold.equals(test))
                    throw new Exception("Can't find upper threshhold! Is it at the top of the file?\n");
                    
                NodeList children = node.getChildNodes();
                Node curr; 

                //Decrypt key
                SecretKeySpec aesKeySpec = new SecretKeySpec(superKey, "AES");
                //Our data is small and shouldn't have patterns, ECB should be fine..
                Cipher cipher = Cipher.getInstance("AES/ECB/PKCS5Padding");
                cipher.init(Cipher.DECRYPT_MODE, aesKeySpec);


                for (int i = 0; i < children.getLength(); i++)
                {
                    curr = children.item(i);
                    if (curr.getNodeName() == "s1")
                    {
                        byte[] s1 = Base64.decode(new String(curr.getChildNodes().item(0).getNodeValue()));
                        s1 = cipher.doFinal(s1);
                        System.arraycopy(s1, 0, testSuperKey, 0, 16);
                    }
                    if (curr.getNodeName() == "s2")
                    {
                        byte[] s2 = Base64.decode(new String(curr.getChildNodes().item(0).getNodeValue()));
                        s2 = cipher.doFinal(s2);
                        System.arraycopy(s2, 0, testSuperKey, 16, 16);
                    }
                    if (curr.getNodeName() == "pk")
                    {
                        testPrivateKey = cipher.doFinal(Base64.decode(new String(curr.getChildNodes().item(0).getNodeValue())));
                    }
                }                    

                //Generate RSA key pair with superKey as the seed to a
                //secure PRNG
                SecureRandom rng = SecureRandom.getInstance("SHA1PRNG");
                rng.setSeed(superKey);

                KeyPairGenerator kpg = KeyPairGenerator.getInstance("RSA", "BC");
                kpg.initialize(2048, rng);

                KeyPair kp = kpg.genKeyPair();

                privateKey = kp.getPrivate();
                publicKey = kp.getPublic();


                //System.out.println(new String(Base64.encode(testSuperKey)));
                //System.out.println(new String(Base64.encode(superKey)));
                
                //System.out.println(new String(Base64.encode(privateKey.getEncoded())));
                //System.out.println(new String(Base64.encode(testPrivateKey)));                 
                
                if (Arrays.equals(testSuperKey, superKey) 
                    && Arrays.equals(testPrivateKey, privateKey.getEncoded()))
                {
                    return;
                }
                throw new Exception("Could not retrieve superkey!");
            }
            else if (encryptedPasswords.size()-keyFactor <= userList.size())
            {
                //Retrieve Superkey w/ Subset of keys
                //Read Keys from XML
                byte[] decKey = new byte[32];
                superKey = new byte[32];

                //Concatenate keys in order
                String passwds = "";
                String salt = "";
                String searchStr = "";
                Vector<Integer> keepers = new Vector<Integer>();
                for (int i = 0; i < encryptedPasswords.size()-keyFactor; i++)
                {
                    passwds += passwordList.get(i);
                    salt += userList.get(i);
                    keepers.add(passOrder.get(i));
                    //System.out.print(keepers.get(i) + ",");
                }
                //System.out.println("\n");
                
                int j = 0;
                for (int i = 0; i < keyFactor; i++)
                {
                    for (int k = 0; k < keepers.size(); k++)
                    {
                        if (keepers.get(k) == j) j++;
                    }
                    if (i != 0) searchStr += ",";
                    searchStr += j;
                    j++;
                }
                

                //Hash it up, the first 128 bits are S_1 and the second are S_2
                decKey = GetHash(passwds, salt);

                //Decrypt key
                SecretKeySpec aesKeySpec = new SecretKeySpec(decKey, "AES");
                //Our data is small and shouldn't have patterns, ECB should be fine..
                Cipher cipher = Cipher.getInstance("AES/ECB/PKCS5Padding");
                cipher.init(Cipher.DECRYPT_MODE, aesKeySpec);
                
                //System.out.println(searchStr + "\n");
                
                
                NodeList nl = doc.getElementsByTagName("keyset");
                for (int i = 0; i < nl.getLength(); i++)
                {
                    NodeList children = nl.item(i).getChildNodes();
                    for (j = 0; j < children.getLength(); j++)
                    {
                        Node curr = children.item(j);
                        if (curr.getNodeName() == "missing")
                        {
                            String testStr = curr.getFirstChild().getNodeValue();
                            //System.out.println(testStr);
                            if (testStr.indexOf(searchStr) != -1)
                            {
                                for (int k = 0; k < children.getLength(); k++)
                                {
                                    curr = children.item(k);
                                    if (curr.getNodeName() == "s1")
                                    {
                                        byte[] s1 = Base64.decode(new String(curr.getChildNodes().item(0).getNodeValue()));
                                        s1 = cipher.doFinal(s1);
                                        System.arraycopy(s1, 0, superKey, 0, 16);
                                        //System.out.println(new String(Base64.encode(s1)));
                                    }
                                    if (curr.getNodeName() == "s2")
                                    {
                                        byte[] s2 = Base64.decode(new String(curr.getChildNodes().item(0).getNodeValue()));
                                        s2 = cipher.doFinal(s2);
                                        System.arraycopy(s2, 0, superKey, 16, 16);
                                        //System.out.println(new String(Base64.encode(s2)));
                                    }
                                    if (curr.getNodeName() == "pk")
                                    {
                                        byte[] tmpPrivateKey = new byte[128];
                                        tmpPrivateKey = cipher.doFinal(Base64.decode(new String(curr.getChildNodes().item(0).getNodeValue())));
                                        PKCS8EncodedKeySpec pks =  new PKCS8EncodedKeySpec(tmpPrivateKey);
                                        KeyFactory kf = KeyFactory.getInstance("RSA", "BC");
                                        privateKey = (PrivateKey) kf.generatePrivate(pks);
                                        //System.out.println(new String(Base64.encode(privateKey.getEncoded())));
                                    }
                                }        
                                return;
                            }
                        }
                    }
                
                }

            }
            else
            {
                System.out.println(userList.size() + " " + (encryptedPasswords.size()-keyFactor));
                System.out.println(userList.toString());
                throw new Exception("Not enough keys!");
            }
        }
    }
    
    public void SetKeyFactor(int newFactor)
    {
        this.keyFactor = newFactor;
    }

    public int GetKeyFactor() throws SAXException, IOException
    {
        if (this.meeting > 1 && this.meeting <= 4 && this.keyFactor == 0)
        {
            Document doc;

            doc = Util.DomParse(privateED + "/keystore.xml");
            NodeList keySetNodes = doc.getElementsByTagName("keyset");
            Node node=null;
            if (keySetNodes.getLength()==1)
            	node=keySetNodes.item(0);
            else
            	node=keySetNodes.item(1);
            this.keyFactor = Integer.parseInt(node.getAttributes().getNamedItem("threshhold").getNodeValue());

        }
        return this.keyFactor;
    } 
        
    public void GenerateKeyStore() 
        throws IOException, NoSuchAlgorithmException, InvalidKeyException, 
            NoSuchPaddingException, IllegalBlockSizeException, BadPaddingException,
            NoSuchProviderException
    {
        //Generate secret key encryptions file
        BufferedWriter keyFile = null;
        keyFile = new BufferedWriter(new FileWriter(privateED + "/keystore.xml"));
        keyFile.write("<xml>\n");
        //Write super encryptions

        /*
        byte[] mk1b = {-45,23,125,-90,-56,-4,0,8,9,10,11,12,13,14,15,16};
        byte[] message = "This is a Test!!".getBytes();
        SecretKeySpec mk1 = new SecretKeySpec(mk1b,"AES");
        //PKCS5Padding - For messages not mult. of block size.
        Cipher cipher = Cipher.getInstance("AES/ECB/NoPadding");
        cipher.init(Cipher.ENCRYPT_MODE,mk1);
        byte[] emk1 = cipher.doFinal(message); 
        */
        byte [] s1 = new byte[superKey.length/2];
        byte [] s2 = new byte[superKey.length/2];
        byte [] pk = privateKey.getEncoded();

        //System.out.println(System.getProperty("java.version"));
        //System.out.println(System.getProperty("java.home"));
            
        System.arraycopy(superKey, 0, s1, 0, superKey.length/2);
        System.arraycopy(superKey, superKey.length/2, s2, 0, superKey.length/2);

        SecretKeySpec aesKeySpec = new SecretKeySpec(superKey, "AES");
        //Our data is small, ECB should be fine..
        Cipher cipher = Cipher.getInstance("AES/ECB/PKCS5Padding");
        cipher.init(Cipher.ENCRYPT_MODE, aesKeySpec);

        keyFile.write("\t<keyset threshhold = \"" + passwordList.size() + "\">\n");
        keyFile.write("\t\t<s1>" + new String(Base64.encode(cipher.doFinal(s1))) + "</s1>\n");
        keyFile.write("\t\t<s2>" + new String(Base64.encode(cipher.doFinal(s2))) + "</s2>\n");
        keyFile.write("\t\t<pk>" + new String(Base64.encode(cipher.doFinal(pk))) + "</pk>\n");                
        keyFile.write("\t</keyset>\n");

        //This returns *ordered* results
        int [] counters = new int[keyFactor];
        int last = counters.length-1;
        //Init counters
        for (int i = 0; i < counters.length; i++) counters[i] = i;
        //Skip the while loop if no factor
        if (counters.length == 0)
        {
            counters = new int[1];
            counters[0] = passwordList.size();
        }

        //This is probably wildy inefficient, but it is straightforward..
        while (counters[0] <= passwordList.size()-counters.length)
        {

            String subKey = "";
            String subSalt = "";
            for (int i = 0; i < passwordList.size(); i++)
            {
                boolean exclude = false;
                for (int j = 0; j < counters.length; j++)
                {
                    if (counters[j] == i)
                    {
                        exclude = true;
                        break;
                    }
                }
                if (!exclude)
                {
                    subKey += passwordList.get(i);
                    subSalt += userList.get(i);
                }

            }

            //Generate Key and XML Data
            aesKeySpec = new SecretKeySpec(GetHash(subKey, subSalt), "AES");
            cipher.init(Cipher.ENCRYPT_MODE, aesKeySpec);

            keyFile.write("\t<keyset threshhold = \"" + keyFactor + "\">\n");
            keyFile.write("\t\t<missing>\n\t\t\t");
            for (int j = 0; j < counters.length-1; j++) keyFile.write(counters[j] + ",");
            keyFile.write(counters[counters.length-1] + "\n");
            keyFile.write("\t\t</missing>\n");
            keyFile.write("\t\t<s1>" + new String(Base64.encode(cipher.doFinal(s1))) + "</s1>\n");
            keyFile.write("\t\t<s2>" + new String(Base64.encode(cipher.doFinal(s2))) + "</s2>\n");
            keyFile.write("\t\t<pk>" + new String(Base64.encode(cipher.doFinal(pk))) + "</pk>\n");                
            keyFile.write("\t</keyset>\n");                    

            //Update Counters
            counters[last]++;
            int j = last;
            while (counters[j] >= passwordList.size()+j-last && j > 0)
            {
                counters[j] = counters[j-1]+2;
                //If we have counters below us, reset them too
                for (int i = j+1; i < counters.length; i++) 
                    counters[i] = counters[i-1]+1;
                j--;
                counters[j]++;
            }
        }

        keyFile.write("</xml>\n");

        keyFile.close();
        BufferedWriter pubFile = new BufferedWriter(new FileWriter(publicED + "/pubkey"));
        pubFile.write(new String(Base64.encode(publicKey.getEncoded())));
        pubFile.close();
    }
    
    public void GeneratePasswdFile() 
        throws IOException, NoSuchAlgorithmException, InvalidKeyException, NoSuchPaddingException, 
            IllegalBlockSizeException, BadPaddingException, SAXException
    {
        //Get the public constant from MeetingOneIn.xml        
        Document doc;
        byte[] constant = Base64.decode("No Value");
        
        doc = Util.DomParse(publicED + "/MeetingOneIn.xml");
        Node node = doc.getElementsByTagName("constant").item(0);
        node = node.getChildNodes().item(0);
        if (node != null) constant = Base64.decode(node.getNodeValue());

        Cipher cipher = Cipher.getInstance("AES/ECB/NoPadding");
        SecretKeySpec aesKeySpec;

        //Generate secret passwds file
        BufferedWriter passwdFile = null;
        passwdFile = new BufferedWriter(new FileWriter(privateED + "/passwd"));
        //Note that we store these *in order* that they were typed in
        for (int i = 0; i < passHashes.size(); i++)
        {
            byte[] sk = (byte[])passHashes.get(i);
            aesKeySpec = new SecretKeySpec(sk, "AES");
            cipher.init(Cipher.ENCRYPT_MODE, aesKeySpec);            
            passwdFile.write(new String(Base64.encode(cipher.doFinal(constant))) + "\n");
        }
        passwdFile.close();        
    }
        
    private byte[] GetHash(String data, String salt)
         throws NoSuchAlgorithmException, NoSuchProviderException
    {
        MessageDigest sha = null;
        
        sha = MessageDigest.getInstance("SHA256", "BC");
        
        sha.update(data.getBytes());
        //salt.
        sha.update(salt.getBytes());
        
        return sha.digest();
    }
    
    public void SetUserPassList(Vector<String> users, Vector<String> passwords)
    {
        this.userList = users;
        this.passwordList = passwords;
    }
    
    private void LoadPasswd(String pwdFile) throws IOException
    {
        BufferedReader passwdReader = new BufferedReader(new FileReader(pwdFile));
        String in = "";
        while (passwdReader.ready())
        {
            in = passwdReader.readLine();
            if (in != "") encryptedPasswords.add(in);                
        }
    }
    
    
    public static void main(String args[]) throws ParserConfigurationException, IOException, Exception {
        ElectionDataHandler test = new ElectionDataHandler("/Users/rick/testing/pub", 
                                                    "/Users/rick/testing/priv", 2);
        /*
        if (!test.AddUser("Test", "test1")) System.out.println("Adding Test Failed!");
        if (!test.AddUser("Test2", "test2")) System.out.println("Adding Test2 Failed!");
        if (!test.AddUser("Test3", "test3")) System.out.println("Adding Test3 Failed!");
        if (!test.AddUser("Test4", "test1")) System.out.println("Adding Test4 Failed!");
        if (!test.AddUser("Test5", "test2")) System.out.println("Adding Test5 Failed!");
        if (!test.AddUser("Test6", "test3")) System.out.println("Adding Test6 Failed!");
        if (!test.AddUser("Test7", "test1")) System.out.println("Adding Test7 Failed!");
        if (!test.AddUser("Test8", "test2")) System.out.println("Adding Test8 Failed!");
        if (!test.AddUser("Test9", "test3")) System.out.println("Adding Test9 Failed!");
        if (!test.AddUser("Test10", "test3")) System.out.println("Adding Test10 Failed!");
        */

        //Mixed Version
        //if (!test.AddUser("Test4", "test1")) System.out.println("Adding Test4 Failed!");
        //if (!test.AddUser("Test", "test1")) System.out.println("Adding Test Failed!");
        //if (!test.AddUser("Test2", "test2")) System.out.println("Adding Test2 Failed!");
        //if (!test.AddUser("Test7", "test1")) System.out.println("Adding Test7 Failed!");
        //if (!test.AddUser("Test5", "test2")) System.out.println("Adding Test5 Failed!");
        //if (!test.AddUser("Test6", "test3")) System.out.println("Adding Test6 Failed!");
        //if (!test.AddUser("Test8", "test2")) System.out.println("Adding Test8 Failed!");
        //if (!test.AddUser("Test3", "test3")) System.out.println("Adding Test3 Failed!");
        //if (!test.AddUser("Test10", "test3")) System.out.println("Adding Test10 Failed!");
        //if (!test.AddUser("Test9", "test3")) System.out.println("Adding Test9 Failed!");
        
        
        test.SetKeyFactor(3);
        
        test.ProcessKeys();
        test.CleanUp();
    }
    
    public String sign( String str ) 
        throws NoSuchAlgorithmException, InvalidKeyException, SignatureException, NoSuchProviderException
    {
       if ( privateKey != null )
        {
            Signature sig = Signature.getInstance( "SHA1withRSA", "BC" );

            sig.initSign( privateKey );
            sig.update( str.getBytes() );

            return new String( Base64.encode( sig.sign() ) );
        }

        return "ERROR GENERATING SIGNATURE";
    }
    
    public byte[] getSuper()
    {
        return superKey;
    }
        
    private String publicED;
    private String privateED;
    private Vector<String> userList;
    private Vector<String> passwordList;
    private Vector<String> encryptedPasswords;
    private Vector<byte[]> passHashes;
    private Vector<Integer> passOrder;
    private byte superKey[];
    private PrivateKey privateKey;
    private PublicKey publicKey;
    private int keyFactor;
    private int meeting; 

}
