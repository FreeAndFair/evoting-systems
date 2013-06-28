package propmgr;

import java.io.*;
import java.net.URL;
import java.util.Properties;

public class PropertyLoader
{

    public String getFileName()
    {
        return fileName;
    }

    public void setFileName(String s)
    {
        fileName = s;
    }

    public Properties getCache()
    {
        return cache;
    }

    public void setCache(Properties properties)
    {
        cache = properties;
    }

    public PropertyLoader(String s)
    {
        fileName = s;
        System.out.println("File name in prop " + fileName);
        cache = new Properties();
        try
        {
            loadProperties();
        }
        catch(Exception exception)
        {
            exception.printStackTrace();
        }
    }

    public synchronized void loadProperties()
    {
        StringBuffer stringbuffer = new StringBuffer();
        try
        {
            URL url = new URL(fileName);
            BufferedReader bufferedreader = new BufferedReader(new InputStreamReader(url.openStream()));
            String s3;
            while((s3 = bufferedreader.readLine()) != null) 
                stringbuffer.append(s3 + "\r\n");
            bufferedreader.close();
            ByteArrayInputStream bytearrayinputstream = new ByteArrayInputStream(stringbuffer.toString().getBytes());
            cache.load(bytearrayinputstream);
            bytearrayinputstream.close();
        }
        catch(FileNotFoundException filenotfoundexception)
        {
            String s = "The following file: " + fileName + " was not found - " + filenotfoundexception.getMessage();
            System.err.println(s);
        }
        catch(IOException ioexception)
        {
            String s1 = "An IOException has occuerd while loading the following file: " + fileName + ioexception.getMessage();
            System.err.println(s1);
        }
        catch(Exception exception)
        {
            String s2 = "An Exception has occuerd while loading the following file: " + fileName + exception.getMessage();
            System.err.println(s2);
        }
    }

    public static void main(String args[])
    {
        try
        {
            PropertyLoader propertyloader = new PropertyLoader("properties/egrantsBEprocessor.properties");
            System.out.print("reading propety " + propertyloader.cache.get("filestorage.location"));
        }
        catch(Exception exception)
        {
            exception.printStackTrace();
        }
    }

    public String getRootPropDir()
    {
        return rootPropDir;
    }

    public void setRootPropDir(String s)
    {
        rootPropDir = s;
    }

    private String fileName;
    private Properties cache;
    private String rootPropDir;
}