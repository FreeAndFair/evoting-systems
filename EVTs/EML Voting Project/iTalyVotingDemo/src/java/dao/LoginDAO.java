package dao;

import java.io.PrintStream;
import java.sql.*;

public class LoginDAO
{

    public LoginDAO()
    {
        userName = null;
        passWD = null;
        driver = "org.apache.derby.jdbc.EmbeddedDriver";
        //connectionURL = "jdbc:derby:italyVotingDB;";
        connectionURL = "jdbc:derby:/home/ovsadmin/italyVoting/derbyDB/italyVotingDB;";
        conn = null;
        query = "SELECT USERNAME,PASSWORD FROM application_access_users_t WHERE USERNAME=? AND PASSWORD=?";
    }

    public LoginDAO(String s, String s1)
    {
        userName = null;
        passWD = null;
        driver = "org.apache.derby.jdbc.EmbeddedDriver";
        connectionURL = "jdbc:derby:italyVotingDB;";
        conn = null;
        query = "SELECT USERNAME,PASSWORD FROM application_access_users_t WHERE USERNAME=? AND PASSWORD=?";
        userName = s;
        passWD = s1;
    }

    public static void main(String args[])
    {
        LoginDAO logindao = new LoginDAO();
        logindao.loginDAO("chenna", "chenna123");
    }

    public boolean loginDAO(String s, String s1)
    {
        boolean flag = false;
        try
        {
            Class.forName(driver);
            System.out.println(driver + " loaded. ");
        }
        catch(ClassNotFoundException classnotfoundexception)
        {
            System.err.print("ClassNotFoundException: ");
            System.err.println(classnotfoundexception.getMessage());
            System.out.println("\n    >>> Please check your CLASSPATH variable   <<<\n");
        }
        try
        {
            conn = DriverManager.getConnection(connectionURL);
            System.out.println("CONNECTED");
            ps = conn.prepareStatement(query);
            ps.setString(1, s);
            ps.setString(2, s1);
            rs = ps.executeQuery();
            if(rs.next())
            {
                System.out.println("DATA");
                flag = true;
                System.out.println(" u Id " + rs.getString(1) + " uname " + rs.getString(2));
            }
            rs.close();
            ps.close();
            conn.close();
            System.out.println("Closed connection");
        }
        catch(Throwable throwable)
        {
            System.out.println(" . . . exception thrown:");
            errorPrint(throwable);
        }
        System.out.println("Working With Derby JDBC program ending.");
        return flag;
    }

    static void errorPrint(Throwable throwable)
    {
        if(throwable instanceof SQLException)
        {
            SQLExceptionPrint((SQLException)throwable);
        } else
        {
            System.out.println("A non SQL error occured.");
            throwable.printStackTrace();
        }
    }

    static void SQLExceptionPrint(SQLException sqlexception)
    {
        for(; sqlexception != null; sqlexception = sqlexception.getNextException())
        {
            System.out.println("\n---SQLException Caught---\n");
            System.out.println("SQLState:   " + sqlexception.getSQLState());
            System.out.println("Severity: " + sqlexception.getErrorCode());
            System.out.println("Message:  " + sqlexception.getMessage());
            sqlexception.printStackTrace();
        }

    }

    public String getPassWD()
    {
        return passWD;
    }

    public void setPassWD(String s)
    {
        passWD = s;
    }

    public String getUserName()
    {
        return userName;
    }

    public void setUserName(String s)
    {
        userName = s;
    }

    private String userName;
    private String passWD;
    String driver;
    String connectionURL;
    Connection conn;
    PreparedStatement ps;
    ResultSet rs;
    String query;
}