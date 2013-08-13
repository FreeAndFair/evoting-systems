/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package tap;

import java.awt.Image;
import java.awt.image.RenderedImage;
import java.io.*;
import java.net.*;
import java.util.*;
import java.util.regex.*;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.nio.charset.Charset;

import javax.imageio.ImageIO;

import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.PublicKey;

import auditorium.AuditoriumCryptoException;
import auditorium.IAuditoriumParams;
import auditorium.Key;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.stream.ASEInputStreamReader;
import sexpression.stream.InvalidVerbatimStreamException;
import votebox.AuditoriumParams;
import votebox.crypto.BallotEncrypter;
import votebox.events.AdderChallengeEvent;
import votebox.events.AuthorizedToCastWithNIZKsEvent;
import votebox.events.CastCommittedBallotEvent;
import votebox.events.ChallengeEvent;
import votebox.events.CommitBallotEvent;

/**
 * Implements an example multi-threaded webserver for use in the challenge-commit model.
 * 
 * User interface is very rudimentary.
 * @author Montrose
 */
public class ChallengeWebServer {
	public static Key PUBLIC_KEY = null;
	public static PublicKey ADDER_PUBLIC_KEY = null;
	public static PublicKey ADDER_FINAL_PUBLIC_KEY = null;
	
	/**
	 * Loads the public key necissary for operation.
	 * Fails fast if key not found.
	 */
	static{
		try {
			PUBLIC_KEY = (new AuditoriumParams("webserver.conf")).getKeyStore().loadKey("public");
			ADDER_PUBLIC_KEY = (PublicKey)(new AuditoriumParams("webserver.conf")).getKeyStore().loadAdderKey("public");
		} catch (AuditoriumCryptoException e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}//static
	
	public static class SocketQueue {
		private LinkedList<Socket> m_q;
		private int m_max;
		public SocketQueue(int maxSize) {
			m_q = new LinkedList<Socket>();
			m_max = maxSize;
		}
		public SocketQueue() {
			m_q = new LinkedList<Socket>();
			m_max = 16384; // suitably enormous
		}
		public synchronized boolean enqueue(Socket sok) {
			if (m_q.size() == m_max) return false;
			m_q.add(sok);
			notify();
			return true;
		}
		public synchronized Socket dequeue() {
			try {
				while (m_q.isEmpty()) { wait(); }
			} catch (InterruptedException exc) { }
			
			Socket sok = m_q.removeFirst();
			return sok;
		}
	}

	public abstract static class Request {
		public String uri;
		public Map<String, String> headers;
		public String version; // HTTP version
		
		public abstract String getMethod();

		public Request(String _uri, Map<String, String> _headers, String _version) {
			uri = _uri; headers = _headers; version = _version;
		}
		public Request(String _uri, String _version) {
			uri = _uri; headers = new HashMap<String, String>(); version = _version;
		}

		public String getHeader(String name) {
			return (String)(headers.get(name));
		}
		public void setHeader(String name, String value) {
			headers.put(name, value);
		}
	}

	public static class GetRequest extends Request {
		public String getMethod() { return "GET"; }
		public GetRequest(String u, Map<String, String> h, String v) { super(u,h,v); }
		public GetRequest(String u, String v) { super(u, v); }
	}
	
	public static class PostRequest extends Request {
		public ByteArrayBuffer body;
		public String getMethod() { return "POST"; }
		public PostRequest(String u, Map<String, String> h, String v, ByteArrayBuffer _bodyBuf) {
			super(u,h,v);
			setBody(_bodyBuf);
		}
		public PostRequest(String u, Map<String, String> h, String v, byte[] _body) {
			super(u,h,v);
			setBody(_body);
		}
		public void setBody(byte[] _body) { body = new ByteArrayBuffer(_body); }
		public void setBody(ByteArrayBuffer _bodyBuf) { body = _bodyBuf; }
	}
	public static class PutRequest extends PostRequest {
		public String getMethod() { return "PUT"; }
		public PutRequest(String u, Map<String, String> h, String v, ByteArrayBuffer _bodyBuf) {
			super(u,h,v,_bodyBuf);
		}
		public PutRequest(String u, Map<String, String> h, String v, byte[] _body) {
			super(u,h,v,_body);
		}
	}
	
	public static abstract class Handler extends Thread {
        protected abstract void handle(Request request);
    
		protected static class WebPrintWriter extends PrintWriter {
			public WebPrintWriter(OutputStream out) { super(out); }
			public WebPrintWriter(OutputStream out,  boolean autoFlush) { super(out, autoFlush); }
			public WebPrintWriter(Writer out) { super(out); }
			public WebPrintWriter(Writer out,  boolean autoFlush) { super(out, autoFlush); }
			public void println() { print("\r\n"); }
		}
		
		protected String readLineFromStream(BufferedInputStream bis) 
			throws IOException
		{
			StringBuffer sb = new StringBuffer(128);
			
			int ch = bis.read();
			boolean stop = false;
			while(!stop) {
				switch (ch) {
					case '\r':
					case '\n':
					case -1:
						stop = true;
						break;
					default:
						sb.append((char)ch);
						ch = bis.read();
						break;
				}
			}
			// possibly eat CRLF newlines
			if (ch == '\r') {
				bis.mark(2);
				int next = bis.read();
				if (next != '\n') reset();
			}
			
			return sb.toString();
		}

		protected static final int BUFSIZ = 4096;

		protected boolean PRINT_EXCEPTIONS = true;
		
		protected Socket socket;
		protected BufferedInputStream rawInput;
		//protected BufferedReader input;
		protected OutputStream rawOutput;
		protected WebPrintWriter output;
		protected boolean headersSent;
		protected SocketQueue m_socketQueue;
		
		public Handler(SocketQueue targetQueue) {
			super("Poolboy.Handler");
			m_socketQueue = targetQueue;
        }

		protected void reset() {
        	headersSent = false;
        }
        
        public void run() {
        	for(;;) {
        		Socket sok = m_socketQueue.dequeue();
        		reset();
				try {
	        		attach(sok);
	        		processSocket();
	        	} catch (java.io.IOException exc) {
	        		System.err.println("Error: "+exc.getLocalizedMessage());
	        	}
        	}
        }

        protected void attach(Socket _socket) throws java.io.IOException {
			socket = _socket;
			rawInput = new BufferedInputStream(socket.getInputStream());
			rawOutput = socket.getOutputStream();
            output = new WebPrintWriter(
				new BufferedWriter(
                    new OutputStreamWriter(rawOutput,
						Charset.forName("UTF-8"))));
		} 
		
		protected void header(String s) {
            if (headersSent) {
                // throw
            } else {
                output.println(s);
            }
		}

		protected void endHeaders() {
			if (headersSent) {
				// throw
			} else {
				output.println();
				headersSent = true;
			}
		}
		
        protected void printHttpResponse(int code) {
            if (code == 404) {
                header("HTTP/1.1 404 Not Found");
            } else if (code == 200) {
                header("HTTP/1.1 200 OK");
            } else if (code == 301) {
                header("HTTP/1.1 301 Document Moved");
            } else if (code == 302) {
                header("HTTP/1.1 302 Document Moved");
            } else {
                header("HTTP/1.1 500 Internal Server Error");
            }
        }

		protected void redirect(String newuri, int code) {
            printHttpResponse(code);
			header("Location: " + newuri);
            header("Content-type: text/html");
            header("Connection: close");
			endHeaders();
            output.println("<h1>" + code + " Document Moved</h1>");
			output.println("The document can now be found at: <tt>" 
				+ newuri + "</tt>");
			printFooter();
		}
        
        protected void die(Exception exc) {
            try {
                printHttpResponse(500);
                header("Content-type: text/html");
				header("Connection: close");
				endHeaders();
                output.println("<h1>Proxy Error</h1>");
                output.print("<p>An exception (<i>" + exc + "</i>) was raised.</p>");
				if (PRINT_EXCEPTIONS) printException(exc);
				printFooter();
            } catch (Exception e) {
                // um, really have to bail out now
				System.out.println("Handler failed to die():");
                e.printStackTrace(System.err);
            }
        }

		protected void notFound(String uri) {
            printHttpResponse(404);
            header("Content-type: text/html");
            header("Connection: close");
			endHeaders();
            output.println("<h1>404 Not Found</h1>The URL <tt>" + uri 
                + "</tt> was not found.");
			printFooter();
		}
        
		protected void printException(Exception exc) {
			output.print("<hr style=\"display: none;\"><pre style=\"font-size: small; background-color: #eee; margin-top: 1.5em; padding: 1em; border: 1px solid #999; -moz-border-radius: 4px;\">");
			exc.printStackTrace(output);
			output.println("</pre>");
		}
		protected void printFooter() { 
			output.println("<hr style=\"display: none;\"><div style=\"font-family: sans-serif; font-size: small; background-color: #eee; margin-top: 1.5em; padding: 1em; border: 1px solid #999; -moz-border-radius: 4px;\">" + getFooterText() + "</div>");
		}
		
		protected String getFooterText() {
			return "Poolboy Java server on " 
				+ socket.getLocalAddress().toString().substring(1)
				+ " (<tt>" + getClass() + "</tt>)";
		}
	
		static Pattern kHeaderPattern = Pattern.compile("^([^:]+): (.*)$");
	
		public void processSocket() {
            try {
                String request, uri, version;
				
                request = readLineFromStream(rawInput);
                boolean isGet = request.startsWith("GET ") || request.startsWith("HEAD ");
                boolean isPost = request.startsWith("POST ") || request.startsWith("PUT ");
				if (isGet || isPost) {
					String[] requestParts = request.split(" ");
					uri = requestParts[1];
					version = requestParts[2].replaceFirst("^HTTP/","");
					Map<String, String> headers = new HashMap<String, String>();
					String headerLine = readLineFromStream(rawInput);
					while (!headerLine.equals("")) {
						Matcher m = kHeaderPattern.matcher(headerLine);
						if (m.matches()) {
							headers.put(m.group(1), m.group(2));
						}
						headerLine = readLineFromStream(rawInput);
					}
					
					ByteArrayBuffer postBuf = null;

					Request requestObj;

					if (isPost) {
						postBuf = new ByteArrayBuffer();
						byte buf[] = new byte[BUFSIZ];
						int len;
						int contentLength = -1;
						String contentLengthStr = (String) (headers.get((Object)"Content-Length"));
						if (contentLengthStr != null) {
							contentLength = new Integer(contentLengthStr).intValue();
						}
						//System.out.println("[Poolboy.run] POST/PUT content-length = " + contentLength);
						if (contentLength > 0) {
							int readLength = 0;
							while (readLength < contentLength) {
								len = rawInput.read(buf, 0, BUFSIZ);
								//System.out.println("[Poolboy.run] read "
								//	+ readLength + "/" + contentLength
								//	+ " bytes (" + len + " just now)");
								if (len >= 0) {
									postBuf.append(buf, 0, len);
								} else {
									//System.out.println("[Poolboy.run] parsing form post: Content-length was "
									//+ (String)(headers.get("Content-Length"))
									//+ " but read() returned " + len 
									//+ " before all content had been read.");

									//System.out.println("[Poolboy.run] What we got was: >>>\n" + postBuf + "\n<<<");
 									break;
								}
								readLength += len;
							}
						} else {
							while ( (len = rawInput.read(buf, 0, BUFSIZ)) >= 0 )
								postBuf.append(buf, 0, len);
						}
						if (request.startsWith("PUT "))
							requestObj = new PutRequest(uri, headers, version, postBuf);
						else
							requestObj = new PostRequest(uri, headers, version, postBuf);
					} else {
						if (request.startsWith("GET "))
							requestObj = new GetRequest(uri, headers, version);
						else
							requestObj = new GetRequest(uri, headers, version);

					}
					handle(requestObj);
                }
            } catch(Exception e) {
                die(e);
            }
			output.flush();
            output.close();
		}
	};

	public void serve(int port)
			throws java.io.IOException, java.lang.IllegalAccessException 
	{ serve(port, true, null); }
	
	public void serve(int port, boolean isPublic)
			throws java.io.IOException, java.lang.IllegalAccessException 
	{ serve(port, isPublic, null); }
	
	public void serve(int port, boolean isPublic, Access.SocketRule[] rules) 
			throws java.io.IOException, java.lang.IllegalAccessException 
	{
		ServerSocket s;
		boolean protectedAccess = false;
		if (isPublic) {
			// open server
			s = new ServerSocket(port, m_connectionBacklog);
		} else if (rules != null && rules.length > 0) {
			s = new ServerSocket(port, m_connectionBacklog);
			// only some hosts allowed to play
			protectedAccess = true;
		} else {
			// totally private
			s = new ServerSocket(port, m_connectionBacklog, 
				InetAddress.getByName("localhost"));
		}
		
		if (!protectedAccess) {
			for (;;) {
				// ServerSocket.accept() blocks
				m_connectionQueue.enqueue(s.accept()); 
			}
		} else {
			for(;;) {
				Socket incoming = s.accept();
				boolean ok = false;
				for(int i=0; i<rules.length; i++) {
					if (rules[i].permitted(incoming)) { ok = true; break; }
				}
				if (ok) {
					m_connectionQueue.enqueue(incoming);
				} else {
					System.out.println("Rejected connection from " + incoming.getInetAddress().getHostAddress());
					incoming.close();
				}
			}
		}
	}

	public abstract static class HandlerFactory {
		public abstract Handler newHandler(SocketQueue q);
	}
	
	protected int m_connectionBacklog = 64; // some web browsers make a LOT of simultaneous requests
    protected HandlerFactory m_handlerFactory;
    protected SocketQueue m_connectionQueue;
    
	public ChallengeWebServer(HandlerFactory handlerFactory) {
		m_handlerFactory = handlerFactory;
		m_connectionBacklog = 64;
		m_connectionQueue = new SocketQueue();

		for(int i=0; i<16; i++) {
			m_handlerFactory.newHandler(m_connectionQueue).start();
		}
	}
	
	public ChallengeWebServer(HandlerFactory handlerFactory, int connectionQueueSize, int threadPoolSize) {
		m_handlerFactory = handlerFactory;
		m_connectionBacklog = connectionQueueSize;
		m_connectionQueue = new SocketQueue();

		for(;threadPoolSize>0;threadPoolSize--) {
			m_handlerFactory.newHandler(m_connectionQueue).start();
		}
	}
	
	public enum MessageType{
		Commit,
		Cast,
		Challenge,
		AdderChallenge,
		Result,
		UnknownType
	};//MessageType

	@SuppressWarnings("serial")
	static class TimeStampedMap<T, U> extends HashMap<T, U>{
		private Map<T, Calendar> _timeMap = new HashMap<T, Calendar>();
		private Calendar _lastModified = null;
		
		@Override
		public U put(T key, U value){
			_lastModified = Calendar.getInstance();
			_timeMap.put(key, _lastModified);
			return super.put(key, value);
		}
		
		public Date lastModified(T key){
			return (_timeMap.get(key)).getTime();
		}//lastModified
		
		public Date lastModified(){
			return _lastModified.getTime();
		}//lastModified
	}//TimeStampedMap
	
	private static void placeInMap(int serial, ASExpression ase, Map<Integer, List<TimeStampedMap<MessageType, ASExpression>>> map){
		MessageType type = MessageType.UnknownType;
		
		if(CommitBallotEvent.getMatcher().match(-1, ase) != null){
			type = MessageType.Commit;
		}//if
		
		if(CastCommittedBallotEvent.getMatcher().match(-1, ase) != null){
			type = MessageType.Cast;
		}//if
		
		if(ChallengeEvent.getMatcher().match(-1, ase) != null){
			type = MessageType.Challenge;
		}//if
		
		if(AdderChallengeEvent.getMatcher().match(-1, ase) != null){
			type = MessageType.AdderChallenge;
		}//if
		
		if(AuthorizedToCastWithNIZKsEvent.getMatcher().match(-1, ase) != null){
			PublicKey finalPubKey = extractFinalKey((ListExpression)ase);
			
			if(ADDER_FINAL_PUBLIC_KEY != null){
				ADDER_FINAL_PUBLIC_KEY = finalPubKey;
			}else{
				if(!ADDER_FINAL_PUBLIC_KEY.equals(finalPubKey)){
					System.err.println("Final public key has CHANGED!\n"+ADDER_FINAL_PUBLIC_KEY+"\n\n"+finalPubKey);
				}
			}
			
			return;
		}
		
		System.out.println(type+" --> "+ase);
		
		List<TimeStampedMap<MessageType, ASExpression>> voteList = map.get(serial);
		
		if(voteList == null) voteList = new ArrayList<TimeStampedMap<MessageType, ASExpression>>();
		
		TimeStampedMap<MessageType, ASExpression> innerMap = null;
		
		if(voteList.size() == 0 || voteList.get(0).containsKey(MessageType.Result) || voteList.get(0).containsKey(MessageType.Cast)){
			innerMap = new TimeStampedMap<MessageType, ASExpression>();
			voteList.add(0, innerMap);
		}else
			innerMap = voteList.get(0);
		
		innerMap.put(type, ase);
		
		map.put(serial, voteList);
		
		if(type == MessageType.Challenge){
			ASExpression ballot = ((CommitBallotEvent)(CommitBallotEvent.getMatcher().match(-1, innerMap.get(MessageType.Commit)))).getBallot();
			ASExpression random = ((ChallengeEvent)ChallengeEvent.getMatcher().match(-1, innerMap.get(MessageType.Challenge))).getRandom();
			
			innerMap.put(MessageType.Result, BallotEncrypter.SINGLETON.decrypt((ListExpression)ballot, (ListExpression)random, PUBLIC_KEY));
			map.put(serial, voteList);
		}//if
		
		if(type == MessageType.AdderChallenge){
			ASExpression ballot = ((CommitBallotEvent)(CommitBallotEvent.getMatcher().match(-1, innerMap.get(MessageType.Commit)))).getBallot();
			ASExpression entry = innerMap.get(MessageType.AdderChallenge);
			
			assert entry != null;
			
			AdderChallengeEvent event = (AdderChallengeEvent)AdderChallengeEvent.getMatcher().match(-1, entry);
			
			assert event != null;
			
			ASExpression random = event.getRandom();
			
			assert random != null;
			
			innerMap.put(MessageType.Result, BallotEncrypter.SINGLETON.adderDecrypt((ListExpression)ballot, toTraditionalList((ListExpression)random)));
			map.put(serial, voteList);
		}
		
	}//placeInMap
	
	private static PublicKey extractFinalKey(ListExpression exp){
		//return PublicKey.fromString(exp.get(4).toString());
		return PublicKey.fromASE(exp.get(4));
	}
	
	private static List<List<AdderInteger>> toTraditionalList(ListExpression exp){
		List<List<AdderInteger>> toRet = new ArrayList<List<AdderInteger>>();
		
		for(int i = 0; i < exp.size(); i++){
			ListExpression sub = (ListExpression)exp.get(i);
			List<AdderInteger> subList = new ArrayList<AdderInteger>();
			for(int j = 0; j < sub.size(); j++){
				ASExpression subExp = sub.get(j);
				//subList.add(new AdderInteger(subExp.toString()));
				subList.add(AdderInteger.fromASE(subExp));
			}
			
			toRet.add(subList);
		}
		
		return toRet;
	}
	
	/**
	 * Taking in a ballot location, tries to load all relavent images into a map of race-ids to Images.
	 * 
	 * @param ballot - The ballot file to read
	 * @param languages - The list of languages in the ballot file
	 * @return a map of race-ids to images, or null if an error was encountered.
	 */
	private static Map<String, Image> loadBallotRaces(String ballot, List<String> languages) {
		try {
			Map<String, Image> racesToImageMap = new HashMap<String, Image>();
			
			ZipFile file = new ZipFile(ballot);
			
			Enumeration<? extends ZipEntry> entries = file.entries();
			
			while(entries.hasMoreElements()){
				ZipEntry entry = entries.nextElement();
				
				if(isRaceImage(entry.getName(), languages)){
					racesToImageMap.put(getRace(entry.getName()), ImageIO.read(file.getInputStream(entry)));
				}//if
			}//while
			
			return racesToImageMap;
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}
	
	/**
	 * @param entryName - the Zip entry to consider
	 * @return true if entryName is in the form "media_B*_selected_*.png", ie if it is a "race image"
	 */
	private static boolean isRaceImage(String entryName, List<String> langs){
		if(!entryName.startsWith("media/B"))
			return false;
		
		if(!entryName.endsWith(".png"))
			return false;
		
		if(entryName.indexOf("_selected_") == -1)
			return false;
		if(langs != null)
			if(entryName.indexOf(langs.get(0)) == -1) //grab the first language for now
				return false;
		
		return true;
	}//isRaceImage
	
	/**
	 * Extracts a race-id from a zip entry of a race image.
	 * 
	 * @param name - the entry of the race image.
	 * @return A string in the form B*, that is a valid race id
	 */
	private static String getRace(String name) {
		int start = name.indexOf('B');
		int end = name.indexOf('_');
		
		return name.substring(start, end);
	}
	
	public static void main(String[] args) throws Exception {
		IAuditoriumParams params = new AuditoriumParams("webserver.conf");
		final Map<Integer, List<TimeStampedMap<MessageType, ASExpression>>> _trappedMessages = new HashMap<Integer, List<TimeStampedMap<MessageType, ASExpression>>>();
		
		if(args.length < 2 || args.length > 3){
			System.out.println("Usage:\nChallengeWebServer [ballot] [port] [http port, optional]");
			System.exit(-1);
		}
		
		String ballotFile = null;
		int httpPort = -1;
		int tmpAuditoriumPort = -1;
		
		if(args.length == 3){
			try{
				ballotFile = args[0];
				tmpAuditoriumPort = Integer.parseInt(args[1]);
				httpPort = Integer.parseInt(args[2]);
			}catch(Exception e){
				System.out.println("Usage:\nChallengeWebServer [ballot] [port] [http port, optional]");
				System.exit(-1);
			}
		}else{
			int p = 0;
			ballotFile = params.getChallengeBallotFile();
			
			if(ballotFile.length() == 0){
				ballotFile = args[p];
				p++;
			}
			
			tmpAuditoriumPort = params.getChallengePort();
			
			if(tmpAuditoriumPort == -1){
				try{
					tmpAuditoriumPort = Integer.parseInt(args[p]);
					p++;
				}catch(Exception e){
					System.out.println("Usage:\nChallengeWebServer [ballot] [port] [http port, optional]\nExpected port.");
					System.exit(-1);
				}
			}
			
			httpPort = params.getHttpPort();
			
			if(args.length == 3){
				try{
					httpPort = Integer.parseInt(args[p]);
					p++;
				}catch(Exception e){
					System.out.println("Usage:\nChallengeWebServer [ballot] [port] [http port, optional]\nExpected valid http port.");
					System.exit(-1);
				}
			}
		}//if
		
		final int auditoriumPort = tmpAuditoriumPort;
		
		final List<String> languages = BallotImageHelper.getLanguages(ballotFile);
		final Map<String, Image> _raceToBallot = loadBallotRaces(ballotFile, languages);
		final Map<String, Image> _raceToTitle = BallotImageHelper.loadBallotTitles(ballotFile);
		
        System.out.println("Starting challenge trapper web-server on port " + httpPort+" watching port "+auditoriumPort);
        
        Thread trapperThread = new Thread(new Runnable(){
        	public void run(){
        		try{
        			ServerSocket socket = new ServerSocket(auditoriumPort);
        			
        			System.out.println("Listening for Trapper connection on port: "+auditoriumPort);
        			
        			Socket trapper = socket.accept();
        			
        			InputStream wrappedIn = trapper.getInputStream();
        			ASEInputStreamReader reader = new ASEInputStreamReader(wrappedIn);
        			
        			System.out.println("Starting read cycle...");
        			
        			while(true){
        				int serial = wrappedIn.read();
        				ASExpression exp = reader.read();
        				
        				placeInMap(serial, exp, _trappedMessages);
        			}//while
        			
        		}catch(IOException e){
        			e.printStackTrace();
        			System.exit(-1);
        		} catch (InvalidVerbatimStreamException e) {
					e.printStackTrace();
					System.exit(-1);
				}
        	}//run
        });
        
        trapperThread.start();
        
        class ChallengeHandler extends Handler{
        	public ChallengeHandler(SocketQueue q){super(q);}
        	
			@Override
			protected void handle(Request request) {
				if(request.uri.equals("") || request.uri.equals("/")){
					printHttpResponse(301);
                    header("Location: /index.html");
					header("Connection: close");
					endHeaders();
					return;
				}//if
				
				if(request.uri.equals("/index.html")){
					printHttpResponse(200);
					header("Content-type: text/html");
					header("Connection: close");
					endHeaders();
                    output.println("<h1>Visit /(your machine id) to verify your vote</h1>");
                    for (Integer i : _trappedMessages.keySet()){
                    	output.println("<a href=\"" + i + "\">Votebox id #" + i + "</a><BR>");
                    }//for
                    return;
				}//if
				
				if(request.uri.startsWith("/img")){
					String race = null;
					RenderedImage img = null;
					
					try {
						race = request.uri.substring(5);
						if(race.startsWith("L")){
							img = (RenderedImage)_raceToTitle.get(race.substring(2));
						}else{
							img = (RenderedImage)_raceToBallot.get(race);
						}//if
						
						if(img == null)
							throw new RuntimeException("Image Not Found");
					}catch (Exception e){
						printHttpResponse(404);
						header("Content-type: text/html");
						header("Connection: close");
						endHeaders();
						
						e.printStackTrace(output);
						return;
					}//catch
					
					try{
						printHttpResponse(200);
						header("Content-type: image/png");
						header("Connection: close");
						endHeaders();
						
						ImageIO.write(img, "png", rawOutput);
					} catch (IOException e) {
						System.err.println("Error serving image: "+e.getMessage());
					}
					
					return;
				}//if
				
				int machineId = -1;
				String[] elements = request.uri.split("/");
				String target = null;
				
				if(elements.length < 2){
					printHttpResponse(404);
					header("Content-type: text/html");
					header("Connection: close");
					endHeaders();
					output.println("Expected at least 2 elements in uri, found "+elements.length);
					return;
				}//if
				
				try{
					machineId = Integer.parseInt(elements[1]);
					
					if(elements.length == 3){
						target = elements[2];
					}
				}catch(NumberFormatException e){
					e.printStackTrace();
					printHttpResponse(404);
					header("Content-type: text/html");
					header("Connection: close");
					endHeaders();
					e.printStackTrace(output);
					
					return;
				}//catch
				
				try{
					printHttpResponse(200);
					header("Content-type: text/html");
					header("Connection: close");
					endHeaders();
					
					List<TimeStampedMap<MessageType, ASExpression>> timeline = _trappedMessages.get(machineId);
					
					//If we're just enumrating a votebox, list all communication ever, with status indicator
					if(target == null){
						output.println("<h1>Votebox #"+machineId+"</h1>");
						for(int i = 0; i < timeline.size(); i++){
							TimeStampedMap<MessageType, ASExpression> map = timeline.get(i);

							output.print("<a href=\"/"+machineId+"/"+toASCII(i)+"\">Vote at "+map.lastModified());
							if(map.containsKey(MessageType.Result)){
								output.println(" WAS CHALLENGED</a><BR>");
							}else
								if(map.containsKey(MessageType.Cast)){
									output.println(" WAS CAST</a><BR>");
								}else
									output.println(" IN PROGRESS</a><BR>");
						}//for
					}else{
						int index = fromASCII(target);
						
						TimeStampedMap<MessageType, ASExpression> map = timeline.get(index);
						
						if(map.containsKey(MessageType.Cast)){
							output.println("<h1>This Vote was counted at "+map.lastModified(MessageType.Cast)+"</h1>");
							output.println(map.get(MessageType.Commit));
						}else
							if(map.containsKey(MessageType.Result)){
								output.println("<h1>This Vote was challenged at "+map.lastModified(MessageType.Result)+"</h1>");
								
								ListExpression decryptedBallot = (ListExpression)map.get(MessageType.Result);
								
								final Map<Image, List<String>> titleToRaces = new HashMap<Image, List<String>>();
								
								for(ASExpression sexp : decryptedBallot){
									String raceId = ((ListExpression)sexp).get(0).toString();
									String value = ((ListExpression)sexp).get(1).toString();
									Image title = _raceToTitle.get(raceId);
									
									List<String> races = titleToRaces.get(title);
									
									if(races == null) races = new ArrayList<String>();
									
									if(value.equals("1"))
										races.add(raceId);
									
									titleToRaces.put(title, races);
								}//for
								
								List<Image> titleSet = new ArrayList<Image>();
								titleSet.addAll(titleToRaces.keySet());
								
								//Get the titles into ascending order before displaying them
								Collections.sort(titleSet, new Comparator<Image>(){
									public int compare(Image title1, Image title2) {
										String raceId1 = null;
										String raceId2 = null;
										
										if(titleToRaces.get(title1).size() != 0)
											raceId1 = titleToRaces.get(title1).get(0);
										else
											raceId1 = "Z98";
										
										if(titleToRaces.get(title2).size() != 0)
											raceId2 = titleToRaces.get(title2).get(0);
										else
											raceId2 = "Z99";
										
										Integer r1 = Integer.parseInt(raceId1.substring(1));
										Integer r2 = Integer.parseInt(raceId2.substring(1));
										
										return r1.compareTo(r2);
									}//compare
								});
								
								output.println("<table width=\"80%\">");
								for(Image title : titleSet){
									String keyForTitle = null;
									
									for(Map.Entry<String, Image> entry : _raceToTitle.entrySet())
										if(entry.getValue() == title){
											keyForTitle = entry.getKey();
											break;
										}
									
									output.println("<tr><td><img src=\"/img/L/"+keyForTitle+"\"></td></tr>");
									List<String> races = titleToRaces.get(title);
									
									for(String race : races)
										output.println("<tr><td><img src=\"/img/"+race+"\"></td></tr>");
								}//for
								
								output.println("</table>");
								
								/*for(ASExpression sexp : decryptedBallot){
									String raceId = ((ListExpression)sexp).get(0).toString();
									String value = ((ListExpression)sexp).get(1).toString();
									
									if(value.equals("0")) continue;
									
									output.println("<img src=\"/img/"+raceId+"\"><BR>");
								}//for*/
							}else{
								output.println("<h1>This Vote is IN PROGRESS</h1>");
								
								for(MessageType key : map.keySet()){
									output.println(key+" --> "+map.get(key)+"<BR>");
								}//for
							}//if
					}//if
				}catch(Exception e){
					e.printStackTrace();
					printHttpResponse(404);
					header("Content-type: text/html");
					header("Connection: close");
					endHeaders();
					e.printStackTrace(output);
				}//catch
			}
        	
        };
        
		new ChallengeWebServer(new HandlerFactory() {
			public Handler newHandler(SocketQueue q) {
				return new ChallengeHandler(q);
			}}).serve(httpPort);
	}
	
	private static String toASCII(int value){
    	String original = ""+value;
    	
    	String mutated = "";
    	
    	for(int i = 0; i < original.length(); i++){
    		char c = '-';
    		
    		switch(original.charAt(i)){
    		case '0': c='A'; break;
    		case '1': c='B'; break;
    		case '2': c='C'; break;
    		case '3': c='D'; break;
    		case '4': c='E'; break;
    		case '5': c='F'; break;
    		case '6': c='G'; break;
    		case '7': c='H'; break;
    		case '8': c='I'; break;
    		case '9': c='J'; break;
    		default: throw new RuntimeException("Expected value between 0 & 9, found "+ original.charAt(i));
    		}//switch
    		
    		mutated += c;
    	}//for
    	
    	return mutated;
    }//toASCII
    
    private static int fromASCII(String original){
    	String mutated = "";
    	
    	for(int i = 0; i < original.length(); i++){
    		char c = '-';
    		
    		switch(original.charAt(i)){
    		case 'A': c='0'; break;
    		case 'B': c='1'; break;
    		case 'C': c='2'; break;
    		case 'D': c='3'; break;
    		case 'E': c='4'; break;
    		case 'F': c='5'; break;
    		case 'G': c='6'; break;
    		case 'H': c='7'; break;
    		case 'I': c='8'; break;
    		case 'J': c='9'; break;
    		default: throw new RuntimeException("Expected value between 'A' & 'J', found "+ original.charAt(i));
    		}//switch
    		
    		mutated += c;
    	}//for
    	
    	return Integer.parseInt(mutated);
    }//fromASCII
}

// inspired by http://www.mcwalter.org/technology/java/httpd/tiny/index.html
