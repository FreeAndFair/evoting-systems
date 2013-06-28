package util;

import com.lowagie.text.*;
import com.lowagie.text.pdf.*;
import java.io.*;
import java.net.URL;
import java.util.HashMap;

import javax.print.*;
import javax.print.attribute.HashPrintRequestAttributeSet;
import javax.print.attribute.PrintRequestAttributeSet;
import javax.print.attribute.standard.Copies;

public class PrintBallot {

	public PrintBallot() {
	}

	public void createPrintBallot(HashMap voted,
			String barCode, String transactionID, String ballotFolder,
			String ballotImagesFolder) {
		System.out.println("Generating ballot PDF for printing....!!!");
		Document document = new Document();
		try {
			PdfWriter pdfwriter = PdfWriter.getInstance(document,
					new FileOutputStream(ballotFolder + "ballot_"
							+ transactionID + ".pdf"));
			document.open();
			com.lowagie.text.pdf.PdfContentByte pdfcontentbyte = pdfwriter
					.getDirectContent();			
			PdfPTable pdfptable = new PdfPTable(1);
			pdfptable.getDefaultCell().setBorder(0);
			PdfPCell pdfpcell = new PdfPCell(new Paragraph("Connecticut Election"));
			pdfpcell.setBorder(0);
			//pdfpcell.setColspan(8);
			pdfptable.addCell(pdfpcell);
			pdfpcell = new PdfPCell(new Paragraph(""));
			pdfpcell.setBorder(0);
			//pdfpcell.setColspan(8);
			pdfptable.addCell(pdfpcell);
			Barcode128 barcode128 = new Barcode128();
			barcode128.setCodeType(1);
			barcode128.setCode(barCode);
			Image image6 = barcode128.createImageWithBarcode(pdfcontentbyte,
					null, null);
			pdfpcell = new PdfPCell(image6);
			pdfpcell.setBorder(0);
			//pdfpcell.setColspan(8);
			pdfptable.addCell(pdfpcell);
			pdfpcell = new PdfPCell(new Paragraph(""));
			pdfpcell.setBorder(0);
			//pdfpcell.setColspan(8);
			pdfptable.addCell(pdfpcell);
			System.out.println("ballotImagesFolder "+ballotImagesFolder);
			Image image = Image.getInstance(ballotImagesFolder+ "connecticut-ballot-img.jpg");
			pdfptable.addCell(image);
			
			//pdfptable.addCell("");
			document.add(pdfptable);
		} catch (DocumentException documentexception) {
			System.err.println(documentexception.getMessage());
		} catch (IOException ioexception) {
			System.err.println(ioexception.getMessage());
		}
		document.close();
		PrintPage(document, ballotFolder, "ballot_" + transactionID + ".pdf");
	}

	public static void PrintPage(Document document, String ballotFolder,
			String transactionID) {
		System.out.println("Printing the ballot PDF....!!!" + transactionID);
		try {
			PrintService printservice = PrintServiceLookup
					.lookupDefaultPrintService();
			javax.print.DocFlavor.INPUT_STREAM input_stream = javax.print.DocFlavor.INPUT_STREAM.AUTOSENSE;
			HashPrintRequestAttributeSet hashprintrequestattributeset = new HashPrintRequestAttributeSet();
			Copies copies = new Copies(3);
			javax.print.attribute.Attribute attribute = hashprintrequestattributeset
					.get(copies.getClass());
			int i = 3;
			if (attribute != null)
				try {
					i = Integer.parseInt(attribute.toString());
				} catch (Exception exception1) {
					i = 3;
				}
			java.io.InputStream inputstream = null;
			  inputstream = ReadFile(ballotFolder + transactionID + ".pdf");          
//			try {
//				URL url = new URL("http://www.openvotingsolutions.info/iTalyVotingDemo/xml/ballots/"+ transactionID + ".pdf");
//				url.openConnection();
//				inputstream = url.openStream();
//			} catch (Exception e) {
//				e.printStackTrace();
//			}
			for (int j = 0; j < i; j++) {
				DocPrintJob docprintjob = printservice.createPrintJob();
				SimpleDoc simpledoc = new SimpleDoc(inputstream, input_stream, null);
				docprintjob.print(simpledoc, hashprintrequestattributeset);
			}

		} catch (Exception exception) {
			exception.printStackTrace();
		}
	}

	public static InputStream ReadFile(String fileLocation) throws IOException {
		StringBuffer stringbuffer = new StringBuffer();
		try {
			BufferedReader bufferedreader = new BufferedReader(new FileReader(
					fileLocation));
			String s1;
			while ((s1 = bufferedreader.readLine()) != null)
				stringbuffer.append(s1.trim());
			bufferedreader.close();
		} catch (IOException ioexception) {
		}
		ByteArrayInputStream is = new ByteArrayInputStream(stringbuffer
				.toString().getBytes("UTF-8"));
		return is;
	}
}
