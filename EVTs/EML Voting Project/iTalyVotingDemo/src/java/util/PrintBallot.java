package util;

import com.lowagie.text.*;
import com.lowagie.text.pdf.*;
import java.io.*;
import java.net.URL;
import javax.print.*;
import javax.print.attribute.HashPrintRequestAttributeSet;
import javax.print.attribute.PrintRequestAttributeSet;
import javax.print.attribute.standard.Copies;

public class PrintBallot {

	public PrintBallot() {
	}

	public void createPrintBallot(String voted1, String voted2, String voted3,
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
			PdfPTable pdfptable = new PdfPTable(8);
			pdfptable.getDefaultCell().setBorder(0);
			PdfPCell pdfpcell = new PdfPCell(new Paragraph("Senate Election"));
			pdfpcell.setBorder(0);
			pdfpcell.setColspan(8);
			pdfptable.addCell(pdfpcell);
			pdfpcell = new PdfPCell(new Paragraph(""));
			pdfpcell.setBorder(0);
			pdfpcell.setColspan(8);
			pdfptable.addCell(pdfpcell);
			Barcode128 barcode128 = new Barcode128();
			barcode128.setCodeType(1);
			barcode128.setCode(barCode);
			Image image6 = barcode128.createImageWithBarcode(pdfcontentbyte,
					null, null);
			pdfpcell = new PdfPCell(image6);
			pdfpcell.setBorder(0);
			pdfpcell.setColspan(8);
			pdfptable.addCell(pdfpcell);
			pdfpcell = new PdfPCell(new Paragraph(""));
			pdfpcell.setBorder(0);
			pdfpcell.setColspan(8);
			pdfptable.addCell(pdfpcell);
			for (int i = 1; i <= 8; i++)
				if (Integer.parseInt(voted1.substring(1, voted1.length())) == i) {
					Image image = Image.getInstance(ballotImagesFolder
							+ "Row-1-Item-" + i + "-selected.jpg");
					pdfptable.addCell(image);
				} else {
					Image image1 = Image.getInstance(ballotImagesFolder
							+ "Row-Box-Print.jpg");
					pdfptable.addCell(image1);
				}

			for (int j = 1; j <= 3; j++)
				if (Integer.parseInt(voted2.substring(1, voted2.length())) == j) {
					Image image2 = Image.getInstance(ballotImagesFolder
							+ "Row-2-Item-" + j + "-selected.jpg");
					pdfptable.addCell(image2);
				} else {
					Image image3 = Image.getInstance(ballotImagesFolder
							+ "Row-Box-Print.jpg");
					pdfptable.addCell(image3);
				}

			pdfptable.addCell("");
			pdfptable.addCell("");
			pdfptable.addCell("");
			pdfptable.addCell("");
			pdfptable.addCell("");
			for (int k = 1; k <= 7; k++)
				if (Integer.parseInt(voted3.substring(1, voted3.length())) == k) {
					Image image4 = Image.getInstance(ballotImagesFolder
							+ "Row-3-Item-" + k + "-selected.jpg");
					pdfptable.addCell(image4);
				} else {
					Image image5 = Image.getInstance(ballotImagesFolder
							+ "Row-Box-Print.jpg");
					pdfptable.addCell(image5);
				}

			pdfptable.addCell("");
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
