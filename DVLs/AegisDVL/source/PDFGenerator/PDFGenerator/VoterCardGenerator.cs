using System.Diagnostics.Contracts;
using System.IO;
using PdfSharp.Drawing;
using PdfSharp.Drawing.BarCodes;
using PdfSharp.Drawing.Layout;
using PdfSharp.Pdf;

//NOTE: references to System.Drawing and PdfSharp must be added for this to work

namespace PDFGenerator
{
    /// <author>Kåre Sylow Pedersen (ksyl@itu.dk) and edited by Nikolaj Aaes</author>
    /// <version>2011-12-12</version>
    /// <summary>
    /// This class generates polling cards.
    /// The design of the polling card, is a rough copy of the official danish pollingcard for national election. 
    /// Each polling card is append as a page to a pdf document.
    /// The pdf document can be saved to a path supplied by the user of the class.
    /// </summary>
    class VoterCardGenerator
    {
        private const int Width = 210, Height = 100, RightMargin = 35, LeftMargin =35;
		private readonly PdfDocument _document;
		private readonly XForm _template;

		/// <summary>
		/// May I have a new polling cards generator for this election?
		/// </summary>
		/// <param name="electionName">The name of the election</param>
		/// <param name="electionDate">The date of the election</param>
		/// <param name="electionTime">The timespan of the election</param>
        public VoterCardGenerator(string electionName, string electionDate, string electionTime)
        {
			Contract.Requires(electionName != null);
			Contract.Requires(electionDate != null);
			Contract.Requires(electionTime != null);
			
			//Create the a new document
			_document = new PdfDocument();

			//Create a template containing the non specific voter details
			_template = new XForm(_document,XUnit.FromMillimeter(Width), XUnit.FromMillimeter(Height));
			XGraphics gfx = XGraphics.FromForm(_template);
			AddWatermark(gfx);
			DrawGraphics(gfx);
			ElectionDetails(gfx, electionName, electionDate, electionTime);
			Descriptions(gfx);
			
			//Release the XGraphics object
			gfx.Dispose();           
		}
		
        /// <summary>
        /// Create a polling card for this person
        /// </summary>
        /// <param name="senderName">the name of the sender</param>
        /// <param name="senderStreet">the street of the sender</param>
        /// <param name="senderCity">the city of the sender</param>
        /// <param name="receiverFirstName">the first name of the receiver</param>
        /// <param name="receiverLastName">the last name of the receiver</param>
        /// <param name="receiverStreet">the street of the receiver</param>
        /// <param name="receiverCity">the city of the receiver</param>
        /// <param name="pollingtable">the number of the polling table</param>
        /// <param name="voterNumber">the voter number of the receiver</param>
        /// <param name="pollingVenueName">the name of the polling venue</param>
        /// <param name="pollingVenueStreet">the street of the polling venue</param>
        /// <param name="pollingVenueCity">the city of the polling venue</param>
        public void CreatePollingCard(string senderName, 
                                      string senderStreet, 
                                      string senderCity, 
                                      string receiverFirstName, 
                                      string receiverLastName,
                                      string receiverStreet,
                                      string receiverCity,
                                      string pollingtable,
                                      string voterNumber,
                                      string pollingVenueName,  
                                      string pollingVenueStreet,
                                      string pollingVenueCity)
        {

			//Add a new page to the document
			PdfPage page = _document.AddPage();
			page.Width = XUnit.FromMillimeter(Width);
			page.Height = XUnit.FromMillimeter(Height);
			XGraphics gfx = XGraphics.FromPdfPage(page);

			//Draw the template
			gfx.DrawImage(_template, 0, 0);

			//Draw the voter specific information on the polling card
            FromField(gfx, senderName, senderStreet, senderCity);
            ToField(gfx, receiverFirstName + " " + receiverLastName, receiverStreet, receiverCity);
            PollingTable(gfx, pollingtable);
            VotingNumber(gfx, voterNumber);
            PollingVenue(gfx, pollingVenueName, pollingVenueStreet, pollingVenueCity);

			//Release the XGraphics object
			gfx.Dispose();
		}

		
		/// <summary>
		/// //Can you save all the polling card on this location on the harddrive?
		/// </summary>
		/// <param name="path">The location on the disk</param>
		public void SaveToDisk(string path){
			Contract.Requires(path != null);
			Contract.Ensures(File.Exists(path));

			_document.Save(path);
		}

		/// <summary>
		/// Draws the Watermark
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		private static void AddWatermark(XGraphics gfx){
			gfx.RotateTransform(-40);
			var font = new XFont("Arial Rounded MT Bold", 60, XFontStyle.Regular);
			var brush = new XSolidBrush(XColor.FromArgb(70, 255, 0, 0));
			gfx.DrawString("VALGKORT", font, brush, -120, 250);
			gfx.RotateTransform(40);           
		}

		/// <summary>
		/// Draws the sender of the polling card
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		/// <param name="name">Name of the sender</param>
		/// <param name="street">Street of the sender</param>
		/// <param name="city">City of the sender</param>
		private static void FromField(XGraphics gfx, string name, string street, string city){
			var font = new XFont("Lucida Console", 8, XFontStyle.Italic);
			var tf = new XTextFormatter(gfx);
			string adress = name + System.Environment.NewLine + street + System.Environment.NewLine + city;
			tf.DrawString(adress, font, XBrushes.Black, new XRect(310, 95, 100, 50));
		}

	   /// <summary>
	   /// Draws the receiver of the polling card
	   /// </summary>
	   /// <param name="gfx">XGraphics object</param>
	   /// <param name="name">Name of the receiver</param>
	   /// <param name="street">Street of the receiver</param>
	   /// <param name="city">City of the receiver</param>
		private static void ToField(XGraphics gfx, string name, string street, string city){
			var font = new XFont("Lucida Console", 8, XFontStyle.Regular);
			var tf = new XTextFormatter(gfx);
			string adress = name + System.Environment.NewLine + street + System.Environment.NewLine + city;
			tf.DrawString(adress, font, XBrushes.Black, new XRect(310, 155, 100, 50));
		}

		/// <summary>
		/// Draws the statics descriptions of the values
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		private void Descriptions(XGraphics gfx){
			var font = new XFont("Arial", 5, XFontStyle.Regular);
			gfx.DrawString("Afstemningssted:", font, XBrushes.Black, 40, 90);
			gfx.DrawString("Valgbord:", font, XBrushes.Black, 40, 162);
			gfx.DrawString("Vælgernr.:", font, XBrushes.Black, 40, 192);
			gfx.DrawString("Afstemningstid:", font, XBrushes.Black, 40, 222);
			gfx.DrawString("Afsender:", font, XBrushes.Black, 305, 90);
			gfx.DrawString("Modtager:", font, XBrushes.Black, 305, 150);
		}

		/// <summary>
		/// Draws the main election details
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		/// <param name="electionName">The name of the election</param>
		/// <param name="electionDate">What date it is</param>
		/// <param name="electionTime">The timespan of the election</param>
		private static void ElectionDetails(XGraphics gfx, string electionName, string electionDate, string electionTime){
			var font = new XFont("Arial", 12, XFontStyle.Bold);
			gfx.DrawString(electionName, font, XBrushes.Black, 35, 40);
			gfx.DrawString(electionDate, font, XBrushes.Black, 35, 55);

			ElectionTime(gfx, electionTime);

			var font2 = new XFont("Arial", 8, XFontStyle.BoldItalic);
			gfx.DrawString("Medbring kortet ved afstemningen", font2, XBrushes.Black, 35, 75);
			
		}

		/// <summary>
		/// Draws the address of the polling venue
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		/// <param name="name">The name of the polling venue</param>
		/// <param name="street">The street of the polling venue</param>
		/// <param name="city">The city of the polling venue</param>
		private static void PollingVenue(XGraphics gfx, string name, string street, string city){
			var font = new XFont("Arial", 9, XFontStyle.Bold);
			var tf = new XTextFormatter(gfx);
			string adress = name + System.Environment.NewLine + street + System.Environment.NewLine + city;
			tf.DrawString(adress, font, XBrushes.Black, new XRect(45, 95, 100, 50));
		}

		/// <summary>
		/// Draws the polling table
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		/// <param name="table">The polling table number</param>
		private static void PollingTable(XGraphics gfx, string table){
			var font = new XFont("Arial", 9, XFontStyle.Bold);
			gfx.DrawString(table, font, XBrushes.Black, 80, 162);
		}

		/// <summary>
		/// Draws the unique voter id
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		/// <param name="votingNumber">The unique voter id</param>
		private static void VotingNumber(XGraphics gfx, string votingNumber){
			var font = new XFont("Arial", 9, XFontStyle.Bold);
			gfx.DrawString(votingNumber, font, XBrushes.Black, 80, 192);
			Barcode(gfx, votingNumber);
		}

		/// <summary>
		/// Draws the voter id as a barcode and a human readable string
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		/// <param name="votingNumber">The unique voter id </param>
		private static void Barcode(XGraphics gfx, string votingNumber){
			//The barcode type
			BarCode barcode = new Code3of9Standard();
			barcode.Text = votingNumber;

			//Indicator to the barcode scanner where the barcode starts and ends
			barcode.StartChar = '*';
			barcode.EndChar = '*';

			//Draws the voter id as a barcode
			barcode.Size = (XSize)(new XPoint(120, 20));
			gfx.DrawBarCode(barcode, XBrushes.Black, new XPoint(310, 40));

			//Draws the voter id as a string
			var font = new XFont("Lucida Console", 7, XFontStyle.Regular);
			gfx.DrawString(votingNumber, font, XBrushes.Black, 310, 35);
		}

		/// <summary>
		/// Draws the timespan for the election
		/// </summary>
		/// <param name="gfx">xGraphics object</param>
		/// <param name="time">The timespan for the election</param>
		private static void ElectionTime(XGraphics gfx, string time){
			var font = new XFont("Arial", 9, XFontStyle.Bold);
			gfx.DrawString(time, font, XBrushes.Black, 80, 222);
		}

		/// <summary>
		/// Draws the graphical lines one the polling card
		/// </summary>
		/// <param name="gfx">XGraphics object</param>
		private static void DrawGraphics(XGraphics gfx){
			//the size and color of the lines
			var pen = new XPen(XColor.FromName("Black"), 0.5);
			
			//The rectangle around the polling venue address
			gfx.DrawRectangle(pen, LeftMargin, 80, 220, 60);

			//The rectangle around the polling table 
			gfx.DrawRectangle(pen, LeftMargin, 150, 220, 20);

			//The rectangle around the voter id
			gfx.DrawRectangle(pen, LeftMargin, 180, 220, 20);
			
			//The rectangle around the voting timespan
			gfx.DrawRectangle(pen, LeftMargin, 210, 220, 20);

			//The vertical separate line
			gfx.DrawLine(pen, 300, 20, 300, 250);

			//The horizontal separate linjes
			gfx.DrawLine(pen, LeftMargin, 250, gfx.PageSize.Width - RightMargin, 250);   
			gfx.DrawLine(pen, 300, 80, gfx.PageSize.Width - RightMargin, 80);
			gfx.DrawLine(pen, 300, 140, gfx.PageSize.Width - RightMargin, 140);

			//The crossed lines on the sender address
			gfx.DrawLine(pen, 300, 80, 450, 140);
			gfx.DrawLine(pen, 300, 140, 450, 80);
		}      

    }
}
