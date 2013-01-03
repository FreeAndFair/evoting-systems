using System;
using System.Diagnostics.Contracts;
using System.IO;
using PdfSharp;
using PdfSharp.Drawing;
using PdfSharp.Drawing.Layout;
using PdfSharp.Pdf;

namespace PDFGenerator
{

    /// <author>Kåre Sylow Pedersen (ksyl@itu.dk) edited by Nikolaj Aaes</author>
    /// <version>2011-12-12</version>
    /// <summary>
    /// This class generates voter lists.
    /// The number of rows is flexible, and the size of the font will automatically be adjusted.
    /// The list can be saved to the harddrive as a pdf file, when all the voters are added.
    /// </summary>
    public class VoterListGenerator
    {
        private const int TopMargin = 100, BottonMargin = 50, RightMargin = 50, LeftMargin = 50;
        private uint _count;
        private readonly uint _rows;
        private double _nameFieldX, _cprnrFieldX, _voternrFieldX, _rowDistance;
        private readonly string _electionName, _electionDate, _pollingTable;
        private readonly XFont _font;
        private XGraphics _gfx;
        private readonly PdfDocument _document;

        /// <summary>
        /// May I have a new voting list for this election?
        /// </summary>
        /// <param name="rows">Numbers of rows on each page</param>
        /// <param name="electionName">The name of the election</param>
        /// <param name="electionDate">The date of the election</param>
        /// <param name="pollingTable">The polling table</param>
        public VoterListGenerator(uint rows, string electionName, string electionDate, string pollingTable)
        {
            
            Contract.Requires(rows > 20);
            Contract.Requires(electionName != null);
            Contract.Requires(electionDate != null);
            Contract.Requires(pollingTable != null);

            _rows = rows;
            _electionName = electionName;
            _electionDate = electionDate;
            _pollingTable = pollingTable;
            _document = new PdfDocument();
            AddPage();
            _font = CreateFont();
        }

        /// <summary>
        /// Can you save the voting list to this location on the harddrive?
        /// </summary>
        /// <param name="voterFirstName">the first name of the voter</param>
        /// <param name="voterLastName">the last name of the voter</param>
        /// <param name="voterCPR">the CPR number of the voter</param>
        /// <param name="voterId">the voter number corresponding to the voter</param>
        public void AddVoter(string voterFirstName, string voterLastName, string voterCPR, string voterId)
        {
            Contract.Requires(voterFirstName != null);
            Contract.Requires(voterLastName != null);
            Contract.Requires(voterCPR != null);
            Contract.Requires(voterId != null);

            //Check for new page
            if (_count == _rows)
            {
                AddPage();
            }
            _count++;
            double positionY = TopMargin + (_rowDistance * _count) - 2;
            _gfx.DrawString(voterFirstName + " " + voterLastName, _font, XBrushes.Black, _nameFieldX, positionY);
            _gfx.DrawString(voterCPR, _font, XBrushes.Black, _cprnrFieldX, positionY);
            _gfx.DrawString(voterId, _font, XBrushes.Black, _voternrFieldX, positionY);
        }

        /// <summary>
        /// Can you save the voting list to this location on the harddrive?
        /// </summary>
        /// <param name="path">The location on the harddrive</param>
        public void SaveToDisk(String path)
        {
            Contract.Requires(path != null);
            Contract.Ensures(File.Exists(path));

            AddPageNumbers();
            _document.Save(path);
        }

        /// <summary>
        /// Creates a new font, where the font size is dependent of the numbers of rows on each page
        /// </summary>
        /// <returns>XFont object</returns>
        private XFont CreateFont()
        {
            int fontsize = 1;
            var font = new XFont("Arial", fontsize, XFontStyle.Regular);

            //Tests that the font size fits inside a row
            while (_gfx.MeasureString("ABC", font).Height < _rowDistance - 2 && fontsize <= 12)
            {
                font = new XFont("Arial", fontsize, XFontStyle.Regular);
                fontsize++;
            }
            return font;
        }

        /// <summary>
        /// Creates a new new page and adds it to the pdf document.
        /// </summary>
        private void AddPage()
        {
            //Releases the Xgraphics object for the previous page
            if (_gfx != null)
            {
                _gfx.Dispose();
            }
            PdfPage page = _document.AddPage();

            //Size of the page
            page.Size = PageSize.A4;

            //Sets the Xgraphics associated with the current page 
            _gfx = XGraphics.FromPdfPage(page);

            //Reset the row counter
            _count = 0;

            //Draw the template
            DrawTemplate(page);
        }

        /// <summary>
        /// Draws the template on the page
        /// </summary>
        /// <param name="page">PdfPage</param>
        private void DrawTemplate(PdfPage page)
        {
            XRect rect = DrawOuterFrame(page);
            DrawInnerFrame(rect);
            DrawColumnDescriptions(rect);
            SetDescriptionFieldsPostitions(rect);
            DrawElectionInformation();
        }

        /// <summary>
        /// Draws the outer lines on the page, and return a XRect used for the lines inside the outer frame
        /// </summary>
        /// <param name="page">PdfPage</param>
        /// <returns>XRect the size of the frame</returns>
        private XRect DrawOuterFrame(PdfPage page)
        {
            var penBold = new XPen(XColor.FromName("Black"), 1.0);
            var rect = new XRect(LeftMargin, TopMargin, page.Width - RightMargin - LeftMargin, page.Height - BottonMargin - TopMargin);
            _gfx.DrawRectangle(penBold, rect);
            return rect;
        }

        /// <summary>
        /// Draws the table lines inside the outerframe
        /// </summary>
        /// <param name="rect">XRect the size of the outer frame</param>
        private void DrawInnerFrame(XRect rect)
        {
            var penRegular = new XPen(XColor.FromName("Black"), 0.5);

            //The vertical lines
            _gfx.DrawLine(penRegular, rect.TopLeft.X + rect.Width / 2, rect.TopLeft.Y, rect.TopLeft.X + rect.Width / 2, rect.BottomLeft.Y);
            _gfx.DrawLine(penRegular, rect.TopLeft.X + rect.Width * 0.75, rect.TopLeft.Y, rect.TopLeft.X + rect.Width * 0.75, rect.BottomLeft.Y);

            //The horizontal lines
            for (double i = rect.TopLeft.Y + (rect.Height / _rows); i < rect.BottomLeft.Y; i += rect.Height / _rows)
            {
                _gfx.DrawLine(penRegular, rect.TopLeft.X, i, rect.TopRight.X, i);
            }
        }

        /// <summary>
        /// Draws the descriptions on top of each column
        /// </summary>
        /// <param name="rect">XRect the size of the outer frame</param>
        private void DrawColumnDescriptions(XRect rect)
        {
            var font = new XFont("Arial", 10, XFontStyle.Bold);
            _gfx.DrawString("Navn", font, XBrushes.Black, 160, rect.TopLeft.Y - 2);
            _gfx.DrawString("CPR nr.", font, XBrushes.Black, 340, rect.TopLeft.Y - 2);
            _gfx.DrawString("Vælgernr.", font, XBrushes.Black, 460, rect.TopLeft.Y - 2);
        }

        /// <summary>
        /// Calculate where the first row in the table is for each column
        /// </summary>
        /// <param name="rect">XRect the size of the outer frame</param>
        private void SetDescriptionFieldsPostitions(XRect rect)
        {
            _rowDistance = rect.Height / _rows;
            _nameFieldX = LeftMargin + 3;
            _cprnrFieldX = rect.TopLeft.X + rect.Width / 2 + 3;
            _voternrFieldX = rect.TopLeft.X + rect.Width * 0.75 + 3;
        }

        /// <summary>
        /// Writes the page numbers on each page in the document
        /// </summary>
        private void AddPageNumbers()
        {
            _gfx.Dispose();
            PdfPages pages = _document.Pages;
            for (int i = 0; i < _document.PageCount; i++)
            {
                int pageNumber = i + 1;
                PdfPage page = pages[i];
                String text = "Side " + pageNumber + " af " + _document.PageCount;
                XGraphics gfx = XGraphics.FromPdfPage(page);
                gfx.DrawString(text, _font, XBrushes.Black, page.Width / 2 - (gfx.MeasureString(text, _font).Width / 2), page.Height - BottonMargin / 2);
            }
        }

        /// <summary>
        /// Draws informations about the election
        /// </summary>
        private void DrawElectionInformation()
        {
            var font = new XFont("Arial", 12, XFontStyle.Bold);
            var tf = new XTextFormatter(_gfx);
            String text = _electionName + Environment.NewLine + _electionDate;
            tf.DrawString(text, font, XBrushes.Black, new XRect(LeftMargin, TopMargin / 3, 200, 50));
            tf.DrawString("Bord " + _pollingTable, font, XBrushes.Black, new XRect(_gfx.PageSize.Width / 2, TopMargin / 3, 200, 50));
        }
    }
}