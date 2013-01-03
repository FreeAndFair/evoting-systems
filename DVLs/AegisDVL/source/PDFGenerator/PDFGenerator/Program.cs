
namespace PDFGenerator
{
    class Program
    {
        static void Main()
        {

            string ElectionName = "Election 23";
            string ElectionDate = "01-01-01";
            string ElectionTime = "12:00";

            string SenderMunicipality = "Københavns Kommune";
            string SenderStreet = "Aabyvej 23";
            string SenderCity = "København Ø";

            string VoterFirstName = "Frank";
            string VoterLastName = "Hansen";
            string VoterStreet = "Poppelvej 3";
            string VoterCity = "Ganløse";

            string PollingTable = "9";
            string VoterNumber = "12345678";

            string VenueName = "Ganløse Skole";
            string VenueStreet = "Genvej 66";
            string VenueCity = "Ganløse";

            var vcg = new VoterCardGenerator(ElectionName, ElectionDate, ElectionTime);
            vcg.CreatePollingCard(SenderMunicipality,
                                  SenderStreet,
                                  SenderCity,
                                  VoterFirstName,
                                  VoterLastName,
                                  VoterStreet,
                                  VoterCity, 
                                  PollingTable,
                                  VoterNumber, 
                                  VenueName, 
                                  VenueStreet, 
                                  VenueCity);
            vcg.SaveToDisk("../VoterCard.pdf");


            uint Rows = 21;

            var vlg = new VoterListGenerator(Rows, ElectionName, ElectionDate, PollingTable);
            vlg.AddVoter(VoterFirstName, VoterLastName, "1234567890", VoterNumber);
            vlg.AddVoter(VoterFirstName, VoterLastName, "1234567890", VoterNumber);
            vlg.AddVoter(VoterFirstName, VoterLastName, "1234567890", VoterNumber);
            vlg.AddVoter(VoterFirstName, VoterLastName, "1234567890", VoterNumber);
            vlg.AddVoter(VoterFirstName, VoterLastName, "1234567890", VoterNumber);
            vlg.AddVoter(VoterFirstName, VoterLastName, "1234567890", VoterNumber);
            vlg.SaveToDisk("../voterList.pdf");
        }
    }
}
