/*
Prime III

URL: http://www.PrimeVotingSystem.org

Copyright (c) 2015 University of Florida

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>. 

*/


var BallotName = "NIST Standard Ballot"; 
var BallotID = "UF2015"; 
var NumberOfCandidates = 71; 
var NumberOfContests = 11; 
var NumberOfParties = 11; 

var AccessCodes = new Array();
AccessCodes[0] = "1853";
AccessCodes[1] = "1111";
AccessCodes[2] = "0000";

var ContestTypes = ["Contest", "Proposition or Amendment", "Ballot Review", "Vote By Party", "Settings"];

var Contests = new Object();
Contests[0] = new Contest("00", ContestTypes[4], 1, "Settings", "settings", "");
Contests[0].NumberOfSelectedCandidates = 1;
Contests[1] = new Contest("01", ContestTypes[3], 1, "Vote By Party", "vote by party", "");
Contests[2] = new Contest("CP", ContestTypes[0], 1, "President and Vice-President", "president and vice president", "");
Contests[3] = new Contest("US", ContestTypes[0], 1, "US Senate", "you, ess senate", "");
Contests[4] = new Contest("UR", ContestTypes[0], 1, "US Representative", "you es representative", "");
Contests[5] = new Contest("GO", ContestTypes[0], 1, "Governor", "Governor", "");
Contests[6] = new Contest("LG", ContestTypes[0], 1, "Lieutenant-Governor", "lieutenant governor", "");
Contests[7] = new Contest("CC", ContestTypes[0], 3, "County Commissioners", "county commissioners", "");
Contests[8] = new Contest("P1", ContestTypes[1], 1, "Proposition #1", "proposition one", "Retain Robert Demergue as Chief Justice of the Supreme Court?");
Contests[9] = new Contest("A1", ContestTypes[1], 1, "Amendment #1", "amendment one, ballot measure one", "Requires primary elections where voters may vote for any state or federal candidate regardless of party registration of voter or candidate. The two primary-election candidates receiving most votes for an office, whether they are candidates with no party or members of same or different party, would be listed on general election ballot. Exempts presidential nominations. Fiscal Impact: No significant net fiscal effect on state and local governments.");
Contests[10] = new Contest("10", ContestTypes[2], 0, "Review My Ballot", "review my ballot", "");

var Parties = new Object();
Parties[0] = new Party("Blue", "B");
Parties[1] = new Party("Yellow", "Y");
Parties[2] = new Party("Purple", "P");
Parties[3] = new Party("Pink", "V");
Parties[4] = new Party("Gold", "G");
Parties[5] = new Party("Gray", "R");
Parties[6] = new Party("Aqua", "A");
Parties[7] = new Party("Brown", "W");
Parties[8] = new Party("Orange", "O");
Parties[9] = new Party(WriteIn, WriteIn);
Parties[10] = new Party(PropositionOrAmendment, PropositionOrAmendment);


var Candidates = new Object();
Candidates[0] = new Candidate("10648", "Joseph Barchi and Joseph Hallaren", Parties[0], Contests[2], "none", "","697","262","");
Candidates[1] = new Candidate("169", "Adam Cramer and Greg Vuocolo", Parties[1], Contests[2], "none", "","697","339","");
Candidates[2] = new Candidate("405224", "Daniel Court and Amy Blumhardt", Parties[2], Contests[2], "none", "","697","416","");
Candidates[3] = new Candidate("3418801", "Alvin Boone and James Lian", Parties[8], Contests[2], "none", "","697","495","");
Candidates[4] = new Candidate("91125", "Austin Hildebrand-MacDougall and James Garritty", Parties[3], Contests[2], "none", "","697","572","");
Candidates[5] = new Candidate("92900", "Martin Patterson and Clay Lariviere", Parties[4], Contests[2], "none", "","1488","262","");
Candidates[6] = new Candidate("8031810176", "Elizabeth Harp and Antoine Jefferson", Parties[5], Contests[2], "none", "","1488","339","");
Candidates[7] = new Candidate("15752961", "Charles Layne and Andrew Kowalski", Parties[6], Contests[2], "none", "","1488","416","");
Candidates[8] = new Candidate("2176782336", "Marzena Pazgier and Welton Phelps", Parties[7], Contests[2], "none", "","1488","495","");
Candidates[9] = new Candidate(WriteInID, WriteIn, Parties[9], Contests[2], "none", "","1488","572","1022,583");

Candidates[10] = new Candidate("927", "Dennis Weiford", Parties[0], Contests[3], "none", "","697","803","");
Candidates[11] = new Candidate("289031", "Lloyd Garriss", Parties[1], Contests[3], "none", "","697","881","");
Candidates[12] = new Candidate("23054", "Sylvia Wentworth-Farthington", Parties[2], Contests[3], "none", "","697","958","");
Candidates[13] = new Candidate("9834496", "John Hewetson", Parties[8], Contests[3], "none", "","697","1033","");
Candidates[14] = new Candidate("577591", "Victor Martinez", Parties[3], Contests[3], "none", "","1488","803","");
Candidates[15] = new Candidate("4567019", "Heather Portier", Parties[4], Contests[3], "none", "","1488","958","");
Candidates[16] = new Candidate("13841287201", "David Platt", Parties[5], Contests[3], "none", "","1488","881","");
Candidates[17] = new Candidate(WriteInID, WriteIn, Parties[9], Contests[3], "none", "","1488","1033","1045,1029");

Candidates[18] = new Candidate("164", "Brad Plunkard", Parties[0], Contests[4], "none", "","697","1231","");
Candidates[19] = new Candidate("3905", "Bruce Reeder", Parties[1], Contests[4], "none", "","697","1308","");
Candidates[20] = new Candidate("777600000", "Brad Schott", Parties[2], Contests[4], "none", "","697","1385","");
Candidates[21] = new Candidate("94931877133", "Glen Tawney", Parties[8], Contests[4], "none", "","1488","1231","");
Candidates[22] = new Candidate("70168848", "Carroll Forrest", Parties[3], Contests[4], "none", "","1488","1308","");
Candidates[23] = new Candidate(WriteInID, WriteIn, Parties[9], Contests[4], "none", "","1488","1385","1062,1368");

Candidates[24] = new Candidate("823", "Charlene Franz", Parties[0], Contests[5], "emoji1.jpg", "","697","1537","");
Candidates[25] = new Candidate("9145", "Gerard Harris", Parties[1], Contests[5], "emoji2.jpg", "","697","1613","");
Candidates[26] = new Candidate("916132832", "Linda Bargmann", Parties[2], Contests[5], "emoji3.jpg", "","697","1690","");
Candidates[27] = new Candidate("816720", "Barbara Adcock", Parties[8], Contests[5], "emoji4.jpg", "","697","1771","");
Candidates[28] = new Candidate("1073741824", "Carrie Steel-Loy", Parties[3], Contests[5], "emoji5.jpg", "","697","1846","");
Candidates[29] = new Candidate("1522435234375", "Frederick Sharp", Parties[4], Contests[5], "emoji6.jpg", "","1488","1537","");
Candidates[30] = new Candidate("16777216", "Alex Wallace", Parties[5], Contests[5], "emoji7.jpg", "","1488","1613","");
Candidates[31] = new Candidate("262144000000", "Barbara Williams", Parties[6], Contests[5], "emoji8.jpg", "","1488","1771","");
Candidates[32] = new Candidate("31640625", "Althea Sharp", Parties[7], Contests[5], "emoji9.jpg", "","1488","1690","");
Candidates[33] = new Candidate(WriteInID, WriteIn, Parties[9], Contests[5], "none", "","1488","1846","1019,1854");

Candidates[34] = new Candidate("2742241", "Chris Norberg ", Parties[0], Contests[6], "none", "","500","187","");
Candidates[35] = new Candidate("625", "Anthony Parks", Parties[1], Contests[6], "none", "","500","266","");
Candidates[36] = new Candidate("91125", "Luis Garcia", Parties[2], Contests[6], "none", "","500","345","");
Candidates[37] = new Candidate("17565568854912", "Charles Qualey", Parties[8], Contests[6], "none", "","500","424","");
Candidates[38] = new Candidate("4298", "George Hovis", Parties[3], Contests[6], "none", "","500","499","");
Candidates[39] = new Candidate("902618", "Burt Zirkle", Parties[4], Contests[6], "none", "","1293","187","");
Candidates[40] = new Candidate("2535525376", "Brenda Davis", Parties[5], Contests[6], "none", "","1293","266","");
Candidates[41] = new Candidate("96059601", "Edward Freeman", Parties[6], Contests[6], "none", "","1293","345","");
Candidates[42] = new Candidate("68719476736", "Paul Swan", Parties[7], Contests[6], "none", "","1293","424","");
Candidates[43] = new Candidate(WriteInID, WriteIn, Parties[9], Contests[6], "none", "","1293","499","823,488");

Candidates[44] = new Candidate("287", "Camille Argent", Parties[0], Contests[7], "none", "","500","696","");
Candidates[45] = new Candidate("8530162", "Chloe Witherspoon", Parties[0], Contests[7], "none", "","500","771","");
Candidates[46] = new Candidate("5320", "Clayton Bainbridge", Parties[0], Contests[7], "none", "","500","850","");
Candidates[47] = new Candidate("107918163081", "Amanda Marracini", Parties[1], Contests[7], "none", "","500","927","");
Candidates[48] = new Candidate("884736", "Charlene Hennessey", Parties[1], Contests[7], "none", "","500","1004","");
Candidates[49] = new Candidate("4717", "Eric Savoy", Parties[1], Contests[7], "none", "","500","1083","");
Candidates[50] = new Candidate("64339296875", "Sheila Moskowitz", Parties[2], Contests[7], "none", "","500","1162","");
Candidates[51] = new Candidate("593", "Mary Tawa", Parties[2], Contests[7], "none", "","500","1237","");
Candidates[52] = new Candidate("405224", "Damian Rangel", Parties[2], Contests[7], "none", "","1293","696","");
Candidates[53] = new Candidate("40867559636992", "Valarie Altman", Parties[8], Contests[7], "none", "","1293","771","");
Candidates[54] = new Candidate("2402318", "Helen Moore", Parties[8], Contests[7], "none", "","1293","850","");
Candidates[55] = new Candidate("104976", "John White", Parties[8], Contests[7], "none", "","1293","927","");
Candidates[56] = new Candidate("21332881", "Joe Lee", Parties[3], Contests[7], "none", "","1293","1004","");
Candidates[57] = new Candidate("3010936384", "Joe Barry", Parties[3], Contests[7], "none", "","1293","1083","");
Candidates[58] = new Candidate("511600", "Martin Schreiner", Parties[5], Contests[7], "none", "","1293","1162","");
Candidates[59] = new Candidate(WriteInID, WriteIn, Parties[9], Contests[7], "none", "","1293","1237","801,1235");
Candidates[60] = new Candidate(WriteInID, WriteIn, Parties[9], Contests[7], "none", "","1293","1237","801,1235");
Candidates[61] = new Candidate(WriteInID, WriteIn, Parties[9], Contests[7], "none", "","1293","1237","801,1235");


Candidates[62] = new Candidate("92900", "Yes", Parties[10], Contests[8], "none", "","500","1435","");
Candidates[63] = new Candidate("373", "No", Parties[10], Contests[8], "none", "","500","1515","");

Candidates[64] = new Candidate("3618", "Accept", Parties[10], Contests[9], "none", "","500","1823","");
Candidates[65] = new Candidate("248832", "Reject", Parties[10], Contests[9], "none", "","500","1902","");

Candidates[66] = new Candidate("Set1", "Very Fast", Parties[9], Contests[0], "none", "","","","");
Candidates[67] = new Candidate("Set2", "Fast", Parties[9], Contests[0], "none", "","","","");
Candidates[68] = new Candidate("Set3", "Average", Parties[9], Contests[0], "none", "","","","");
Candidates[68].CandidateSelected = true;
Candidates[68].WhenSelected = new Date();
Candidates[69] = new Candidate("Set4", "Slow", Parties[9], Contests[0], "none", "","","","");
Candidates[70] = new Candidate("Set5", "Very Slow", Parties[9], Contests[0], "none", "","","","");
