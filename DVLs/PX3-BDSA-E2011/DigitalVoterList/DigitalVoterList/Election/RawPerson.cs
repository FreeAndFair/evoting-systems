/*
 * Authors: Jens
 * Team: PX3
 * Date: 12-12-2011
 */

namespace DigitalVoterList.Election
{

    /// <summary>
    /// Raw person data
    /// </summary>
    public struct RawPerson
    {
        public string Name { get; set; }

        public string CPR { get; set; }

        public string Address { get; set; }

        public string AddressPrevious { get; set; }

        public string Birthday { get; set; }

        public string Birthplace { get; set; }

        public bool Dead { get; set; }

        public string Deathdate { get; set; }

        public int? Age { get; set; }

        public string MotherName { get; set; }

        public int? MotherAge { get; set; }

        public string MotherBirthday { get; set; }

        public string MotherEducation { get; set; }

        public bool MotherDead { get; set; }

        public string FatherName { get; set; }

        public int? FatherAge { get; set; }

        public string FatherBirthday { get; set; }

        public string FatherEducation { get; set; }

        public bool FatherDead { get; set; }

        public string Education { get; set; }

        public string Workplace { get; set; }

        public bool MilitaryServed { get; set; }

        public string DriverID { get; set; }

        public string TelephoneNumber { get; set; }

        public string PassportNumber { get; set; }

        public string City { get; set; }

        public int? Zipcode { get; set; }

        public string Nationality { get; set; }

        public bool Disempowered { get; set; }
    }
}
