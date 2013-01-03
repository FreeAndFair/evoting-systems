/*
 * Authors: Morten, Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

namespace DigitalVoterList.Election
{

    /// <summary>
    /// A humanbeing with a name
    /// </summary>
    public class Person
    {
        /// <summary>
        /// A human being 
        /// </summary>
        /// <param name="id">A database id. Set to 0 to create new person.</param>
        public Person(int id)
        {
            DbId = id;
            Name = "";
            Address = "";
            PlaceOfBirth = "";
        }

        /// <summary>
        /// A human being
        /// </summary>
        public Person()
            : this(0)
        {

        }

        /// <summary>
        /// The persons CPR-number
        /// </summary>
        public string Cpr { get; set; }

        /// <summary>
        /// The persons passport number
        /// </summary>
        public string PassportNumber { get; set; }

        /// <summary>
        /// The persons full name
        /// </summary>
        public string Name { get; set; }

        /// <summary>
        /// The persons address
        /// </summary>
        public string Address { get; set; }

        /// <summary>
        /// Where this person was born
        /// </summary>
        public string PlaceOfBirth { get; set; }

        /// <summary>
        /// The database id of the person
        /// </summary>
        public int DbId { get; set; }

        /// <summary>
        /// Determines whether the specified object is equal to the current object.
        /// </summary>
        /// <returns>
        /// true if the specified object is equal to the current object; otherwise, false.
        /// </returns>
        /// <param name="obj">The object to compare with the current object.</param>
        public override bool Equals(object obj)
        {
            if (ReferenceEquals(null, obj))
            {
                return false;
            }
            if (ReferenceEquals(this, obj))
            {
                return true;
            }
            if (obj.GetType() != typeof(Person))
            {
                return false;
            }
            return Equals((Person)obj);
        }

        public bool Equals(Person other)
        {
            if (ReferenceEquals(null, other))
            {
                return false;
            }
            if (ReferenceEquals(this, other))
            {
                return true;
            }
            return Equals(other.Cpr, this.Cpr) && Equals(other.PassportNumber, this.PassportNumber) && Equals(other.Name, this.Name) && Equals(other.Address, this.Address) && Equals(other.PlaceOfBirth, this.PlaceOfBirth) && other.DbId == this.DbId;
        }

        public override int GetHashCode()
        {
            unchecked
            {
                int result = (this.Cpr != null ? this.Cpr.GetHashCode() : 0);
                result = (result * 397) ^ (this.PassportNumber != null ? this.PassportNumber.GetHashCode() : 0);
                result = (result * 397) ^ (this.Name != null ? this.Name.GetHashCode() : 0);
                result = (result * 397) ^ (this.Address != null ? this.Address.GetHashCode() : 0);
                result = (result * 397) ^ (this.PlaceOfBirth != null ? this.PlaceOfBirth.GetHashCode() : 0);
                result = (result * 397) ^ this.DbId;
                return result;
            }
        }
    }
}
