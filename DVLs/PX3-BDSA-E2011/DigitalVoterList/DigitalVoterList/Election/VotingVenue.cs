/*
 * Authors: Morten, Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

namespace DigitalVoterList.Election
{
    using System.Diagnostics.Contracts;

    /// <summary>
    /// A specific venue for voting, typically a school or similair public place.
    /// </summary>
    public class VotingVenue
    {
        public VotingVenue(int dbid, string name, string address)
        {
            Contract.Requires(!string.IsNullOrEmpty(name), "Votingvenue must have a name");
            Contract.Requires(!string.IsNullOrEmpty(address), "Votingvenue must have an address");
            Address = address;
            Name = name;
            DbId = dbid;
        }

        public string Address { get; private set; }

        public string Name { get; private set; }

        public int DbId { get; private set; }

        public static bool operator ==(VotingVenue a, VotingVenue b)
        {
            var c = a ?? new VotingVenue(0, "-", "-");
            var d = b ?? new VotingVenue(0, "-", "-");
            return c.DbId == d.DbId;
        }

        public static bool operator !=(VotingVenue a, VotingVenue b)
        {
            return !(a == b);
        }

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
            if (obj.GetType() != typeof(VotingVenue))
            {
                return false;
            }
            return Equals((VotingVenue)obj);
        }

        [ContractInvariantMethod]
        private void ObjectInvariant()
        {
            Contract.Invariant(Name != null);
            Contract.Invariant(Address != null);
        }

        public bool Equals(VotingVenue other)
        {
            if (ReferenceEquals(null, other))
            {
                return false;
            }
            if (ReferenceEquals(this, other))
            {
                return true;
            }
            return Equals(other.Address, this.Address) && Equals(other.Name, this.Name) && other.DbId == this.DbId && Equals(other.Address, this.Address) && Equals(other.Name, this.Name) && other.DbId == this.DbId;
        }

        public override int GetHashCode()
        {
            unchecked
            {
                int result = (this.Address != null ? this.Address.GetHashCode() : 0);
                result = (result * 397) ^ (this.Name != null ? this.Name.GetHashCode() : 0);
                result = (result * 397) ^ this.DbId;
                result = (result * 397) ^ (this.Address != null ? this.Address.GetHashCode() : 0);
                result = (result * 397) ^ (this.Name != null ? this.Name.GetHashCode() : 0);
                result = (result * 397) ^ this.DbId;
                return result;
            }
        }
    }
}
