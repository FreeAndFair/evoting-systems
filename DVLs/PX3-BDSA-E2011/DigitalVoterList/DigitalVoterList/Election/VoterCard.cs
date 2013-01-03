/*
 * Authors: Morten, Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System.Diagnostics.Contracts;

namespace DigitalVoterList.Election
{
    using System;

    using DigitalVoterList.Utilities;

    /// <summary>
    /// A ticket to be exchanged for a ballot, that is send out to the voter as a part of the validation process.
    /// </summary>
    public class VoterCard
    {
        private string _idKey;

        private static Random _random = new Random();

        /// <summary>
        /// The ElectionEvent that the Voter Card is attached to.
        /// </summary>
        public ElectionEvent ElectionEvent { get; set; }

        /// <summary>
        /// The citizen, who is the owner of the Voter Card.
        /// </summary>
        public Citizen Citizen { get; set; }

        /// <summary>
        /// The database id of the Voter Card.
        /// </summary>
        public int Id { get; set; }

        /// <summary>
        /// The id-key, corresponding to the barcode on the physical votercard
        /// </summary>
        public string IdKey
        {
            get
            {
                return _idKey;
            }
            set
            {
                Contract.Requires(value != null);
                _idKey = value;
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        public static string GenerateIdKey()
        {
            return RandomStringGenerator.RandomString(8);
        }


        /// <summary>
        /// This says if the Voter Card is valid or not.
        /// </summary>
        public bool Valid { get; set; }

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
            if (obj.GetType() != typeof(VoterCard))
            {
                return false;
            }
            return Equals((VoterCard)obj);
        }

        public bool Equals(VoterCard other)
        {
            if (ReferenceEquals(null, other))
            {
                return false;
            }
            if (ReferenceEquals(this, other))
            {
                return true;
            }
            return Equals(other.ElectionEvent, this.ElectionEvent) && Equals(other.Citizen, this.Citizen) && other.Id == this.Id && other.Valid.Equals(this.Valid);
        }

        public override int GetHashCode()
        {
            unchecked
            {
                int result = (this.ElectionEvent != null ? this.ElectionEvent.GetHashCode() : 0);
                result = (result * 397) ^ (this.Citizen != null ? this.Citizen.GetHashCode() : 0);
                result = (result * 397) ^ this.Id;
                result = (result * 397) ^ this.Valid.GetHashCode();
                return result;
            }
        }
    }
}
