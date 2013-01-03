/*
 * Authors: Morten, Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using System.Diagnostics.Contracts;


namespace DigitalVoterList.Election
{

    /// <summary>
    /// An actual election, that runs at a specific time, in a specific area and with a specific set of elegible voters.
    /// </summary>
    public abstract class ElectionEvent
    {
        private DateTime _date;
        private string _name;

        protected ElectionEvent(DateTime date, string name)
        {
            Contract.Requires(!date.Equals(null));
            Contract.Requires(!string.IsNullOrEmpty(name));
            _date = date;
            _name = name;
        }

        /// <summary>
        /// A getter and setter for _date. The date is the scheduled date of the ElectionEvent.
        /// </summary>
        public DateTime Date
        {
            get
            {
                return _date;
            }
            set
            {
                Contract.Ensures(!value.Equals(null));
                _date = value;
            }
        }

        /// <summary>
        /// A getter and setter for _name. The name is the name of the election.
        /// </summary>
        public string Name
        {
            get
            {
                return _name;
            }
            set
            {
                Contract.Ensures(!string.IsNullOrEmpty(value));
                _name = value;
            }
        }

        public abstract VotingVenue VotingVenueForCitizen(RawPerson rawPerson);

        public abstract bool CitizenEligibleToVote(RawPerson rawPerson);

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
            if (obj.GetType() != typeof(ElectionEvent))
            {
                return false;
            }
            return Equals((ElectionEvent)obj);
        }

        public bool Equals(ElectionEvent other)
        {
            if (ReferenceEquals(null, other))
            {
                return false;
            }
            if (ReferenceEquals(this, other))
            {
                return true;
            }
            return other._date.Equals(this._date) && Equals(other._name, this._name);
        }

        public override int GetHashCode()
        {
            unchecked
            {
                return (this._date.GetHashCode() * 397) ^ (this._name != null ? this._name.GetHashCode() : 0);
            }
        }
    }
}
