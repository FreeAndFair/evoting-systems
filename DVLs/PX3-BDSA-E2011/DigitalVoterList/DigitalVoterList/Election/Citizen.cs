/*
 * Authors: Morten, Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using DigitalVoterList.Utilities;

namespace DigitalVoterList.Election
{
    using System.Text.RegularExpressions;

    /// <summary>
    /// A person with a valid and unique ID-number (CPR-number)
    /// </summary>
    public class Citizen : Person
    {
        public Citizen(int id, string cpr)
            : base(id)
        {
            Contract.Requires(cpr != null);
            Contract.Requires(ValidCpr(cpr));
            Cpr = cpr;
        }

        public Citizen(int id, string cpr, bool hasVoted)
            : this(id, cpr)
        {
            Contract.Requires(cpr != null);
            Contract.Requires(ValidCpr(cpr));
            HasVoted = hasVoted;
        }

        /// <summary>
        /// Determines whether the specified object is equal to the current object.
        /// </summary>
        /// <returns>
        /// true if the specified object is equal to the current object; otherwise, false.
        /// </returns>
        /// <param name="obj">The object to compare with the current object.</param>
        public override bool Equals(Object obj)
        {
            if (ReferenceEquals(null, obj))
            {
                return false;
            }
            if (ReferenceEquals(this, obj))
            {
                return true;
            }
            return Equals(obj as Citizen);
        }

        private HashSet<VoterCard> _voterCards;

        private HashSet<Quiz> _securityQuestions;

        public bool HasVoted { get; private set; }

        public bool EligibleToVote { get; set; }

        public VotingVenue VotingPlace { get; set; }

        public HashSet<VoterCard> VoterCards
        {
            get { return _voterCards ?? new HashSet<VoterCard>(); }
            set { _voterCards = value ?? new HashSet<VoterCard>(); }
        }

        public HashSet<Quiz> SecurityQuestions
        {
            get
            {
                if (_securityQuestions == null)
                {
                    _securityQuestions = new HashSet<Quiz>();
                }
                return _securityQuestions;
            }
            set { _securityQuestions = value ?? new HashSet<Quiz>(); }
        }


        public void SetHasVoted()
        {
            Contract.Requires(DAOFactory.Ready);
            IDataAccessObject dao = DAOFactory.CurrentUserDAO;
            dao.SetHasVoted(this);
            HasVoted = true;
        }

        [ContractInvariantMethod]
        [System.Diagnostics.CodeAnalysis.SuppressMessage("Microsoft.Performance", "CA1822:MarkMembersAsStatic", Justification = "Required for code contracts.")]
        private void ObjectInvariant()
        {
            Contract.Invariant(ValidCpr(Cpr));
        }

        public static bool ValidCpr(string cpr)
        {
            Contract.Requires(cpr != null);
            if (Regex.IsMatch(cpr, @"^\d{10}$"))
            {
                int day;
                if (!Int32.TryParse(cpr.Substring(0, 2), out day)) return false;
                int month;
                if (!Int32.TryParse(cpr.Substring(2, 2), out month)) return false;
                if (!(day > 0 && day <= 31)) return false;
                if (!(month > 0 && month <= 12)) return false;

                return true;
            }
            return false;
        }

        public bool Equals(Citizen other)
        {
            if (ReferenceEquals(null, other))
            {
                return false;
            }
            if (ReferenceEquals(this, other))
            {
                return true;
            }


            var i1 = base.Equals(other);
            var i2 = Equals(other._voterCards, this._voterCards);

            var i4 = other.HasVoted.Equals(this.HasVoted);
            var i5 = other.EligibleToVote.Equals(this.EligibleToVote);
            var i6 = Equals(other.VotingPlace, this.VotingPlace);

            var i7 = Equals(other._voterCards, this._voterCards) && other.HasVoted.Equals(this.HasVoted) && other.EligibleToVote.Equals(this.EligibleToVote) && Equals(other.VotingPlace, this.VotingPlace);
            return Equals(other._voterCards, this._voterCards) && other.HasVoted.Equals(this.HasVoted) && other.EligibleToVote.Equals(this.EligibleToVote) && Equals(other.VotingPlace, this.VotingPlace);
        }

        public override int GetHashCode()
        {
            unchecked
            {
                int result = (this._voterCards != null ? this._voterCards.GetHashCode() : 0);
                result = (result * 397) ^ (this._securityQuestions != null ? this._securityQuestions.GetHashCode() : 0);
                result = (result * 397) ^ this.HasVoted.GetHashCode();
                result = (result * 397) ^ this.EligibleToVote.GetHashCode();
                result = (result * 397) ^ (this.VotingPlace != null ? this.VotingPlace.GetHashCode() : 0);
                return result;
            }
        }
    }
}
