/*
 * Authors: Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System.Collections.Generic;

namespace DigitalVoterList.Election
{
    using System;
    using System.Diagnostics.Contracts;

    using DigitalVoterList.Election.Administration;

    /// <summary>
    /// A proxy to handle permissions for data access actions
    /// </summary>
    public class DAOPermissionProxy : IDataAccessObject
    {
        private readonly User _user;
        private readonly IDataAccessObject _dao;

        public DAOPermissionProxy(User u, IDataAccessObject dao)
        {
            Contract.Requires(u != null);
            Contract.Requires(dao != null);
            _user = u;
            _dao = dao;
        }

        #region public permission functions

        /// <summary>
        /// Does my user have permission to perform this SystemAction?
        /// </summary>
        /// <param name="a"></param>
        /// <returns></returns>
        public bool ActionPermitted(SystemAction a)
        {
            Contract.Ensures(
                (!_user.HasPermission(a) && Contract.Result<bool>() == false)
                || (_user.HasPermission(a) && Contract.Result<bool>() == true));

            return _user.HasPermission(a);
        }

        /// <summary>
        /// Is this user my user?
        /// </summary>
        /// <param name="user"></param>
        /// <returns></returns>
        public bool CorrectUser(User user)
        {
            Contract.Requires(user != null);
            return user.Equals(_user);
        }

        /// <summary>
        /// Is my user permitted to work on this voting venue?
        /// </summary>
        /// <param name="v"></param>
        /// <param name="msg"></param>
        /// <returns></returns>
        public bool PermittedToWorkHere(VotingVenue v, string msg = "You can't perform this action, as you don't work in the right voting venue, or have global access")
        {
            return _user.WorksHere(v) || this.ActionPermitted(SystemAction.AllVotingPlaces);
        }

        #endregion

        #region privateTestHelpers


        private void TestCorrectUser(User user)
        {
            Contract.Requires(user != null);
            if (!this.CorrectUser(user)) throw new PermissionException(_user, "You must be logged as this user");
        }

        private void TestWorksHere(VotingVenue votingVenue)
        {
            if (!this.PermittedToWorkHere(votingVenue)) throw new PermissionException(_user, "You don't work at this voting venue");
        }

        private void TestPermission(SystemAction a, string msg)
        {
            if (!this.ActionPermitted(a)) throw new PermissionException(a, _user, msg);
        }

        #endregion

        #region proxyfunctions

        public Citizen LoadCitizen(int id)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.LoadCitizen));
            this.TestPermission(SystemAction.LoadCitizen, "You dont have permission to load information about citizens");
            return _dao.LoadCitizen(id);
        }

        public User LoadUser(string username)
        {
            return _dao.LoadUser(username);
        }

        public User LoadUser(int id)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.LoadUser));
            this.TestPermission(SystemAction.LoadUser, "You dont have permission to load information about users");
            return _dao.LoadUser(id);
        }

        public bool ValidateUser(string username, string passwordHash)
        {
            return _dao.ValidateUser(username, passwordHash);
        }

        public HashSet<SystemAction> GetPermissions(User u)
        {
            return _dao.GetPermissions(u);
        }

        public HashSet<VotingVenue> GetWorkplaces(User u)
        {
            return _dao.GetWorkplaces(u);
        }

        public HashSet<VotingVenue> Workplaces(User u)
        {
            return _dao.GetWorkplaces(u);
        }

        public VoterCard LoadVoterCard(int id)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.LoadVoterCard));
            this.TestPermission(SystemAction.LoadVoterCard, "You dont have permission to load information about votercards");
            return _dao.LoadVoterCard(id);
        }

        public VoterCard LoadVoterCard(string idKey)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.ScanVoterCard));
            this.TestPermission(SystemAction.ScanVoterCard, "You dont have permission to scan votercards");
            return _dao.LoadVoterCard(idKey);
        }

        /// <summary>
        /// Update votercards
        /// </summary>
        public void UpdateVoterCards()
        {
            Contract.Requires(this.ActionPermitted(SystemAction.UpdateVoterCards));
            this.TestPermission(SystemAction.UpdateVoterCards, "You dont have permission to update votercards");
            _dao.UpdateVoterCards();
        }

        public List<Citizen> FindCitizens(Dictionary<CitizenSearchParam, object> data, SearchMatching matching = SearchMatching.Similair)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.FindCitizen));
            this.TestPermission(SystemAction.FindCitizen, "you don't have permission to search for citizens");
            return _dao.FindCitizens(data, matching);
        }

        public List<User> FindUsers(Dictionary<UserSearchParam, object> data, SearchMatching matching)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.FindUser));
            this.TestPermission(SystemAction.FindUser, "You don't have permission to search for users");
            return _dao.FindUsers(data, matching);
        }

        public void Save(User user)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.SaveUser));
            this.TestPermission(SystemAction.SaveUser, "You don't have permission to save users");
            _dao.Save(user);
        }

        public void SetHasVoted(Citizen citizen, string cprKey)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.SetHasVoted));
            Contract.Requires(this.PermittedToWorkHere(citizen.VotingPlace));
            this.TestPermission(SystemAction.SetHasVoted, "You don't have permission register voting");
            this.TestWorksHere(citizen.VotingPlace);
            _dao.SetHasVoted(citizen, cprKey);
        }

        public void SetHasVoted(Citizen citizen)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.SetHasVotedManually));
            this.TestPermission(SystemAction.SetHasVotedManually, "You don't have permission to register voting without a key");

            _dao.SetHasVoted(citizen);
        }

        public void ChangePassword(User user, string newPasswordHash, string oldPasswordHash)
        {
            Contract.Requires(ActionPermitted(SystemAction.ChangeOwnPassword));
            Contract.Requires(this.CorrectUser(user));
            this.TestPermission(SystemAction.ChangeOwnPassword, "You don't have permission to change your own password");
            this.TestCorrectUser(user);
            _dao.ChangePassword(user, newPasswordHash, oldPasswordHash);
        }

        public void ChangePassword(User user, string newPasswordHash)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.ChangeOthersPassword));
            this.TestPermission(SystemAction.ChangeOthersPassword, "You don't have permission to changed users passwords");
            _dao.ChangePassword(user, newPasswordHash);
        }

        public void UpdatePeople(Func<Citizen, RawPerson, Citizen> update)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.UpdateCitizens));
            this.TestPermission(SystemAction.UpdateCitizens, "You don't have permission to update citizen data.");
            _dao.UpdatePeople(update);
        }

        /// <summary>
        /// Update all persons in the dataset with this update
        /// </summary>
        /// <param name="voterCardPrinter"></param>
        public void PrintVoterCards(VoterCardPrinter voterCardPrinter)
        {
            Contract.Requires(this.ActionPermitted(SystemAction.PrintVoterCards));
            this.TestPermission(SystemAction.PrintVoterCards, "You don't have permission to print votercards.");
            _dao.PrintVoterCards(voterCardPrinter);
        }

        #endregion
    }
}
