/*
 * Authors: Morten, Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System.Collections.Generic;
using System.Security.Cryptography;
using System.Text;

namespace DigitalVoterList.Election
{
    using System.Diagnostics.Contracts;

    /// <summary>
    /// A person responsible of helping out at an election
    /// </summary>
    public class User : Person
    {
        private HashSet<SystemAction> _permissions;
        private HashSet<VotingVenue> _workplaces;

        public new string Cpr { get; private set; }

        /// <summary>
        /// What user has this login?
        /// </summary>
        /// <param name="username">Username</param>
        /// <param name="password">Password</param>
        /// <returns>A validated user obejct, or null if the login is not found.</returns>
        public static User GetUser(string username, string password)
        {
            Contract.Requires(DAOFactory.Ready);
            IDataAccessObject dao = DAOFactory.CurrentUserDAO;
            User u = dao.LoadUser(username);
            if (u == null) return null;
            u.FetchPermissions(username, password);
            return u.Validated ? u : null;
        }

        /// <summary>
        /// The users at the election venue and people adminitrating the electing, who have different priviledges.
        /// </summary>
        /// <param name="id">The database id of the user</param>
        public User(int id, string cpr)
            : base(id)
        {
            Cpr = cpr;
            DbId = id;
            _permissions = new HashSet<SystemAction>();
            _workplaces = new HashSet<VotingVenue>();
        }

        /// <summary>
        /// The users at the election venue and people adminitrating the electing, who have different priviledges.
        /// </summary>
        public User()
            : this(0, null)
        {
        }

        /// <summary>
        /// Validate the user and load according permissions into the user object.
        /// </summary>
        /// <param name="uname">The username to validate</param>
        /// <param name="pwd">The password to validate</param>
        private void FetchPermissions(string uname, string pwd)
        {
            var dao = DAOFactory.getDAO(this);
            string pwdHash = HashPassword(pwd);
            if (DAOFactory.getDAO(this).ValidateUser(uname, HashPassword(pwd)))
            {
                _permissions = dao.GetPermissions(this);
                _workplaces = dao.GetWorkplaces(this);
            }
        }

        /// <summary>
        /// The user's username
        /// </summary>
        public string Username { get; set; }

        public string UserSalt { get; set; }

        public bool Valid { get; set; }

        /// <summary>
        /// Changes the password of this user
        /// </summary>
        /// <param name="oldPwd">The old password</param>
        /// <param name="newPwd">The new password</param>
        /// <returns>Was it succesful?</returns>
        public void ChangePassword(string oldPwd, string newPwd)
        {
            IDataAccessObject dao = DAOFactory.getDAO(this);
            dao.ChangePassword(this, HashPassword(newPwd), HashPassword(oldPwd));
        }

        /// <summary>
        /// Changes the password of this user
        /// </summary>
        /// <param name="newPwd">The new password</param>
        /// <returns>Was it succesful?</returns>
        public void ChangePassword(string newPwd)
        {
            IDataAccessObject dao = DAOFactory.CurrentUserDAO;
            dao.ChangePassword(this, HashPassword(newPwd));
        }

        /// <summary>
        /// The user's id in the database
        /// </summary>
        public new int DbId { get; private set; }

        public int PersonDbId
        {
            get { return base.DbId; }
        }

        /// <summary>
        /// The user's jobtitle
        /// </summary>
        public string Title { get; set; }

        /// <summary>
        /// The users permission. Is an empty set if validation has expired, or has not been performed yet.
        /// </summary>
        public HashSet<SystemAction> Permissions
        {
            get
            {
                return _permissions == null ? new HashSet<SystemAction>() : new HashSet<SystemAction>(_permissions);
            }
        }

        /// <summary>
        /// The voting venue(s) where the user works.
        /// </summary>
        public HashSet<VotingVenue> Workplaces
        {
            get
            {
                return _workplaces == null ? new HashSet<VotingVenue>() : new HashSet<VotingVenue>(_workplaces);
            }
        }

        /// <summary>
        /// Has the user got permission to perform this SystemAction?
        /// </summary>
        /// <param name="a">The SystemAction to check for permission</param>
        /// <returns>True if the user has the permission. False if not.</returns>
        [Pure]
        public bool HasPermission(SystemAction a)
        {
            return Validated && _permissions.Contains(a);
        }

        /// <summary>
        /// Checks if the user works at this specific voting venue
        /// </summary>
        /// <param name="v">The voting venue to check for</param>
        /// <returns>True if the user works here. False if not</returns>
        [Pure]
        public bool WorksHere(VotingVenue v)
        {
            return Validated && _workplaces.Contains(v);
        }

        public bool Validated
        {
            get
            {
                if (_permissions == null) return false;
                if (_permissions.Count < 1) return false;
                return true;
            }
        }

        /// <summary>
        /// Determines whether the specified object is equal to the current object.
        /// </summary>
        /// <returns>
        /// true if the specified object is equal to the current object; otherwise, false.
        /// </returns>
        /// <param name="obj">The object to compare with the current object.</param>
        [Pure]
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
            return Equals(obj as User);
        }

        [Pure]
        private string HashPassword(string password)
        {
            string salted = UserSalt + password + "AX7530G7FR";
            MD5 md5 = System.Security.Cryptography.MD5.Create();
            byte[] inputBytes = System.Text.Encoding.UTF32.GetBytes(salted);
            byte[] hash = md5.ComputeHash(inputBytes);
            StringBuilder output = new StringBuilder();
            for (int i = 0; i < hash.Length; i++)
            {
                output.Append(hash[i].ToString("X2"));
            }
            return output.ToString();
        }

        [Pure]
        public bool Equals(User other)
        {
            if (ReferenceEquals(null, other))
            {
                return false;
            }
            if (ReferenceEquals(this, other))
            {
                return true;
            }
            return base.Equals(other) && Equals(other._permissions, this._permissions) && Equals(other._workplaces, this._workplaces) && Equals(other.UserSalt, this.UserSalt) && other.Valid.Equals(this.Valid) && other.DbId == this.DbId;
        }

        [Pure]
        public override int GetHashCode()
        {
            unchecked
            {
                int result = base.GetHashCode();
                result = (result * 397) ^ (this._permissions != null ? this._permissions.GetHashCode() : 0);
                result = (result * 397) ^ (this._workplaces != null ? this._workplaces.GetHashCode() : 0);
                result = (result * 397) ^ (this.UserSalt != null ? this.UserSalt.GetHashCode() : 0);
                result = (result * 397) ^ this.Valid.GetHashCode();
                result = (result * 397) ^ this.DbId;
                return result;
            }
        }
    }
}
