/*
 * Authors: Morten, Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

namespace DigitalVoterList.Election
{
    using System.Collections.Generic;
    using System.Diagnostics.Contracts;

    /// <summary>
    /// A factory responsible of creating Data Access Objects.
    /// </summary>
    public static class DAOFactory
    {
        private static Dictionary<User, IDataAccessObject> daos = new Dictionary<User, IDataAccessObject>();

        public static bool Ready { get; private set; }

        private static string _connectionString;

        public static string ConnectionString
        {
            private get
            {
                return _connectionString;
            }
            set
            {
                _connectionString = value;
                Ready = true;
            }
        }

        /// <summary>
        /// May i have the Data Access Object for this user?
        /// </summary>
        /// <param name="u">The user for which data access permissions will be fetched</param>
        /// <returns>A data access object ready to use</returns>
        public static IDataAccessObject getDAO(User u)
        {
            Contract.Requires(Ready);
            Contract.Requires(u != null);
            Contract.Ensures(Contract.Result<IDataAccessObject>() != null);
            Contract.Ensures(daos.ContainsKey(u));

            if (!daos.ContainsKey(u)) //Check if dao already exists
            {
                IDataAccessObject dao = DAOMySql.GetDAO(u, ConnectionString);
                daos[u] = dao; //Create dao if it doesn't exist
            }
            return daos[u];
        }

        /// <summary>
        /// May i have the data access object for the current user?
        /// </summary>
        public static IDataAccessObject CurrentUserDAO
        {
            get
            {
                Contract.Requires(Ready);
                Contract.Requires(VoterListApp.CurrentUser != null);
                return getDAO(VoterListApp.CurrentUser);
            }
        }
    }
}
