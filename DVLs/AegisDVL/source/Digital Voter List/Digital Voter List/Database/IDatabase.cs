using System;
using System.Linq;
using System.Collections.Generic;
using Aegis_DVL.Data_Types;
using System.Diagnostics.Contracts;

namespace Aegis_DVL.Database {
    /// <summary>
    /// The database-layer is responsible for communicating with the database (create, read, update, write). It can also perform batch-operations such as importing and exporting the database.
    /// </summary>
    [ContractClass(typeof(DatabaseContract))]
    public interface IDatabase : IDisposable {
        /// <summary>
        /// Has this voter received a ballot?
        /// This voter has received a ballot!
        /// This user's ballot has been revoked!
        /// </summary>
        /// <param name="voternumber">The voternumber to be checked.</param>
        /// <param name="cpr">The CPR number to be checked.</param>
        /// <returns>The BallotStatus for the voternumber/cpr combination.</returns>
        BallotStatus this[VoterNumber voternumber, CPR cpr] { [Pure] get; set; }

        /// <summary>
        /// Has this voter received a ballot?
        /// This voter has received a ballot!
        /// This user's ballot has been revoked!
        /// </summary>
        /// <param name="cpr">The CPR number to be checked.</param>
        /// <param name="masterPassword">The masterpassword of the election.</param>
        /// <returns>The BallotStatus for the voternumber/cpr combination.</returns>
        BallotStatus this[CPR cpr, string masterPassword] { [Pure] get; set; }

        /// <summary>
        ///What does the entire database look like?
        /// </summary>
        IEnumerable<EncryptedVoterData> AllData { [Pure] get; }

        /// <summary>
        /// Who is my parent station?
        /// </summary>
        Station Parent { [Pure] get; }

        #region Database Transportation
        /// <summary>
        /// Import this encrypted data into the database!
        /// </summary>
        /// <param name="data">A dataset to be imported.</param>
        void Import(IEnumerable<EncryptedVoterData> data);
        #endregion
    }

    [ContractClassFor(typeof(IDatabase))]
    public abstract class DatabaseContract : IDatabase {
        public BallotStatus this[VoterNumber voternumber, CPR cpr] {
            get {
                return default(BallotStatus);
            }
            set {
                //You can't set a ballot as unavailable. If it's in the DB, it's either received or not received.
                Contract.Requires(value != BallotStatus.Unavailable);
                //When you're setting a value, it must be in the DB
                Contract.Requires(this[voternumber, cpr] != BallotStatus.Unavailable);
                //You can only hand out or revoke ballots if they have the opposite state
                //If it's not handed out, you can hand it out
                Contract.Requires(value != BallotStatus.Received || this[voternumber, cpr] == BallotStatus.NotReceived);
                //If it's handed out, you can revoke it.
                Contract.Requires(value != BallotStatus.NotReceived || this[voternumber, cpr] == BallotStatus.Received);
                Contract.Ensures(this[voternumber, cpr] == value);
            }
        }

        public BallotStatus this[CPR cpr, string masterPassword] {
            get {
                Contract.Requires(masterPassword != null);
                Contract.Requires(Parent.ValidMasterPassword(masterPassword));
                return default(BallotStatus);
            }
            set {
                Contract.Requires(Parent.ValidMasterPassword(masterPassword));

                //You can't set a ballot as unavailable. If it's in the DB, it's either received or not received.
                Contract.Requires(value != BallotStatus.Unavailable);
                //When you're setting a value, it must be in the DB
                Contract.Requires(this[cpr, masterPassword] != BallotStatus.Unavailable);
                //You can only hand out or revoke ballots if they have the opposite state
                //If it's not handed out, you can hand it out
                Contract.Requires(value != BallotStatus.Received || this[cpr, masterPassword] == BallotStatus.NotReceived);
                //If it's handed out, you can revoke it.
                Contract.Requires(value != BallotStatus.NotReceived || this[cpr, masterPassword] == BallotStatus.Received);
                Contract.Ensures(this[cpr, masterPassword] == value);
            }
        }

        public IEnumerable<EncryptedVoterData> AllData {
            get {
                Contract.Ensures(Contract.Result<IEnumerable<EncryptedVoterData>>() != null);
                return default(IEnumerable<EncryptedVoterData>);
            }
        }

        public Station Parent {
            get {
                Contract.Ensures(Contract.Result<Station>() != null);
                return default(Station);
            }
        }

        public void Import(IEnumerable<EncryptedVoterData> data) {
            Contract.Requires(data != null);
        }

        public void Dispose() {
        }
    }
}