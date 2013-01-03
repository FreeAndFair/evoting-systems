using System;
using System.Collections.Generic;
using System.Data.SQLite;
using System.Diagnostics.Contracts;
using System.Linq;
using Aegis_DVL.Cryptography;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;

namespace Aegis_DVL.Database {
    class SqLiteDatabase : IDatabase {
        private readonly Entities _db;

        /// <summary>
        /// May I have a new SqliteDatabase?
        /// </summary>
        /// <param name="parent">The parent station of the database.</param>
        /// <param name="filename">The name of the file where the data is stored. Defaults to Voters.sqlite.</param>
        public SqLiteDatabase(Station parent, string filename = "Voters.sqlite") {
            Contract.Requires(parent != null);
            Contract.Requires(filename != null);

            Parent = parent;
            var password = Crypto.GeneratePassword();
            InitDb(filename, password);

            var conStr = String.Format("metadata=res://*/Database.VoterModel.csdl|res://*/Database.VoterModel.ssdl|res://*/Database.VoterModel.msl;provider=System.Data.SQLite;provider connection string='data source={0};Password={1}'", filename, password);
            _db = new Entities(conStr);
            _db.Connection.Open();
        }

        public BallotStatus this[VoterNumber voternumber, CPR cpr] {
            get {
                var voter = GetVoter(cpr);
                if(voter == null)
                    return BallotStatus.Unavailable;
                var encVn = Parent.Crypto.AsymmetricEncrypt(Bytes.From(voternumber.Value), Parent.Crypto.VoterDataEncryptionKey);
                if(!voter.VoterNumber.IsIdenticalTo(encVn))
                    return BallotStatus.Unavailable;
                var encBallotReceived = Parent.Crypto.AsymmetricEncrypt(Bytes.From((uint)BallotStatus.Received), Parent.Crypto.VoterDataEncryptionKey);
                return voter.BallotStatus.IsIdenticalTo(encBallotReceived) ? BallotStatus.Received : BallotStatus.NotReceived;
            }
            set {
                if(Parent.Logger != null)
                    Parent.Logger.Log("Setting ballotstatus for voternumber=" + voternumber + "; CPR=" + cpr + " to " + value, Level.Info);
                var voter = GetVoter(cpr);
                voter.BallotStatus = Parent.Crypto.AsymmetricEncrypt(Bytes.From((uint)value), Parent.Crypto.VoterDataEncryptionKey);
                _db.SaveChanges();
            }
        }

        public BallotStatus this[CPR cpr, string masterPassword] {
            get {
                var encBallotReceived = Parent.Crypto.AsymmetricEncrypt(Bytes.From((uint)BallotStatus.Received), Parent.Crypto.VoterDataEncryptionKey);
                var voter = GetVoter(cpr);
                if(voter == null)
                    return BallotStatus.Unavailable;
                return voter.BallotStatus.IsIdenticalTo(encBallotReceived) ? BallotStatus.Received : BallotStatus.NotReceived;
            }
            set {
                if(Parent.Logger != null)
                    Parent.Logger.Log("Setting ballotstatus for CPR=" + cpr + " with masterpassword to " + value, Level.Info);
                var voter = GetVoter(cpr);
                voter.BallotStatus = Parent.Crypto.AsymmetricEncrypt(Bytes.From((uint)value), Parent.Crypto.VoterDataEncryptionKey);
                _db.SaveChanges();
            }
        }

        private Voter GetVoter(CPR cpr) {
            var encCpr = Parent.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value), Parent.Crypto.VoterDataEncryptionKey);

            var res = _db.Voters.Where(data => data.CPR == encCpr.Value);
            return !res.Any() ? null : res.Single();
        }

        public IEnumerable<EncryptedVoterData> AllData {
            get { return _db.Voters.ToArray().Select(data => new EncryptedVoterData(new CipherText(data.VoterNumber), new CipherText(data.CPR), new CipherText(data.BallotStatus))).ToArray(); }
        }

        public Station Parent { get; private set; }

        /// <summary>
        /// Add this encrypted voter data to the database!
        /// </summary>
        /// <param name="data">The data to add.</param>
        private void Add(EncryptedVoterData data) {
            Contract.Requires(!Equals(data, null));
            Contract.Requires(Contract.ForAll(AllData, row => !row.CPR.Value.IsIdenticalTo(data.CPR.Value) && !row.VoterNumber.Value.IsIdenticalTo(data.VoterNumber.Value)));
            _db.Voters.AddObject(Voter.CreateVoter(data.VoterNumber, data.CPR, data.BallotStatus));
            _db.SaveChanges();
        }

        private static void InitDb(string fileName, string password) {
            SQLiteConnection.CreateFile(fileName);
            var connString = string.Format("data source={0};Password={1}", fileName, password);
            using(var db = new SQLiteConnection(connString)) {
                db.Open();
                using(var cmd = db.CreateCommand()) {
                    cmd.CommandText = "CREATE TABLE Voters(VoterNumber BLOB NOT NULL PRIMARY KEY DESC, CPR BLOB UNIQUE NOT NULL, BallotStatus BLOB NOT NULL)";
                    cmd.ExecuteNonQuery();
                }
            }
        }

        public void Import(IEnumerable<EncryptedVoterData> data) {
            var c = 0;
            using(var transaction = _db.Connection.BeginTransaction()) {
                data.ForEach(row => { Add(row); c++; });
                transaction.Commit();
            }
            if(Parent.Logger != null)
                Parent.Logger.Log("Importing data. " + c + " entries.", Level.Info);
        }


        #region IDisposable
        ~SqLiteDatabase() {
            Dispose(false);
        }

        private bool _isDisposed;
        public void Dispose() {
            if(!_isDisposed)
                Dispose(true);
            GC.SuppressFinalize(this);
        }

        private void Dispose(bool disposing) {
            _isDisposed = true;
            if(disposing)
                _db.Dispose();
        }
        #endregion
    }
}