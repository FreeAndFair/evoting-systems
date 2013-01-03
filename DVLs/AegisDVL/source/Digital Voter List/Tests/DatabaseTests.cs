using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Aegis_DVL;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;
using NUnit.Framework;

namespace Tests {
    [TestFixture]
    public class DatabaseTests {
        /// <summary>
        /// SetUp test helper properties.
        /// </summary>
        [SetUp]
        public void SetUp() {
            Station = new Station(new TestUi(), "dataEncryption.key", "yo boii", 62000, "DatabaseTestVoters.sqlite");
            Assert.That(Station.ValidMasterPassword("yo boii"));
        }

        [TearDown]
        public void TearDown() {
            Station.Dispose();
            Station = null;
            File.Delete("DatabaseTestVoters.sqlite");
        }

        public Station Station { get; private set; }

        /// <summary>
        /// 
        /// </summary>
        [Test]
        public void Test() {
            var db = Station.Database;
            var vn = new VoterNumber(250000);
            var cpr = new CPR(2312881234);

            Assert.That(db[vn, cpr] == BallotStatus.Unavailable);
            //Contracts do not allow us to do this, but they can be disabled.... 
            //Assert.Throws<ArgumentException>(() => db[vn, cpr] = BallotStatus.NotReceived);

            db.Import(new List<EncryptedVoterData> { new EncryptedVoterData(new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(vn.Value), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value + (uint)BallotStatus.NotReceived), Station.Crypto.VoterDataEncryptionKey))) });

            Assert.That(db.AllData != null);
            Assert.That(db.AllData.All(data => !Equals(data.BallotStatus, null) && !Equals(data.CPR, null) && !Equals(data.VoterNumber, null)));
            
            //CPR is in DB, but the voternumber doesn't match.
            Assert.That(db[new VoterNumber(123), cpr] == BallotStatus.Unavailable);
            
            Assert.That(db[vn, cpr] == BallotStatus.NotReceived);
            db[vn, cpr] = BallotStatus.Received;
            Assert.That(db[vn, cpr] == BallotStatus.Received);
            db[vn, cpr] = BallotStatus.NotReceived;
            Assert.That(db[vn, cpr] == BallotStatus.NotReceived);

            var notNull = true;
            db.AllData.ForEach(row => notNull = notNull & !Equals(row.VoterNumber, null));
            Assert.That(notNull);
        }

        [Test]
        public void TestMasterPasswordDb() {
            var db = Station.Database;
            var vn = new VoterNumber(250000);
            var cpr = new CPR(2312881234);

            Assert.That(db[cpr, "yo boii"] == BallotStatus.Unavailable);

            db.Import(new List<EncryptedVoterData> { new EncryptedVoterData(new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(vn.Value), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value + (uint)BallotStatus.NotReceived), Station.Crypto.VoterDataEncryptionKey))), new EncryptedVoterData(new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(vn.Value + 5), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value + 5), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value + (uint)BallotStatus.NotReceived + 5), Station.Crypto.VoterDataEncryptionKey))) });

            Assert.That(db.AllData != null);
            Assert.That(db.AllData.All(data => !Equals(data.BallotStatus, null) && !Equals(data.CPR, null) && !Equals(data.VoterNumber, null)));
            Assert.That(db[cpr, "yo boii"] == BallotStatus.NotReceived);

            //Contracts do not allow us to do this, but they can be disabled.... 
            //Assert.Throws<ArgumentException>(() => status = db[cpr, "yo boii"]);
            //Assert.Throws<ArgumentException>(() => db[new CPR(123), "yo boii"] = BallotStatus.NotReceived);

            db[cpr, "yo boii"] = BallotStatus.Received;
            Assert.That(db[cpr, "yo boii"] == BallotStatus.Received);
            db[cpr, "yo boii"] = BallotStatus.NotReceived;
            Assert.That(db[cpr, "yo boii"] == BallotStatus.NotReceived);

            var notNull = true;
            db.AllData.ForEach(row => notNull = notNull & !Equals(row.VoterNumber, null));
            Assert.That(notNull);
        }
    }
}
