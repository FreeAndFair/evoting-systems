using System;
using System.IO;
using Aegis_DVL;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;
using NUnit.Framework;
using Org.BouncyCastle.Crypto;

namespace Tests {
    [TestFixture]
    public class DataTypesTests {
        /// <summary>
        /// SetUp test helper properties.
        /// </summary>
        [SetUp]
        public void SetUp() {
        }

        /// <summary>
        /// 
        /// </summary>
        [Test]
        public void VoterNumberTest() {
            var vn = new VoterNumber(8000000);
            Assert.That(vn.Value == 8000000);
            Assert.That(vn.ToString().Equals("8000000"));
            Assert.That(((uint)8000000).Equals(vn));
        }

        [Test]
        public void CPRTest() {
            var cpr = new CPR(2312881133);
            Assert.That(cpr.Value == 2312881133);
            Assert.That(cpr.ToString().Equals("2312881133"));
            Assert.That(2312881133.Equals(cpr));
        }

        [Test]
        public void BallotStatusTest() {
            var bs = BallotStatus.NotReceived;
            Assert.That((uint)bs == 11);
            bs = BallotStatus.Received;
            Assert.That((uint)bs == 7);
            bs = BallotStatus.Unavailable;
            Assert.That((uint)bs == 13);
        }

        [Test]
        public void MessageTest() {
            var symKey = new CipherText(new byte[] { 1, 2 });
            var cmd = new CipherText(new byte[] { 2, 3 });
            var senderHash = new CipherText(new byte[] { 3, 4 });
            var iv = new byte[] { 5, 6 };

            var msg = new Message(symKey, cmd, senderHash, iv);

            Assert.That(msg.SymmetricKey.Equals(symKey));
            Assert.That(msg.Command.Equals(cmd));
            Assert.That(msg.SenderHash.Equals(senderHash));
            Assert.That(msg.Iv.IsIdenticalTo(iv));
            Assert.That(msg.ToString() != null);
        }

        [Test]
        public void KeyTest() {
            var asymmetricKeyParameter = new AsymmetricKeyParameter(false);
            var asymmetricKey = new AsymmetricKey(asymmetricKeyParameter);
            Assert.That(asymmetricKey.Value == asymmetricKeyParameter);
            Assert.That(asymmetricKeyParameter == asymmetricKey.Value);
            Assert.That((AsymmetricKeyParameter)asymmetricKey == asymmetricKeyParameter);

            var bytes = new byte[] { 1, 2, 3 };
            var symmetricKey = new SymmetricKey(bytes);
            Assert.That(symmetricKey.Value.IsIdenticalTo(bytes));
        }

        [Test]
        public void CipherTextTest() {
            var bytes = new byte[] { 1, 2, 3, 4, 5, 6 };
            var cipher = new CipherText(bytes);
            Assert.That(bytes.IsIdenticalTo(cipher));
            Assert.That(bytes.IsIdenticalTo(cipher.Value));
            Assert.That(cipher.ToString() != null);
        }

        [Test]
        public void EncryptedVoterDataTest() {
            var voternumber = new CipherText(new byte[] { 2, 1 });
            var cpr = new CipherText(new byte[] { 3, 2 });
            var ballotstatus = new CipherText(new byte[] { 4, 3 });

            var encVoterData = new EncryptedVoterData(voternumber, cpr, ballotstatus);

            Assert.That(voternumber.Equals(encVoterData.VoterNumber));
            Assert.That(cpr.Equals(encVoterData.CPR));
            Assert.That(ballotstatus.Equals(encVoterData.BallotStatus));
            Assert.That(encVoterData.ToString() != null);
        }

        [Test]
        public void PublicKeyWrapperTest() {
            using(var s = new Station(new TestUi(), "dataEncryption.key", "yo boii", 62001, "CoreDataTypesTestsPkWrapperVoters.sqlite")) {
                var originalKey = s.Crypto.Keys.Item1.Value;
                var pkWrapper = new PublicKeyWrapper(s.Crypto, "batman");
                Assert.That(originalKey.Equals(pkWrapper.GetKey(s.Crypto, "batman").Value));
                try {
                    pkWrapper.GetKey(s.Crypto, "wrongKey");
                    Assert.Fail();
                }
                catch (ArgumentException){}
            }
            File.Delete("CoreDataTypesTestsPkWrapperVoters.sqlite");
        }

        [Test]
        public void LogEntryTest() {
            var entry = new LogEntry("hello", Level.Info);
            Assert.That(entry.Level.Equals(Level.Info));
            Assert.That(entry.Message.Equals("hello"));
            Assert.That(entry.Timestamp != null);
            Assert.That(entry.ToString() != null);
        }
    }
}
