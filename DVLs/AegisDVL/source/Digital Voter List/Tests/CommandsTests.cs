using System.Collections.Generic;
using System.IO;
using Aegis_DVL;
using Aegis_DVL.Commands;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;
using NUnit.Framework;

namespace Tests {
    [TestFixture]
    public class CommandsTests {

        public Station Manager { get; private set; }
        public Station Station { get; private set; }
        public Station NewPeer { get; private set; }


        /// <summary>
        /// SetUp test helper properties.
        /// </summary>
        [SetUp]
        public void SetUp() {
            var ui = new TestUi();
            Manager = new Station(ui, "dataEncryption.key", "yo boii", 62001, "CommandsTestsManagerVoters.sqlite", "CommandsTestsLog.sqlite");
            Station = new Station(ui, 62002, "CommandsTestsStationVoters.sqlite");
            NewPeer = new Station(ui, 62003, "CommandsTestsNewPeerVoters.sqlite");

            Manager.Manager = Manager.Address;
            Station.Manager = Manager.Address;
            NewPeer.Manager = Manager.Address;



            Manager.AddPeer(Station.Address, Station.Crypto.Keys.Item1);

            Station.AddPeer(Manager.Address, Manager.Crypto.Keys.Item1);
            Station.AddPeer(NewPeer.Address, NewPeer.Crypto.Keys.Item1);
            Station.Crypto.VoterDataEncryptionKey = Manager.Crypto.VoterDataEncryptionKey;

            NewPeer.AddPeer(Manager.Address, Manager.Crypto.Keys.Item1);
        }

        [TearDown]
        public void TearDown() {
            Manager.Dispose();
            Station.Dispose();
            NewPeer.Dispose();
            Manager = null;
            Station = null;
            NewPeer = null;
            File.Delete("CommandsTestsManagerVoters.sqlite");
            File.Delete("CommandsTestsStationVoters.sqlite");
            File.Delete("CommandsTestsNewPeerVoters.sqlite");
            File.Delete("CommandsTestsLog.sqlite");
        }

        [Test]
        public void AddPeerCommandTest() {
            var cmd = new AddPeerCommand(Manager.Address, Station.Address, Station.Crypto.Keys.Item1);
            Assert.That(cmd.Sender == Manager.Address);

            //Manager sending to station, should work
            Assert.That(!NewPeer.Peers.ContainsKey(Station.Address));
            cmd.Execute(NewPeer);
            Assert.That(NewPeer.Peers.ContainsKey(Station.Address));

            //Station sending to manager, shouldn't work.
            cmd = new AddPeerCommand(NewPeer.Address, NewPeer.Address, NewPeer.Crypto.Keys.Item1);
            Assert.That(!Manager.Peers.ContainsKey(NewPeer.Address));
            cmd.Execute(Manager);
            Assert.That(!Manager.Peers.ContainsKey(NewPeer.Address));
        }

        [Test]
        public void BallotReceivedCommandAndRevokeBallotCommandTest() {
            var vn = new VoterNumber(250000);
            var cpr = new CPR(2312881234);

            Assert.That(Station.Database[vn, cpr] == BallotStatus.Unavailable);

            Station.Database.Import(new List<EncryptedVoterData> { new EncryptedVoterData(new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(vn.Value), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value + (uint)BallotStatus.NotReceived), Station.Crypto.VoterDataEncryptionKey))) });

            var cmd = new BallotReceivedCommand(Manager.Address, Station.Address, vn, cpr);
            Assert.That(cmd.Sender == Manager.Address);
            Assert.That(Station.Database[vn, cpr] == BallotStatus.NotReceived);
            cmd.Execute(Station);
            Assert.That(Station.Database[vn, cpr] == BallotStatus.Received);

            var revoke = new RevokeBallotCommand(Manager.Address, vn, cpr);
            revoke.Execute(Station);
            Assert.That(Station.Database[vn, cpr] == BallotStatus.NotReceived);
        }

        [Test]
        public void CryptoCommandTest() {
            var cmd = new CryptoCommand(Manager, Station.Address, new StartElectionCommand(Manager.Address));
            Assert.That(cmd.Sender == Manager.Address);
            Assert.That(!Station.ElectionInProgress);
            cmd.Execute(Station);
            Assert.That(Station.ElectionInProgress);

            //Station sending to NewPeer
            NewPeer.RemovePeer(Manager.Address);
            cmd = new CryptoCommand(Station, NewPeer.Address, new StartElectionCommand(Station.Address));
            Assert.That(!NewPeer.ElectionInProgress);
            Assert.Throws<TheOnlyException>(() => cmd.Execute(NewPeer));
            Assert.That(!NewPeer.ElectionInProgress);
        }

        [Test]
        public void ShutDownElectionCommandTest() {
            var cmd = new ShutDownElectionCommand(Manager.Address);
            Assert.That(cmd.Sender == Manager.Address);
            Assert.Throws<TheOnlyException>(() => cmd.Execute(Station));
        }

        [Test]
        public void PublicKeyExchangeCommandTest() {
            var ui = new TestUi();
            using(var manager = new Station(ui, "dataEncryption.key", "pw", 65432, "CommandsTestPublicKeyExchangeCommandTestManagerVoters.sqlite", "CommandsTestPublicKeyExchangeCommandTestManagerLog.sqlite"))
            using(var receiver = new Station(ui, 65433, "CommandsTestPublicKeyExchangeCommandTestReceiverVoters.sqlite")) {
                var cmd = new PublicKeyExchangeCommand(manager);
                Assert.That(cmd.Sender.Equals(manager.Address));
                Assert.That(!receiver.Peers.ContainsKey(manager.Address));
                Assert.That(receiver.Manager == null);
                cmd.Execute(receiver);
                Assert.That(receiver.Peers.ContainsKey(manager.Address));
                Assert.That(receiver.Manager.Equals(manager.Address));
            }
            File.Delete("CommandsTestPublicKeyExchangeCommandTestManagerVoters.sqlite");
            File.Delete("CommandsTestPublicKeyExchangeCommandTestManagerLog.sqlite");
            File.Delete("CommandsTestPublicKeyExchangeCommandTestReceiverVoters.sqlite");
        }

        [Test]
        public void ElectNewManagerCommandTest() {
            var cmd = new ElectNewManagerCommand(Station.Address);
            NewPeer.AddPeer(Station.Address, Station.Crypto.Keys.Item1);
            Manager.StopListening();
            cmd.Execute(NewPeer);
            Assert.That(NewPeer.Manager.Equals(Station.Address));
        }

        [Test]
        public void BallotRequestDeniedTest() {
            var cmd = new BallotRequestDeniedCommand(Manager.Address);
            Assert.That(cmd.Sender.Equals(Manager.Address));
            cmd.Execute(Station);
            Assert.That(!((TestUi)Manager.UI).HandOutBallot);
            cmd = new BallotRequestDeniedCommand(Station.Address);
            cmd.Execute(Station);
        }

        [Test]
        public void RequestBallotCommandsTest() {
            var ui = (TestUi)Manager.UI;
            var vn = new VoterNumber(250000);
            var cpr = new CPR(2312881234);
            var cmd = new RequestBallotCommand(Station.Address, vn, cpr);
            var pswdcmd = new RequestBallotCPROnlyCommand(Station.Address, cpr, "yo boii");
            var data = new List<EncryptedVoterData> { new EncryptedVoterData(new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(vn.Value), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value), Station.Crypto.VoterDataEncryptionKey)), new CipherText(Station.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value + (uint)BallotStatus.NotReceived), Station.Crypto.VoterDataEncryptionKey))) };
            Manager.Database.Import(data);
            Station.Database.Import(data);
            Station.MasterPassword = Manager.MasterPassword;
            Manager.BallotReceived(vn, cpr);
            cmd.Execute(Manager);
            Assert.That(!ui.HandOutBallot);
            pswdcmd.Execute(Manager);
            Assert.That(!ui.HandOutBallot);

            Manager.RevokeBallot(vn, cpr);

            cmd = new RequestBallotCommand(Manager.Address, vn, cpr);
            pswdcmd = new RequestBallotCPROnlyCommand(Manager.Address, cpr, "yo boii");
            cmd.Execute(Manager);
            Assert.That(ui.HandOutBallot);
            Manager.RevokeBallot(vn, cpr);
            pswdcmd.Execute(Manager);
            Assert.That(ui.HandOutBallot);
        }

        [Test]
        public void IsAliveCommandTest() {
            var cmd = new IsAliveCommand(Station.Address);
            Assert.That(cmd.Sender.Equals(Station.Address));
        }

        [Test]
        public void ManagerRequirementCheckTest() {
            var start = new StartElectionCommand(NewPeer.Address);
            var end = new EndElectionCommand(NewPeer.Address);
            Assert.That(!((TestUi)Station.UI).OngoingElection);
            start.Execute(Station);
            Assert.That(!((TestUi)Station.UI).OngoingElection);
            Station.StartElection();
            Assert.That(Station.ElectionInProgress);
            end.Execute(Station);
            Assert.That(Station.ElectionInProgress);

            var vn = new VoterNumber(5);
            var cpr = new CPR(5);
            var req = new RequestBallotCommand(NewPeer.Address, vn, cpr);
            var reqCPROnly = new RequestBallotCPROnlyCommand(NewPeer.Address, cpr, "sup homey");
            var revoke = new RevokeBallotCommand(NewPeer.Address, vn, cpr);
            var revokeCPROnly = new RevokeBallotCPROnlyCommand(NewPeer.Address, cpr, "sup homey");
            req.Execute(Station);
            reqCPROnly.Execute(Station);
            revoke.Execute(Station);
            revokeCPROnly.Execute(Station);
            Assert.That(Station.Database[vn, cpr] == BallotStatus.Unavailable);

            NewPeer.Crypto.VoterDataEncryptionKey = Manager.Crypto.VoterDataEncryptionKey;
            var sync = new SyncCommand(NewPeer);
            sync.Execute(Station);

            var promoteManager = new PromoteNewManagerCommand(NewPeer.Address, NewPeer.Address);
            promoteManager.Execute(Station);
            Assert.That(!Station.Manager.Equals(NewPeer.Address));
        }
    }
}