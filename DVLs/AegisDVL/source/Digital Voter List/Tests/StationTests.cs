using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using Aegis_DVL;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Logging;
using Aegis_DVL.Util;
using NUnit.Framework;
using System.Linq;

namespace Tests {
    [TestFixture]
    public class StationTests {
        /// <summary>
        /// SetUp test helper properties.
        /// </summary>
        [SetUp]
        public void SetUp() {
            const string masterpassword = "yo boii";
            var ui = new TestUi();
            Manager = new Station(ui, "dataEncryption.key", masterpassword, 62000, "StationTestsManagerVoters.sqlite", "StationTestsManagerLog.sqlite");
            var pswd = Manager.Crypto.Hash(Bytes.From("_½æøåÆÅØ§.^\\,QBsa(/YHh*^#3£()cZ?\\}`|`´ '*jJxCvZ;;;<><aQ\\ ><" + masterpassword));
            Peer1 = new Station(ui, 62001, "StationTestsPeer1Voters.sqlite") {
                Manager = Manager.Address,
                MasterPassword = pswd,
                Crypto = { VoterDataEncryptionKey = Manager.Crypto.VoterDataEncryptionKey }
            };
            Peer2 = new Station(ui, 62002, "StationTestsPeer2Voters.sqlite") {
                Manager = Manager.Address,
                MasterPassword = pswd,
                Crypto = { VoterDataEncryptionKey = Manager.Crypto.VoterDataEncryptionKey }
            };
            Peer3 = new Station(ui, 62003, "StationTestsPeer3Voters.sqlite") {
                Manager = Manager.Address,
                MasterPassword = pswd,
                Crypto = { VoterDataEncryptionKey = Manager.Crypto.VoterDataEncryptionKey }
            };
            Peer4 = new Station(ui, 62004, "StationTestsPeer4Voters.sqlite") {
                Manager = Manager.Address,
                MasterPassword = pswd,
                Crypto = { VoterDataEncryptionKey = Manager.Crypto.VoterDataEncryptionKey }
            };

            Manager.StopListening();
            Peer1.StopListening();
            Peer2.StopListening();
            Peer3.StopListening();
            Peer4.StopListening();

            Peer1.Logger = new Logger(Peer1, "StationsTestsPeer1Log.sqlite");
            Peer2.Logger = new Logger(Peer2, "StationsTestsPeer2Log.sqlite");
            Peer3.Logger = new Logger(Peer3, "StationsTestsPeer3Log.sqlite");
            Peer4.Logger = new Logger(Peer4, "StationsTestsPeer4Log.sqlite");

            Manager.AddPeer(Peer1.Address, Peer1.Crypto.Keys.Item1);
            Manager.AddPeer(Peer2.Address, Peer2.Crypto.Keys.Item1);
            Manager.AddPeer(Peer3.Address, Peer3.Crypto.Keys.Item1);


            Peer1.AddPeer(Manager.Address, Manager.Crypto.Keys.Item1);
            Peer1.AddPeer(Peer2.Address, Peer2.Crypto.Keys.Item1);
            Peer1.AddPeer(Peer3.Address, Peer3.Crypto.Keys.Item1);


            Peer2.AddPeer(Manager.Address, Manager.Crypto.Keys.Item1);
            Peer2.AddPeer(Peer1.Address, Peer1.Crypto.Keys.Item1);
            Peer2.AddPeer(Peer3.Address, Peer3.Crypto.Keys.Item1);

            Peer3.AddPeer(Manager.Address, Manager.Crypto.Keys.Item1);
            Peer3.AddPeer(Peer1.Address, Peer1.Crypto.Keys.Item1);
            Peer3.AddPeer(Peer2.Address, Peer2.Crypto.Keys.Item1);

            ManagerListener = Manager.Communicator.ReceiveAndHandle;
            Peer1Listener = Peer1.Communicator.ReceiveAndHandle;
            Peer2Listener = Peer2.Communicator.ReceiveAndHandle;
            Peer3Listener = Peer3.Communicator.ReceiveAndHandle;
        }

        [TearDown]
        public void TearDown() {
            Manager.Dispose();
            Peer1.Dispose();
            Peer2.Dispose();
            Peer3.Dispose();
            Peer4.Dispose();
            Manager = null;
            Peer1 = null;
            Peer2 = null;
            Peer3 = null;
            Peer4 = null;
            File.Delete("StationTestsManagerVoters.sqlite");
            File.Delete("StationTestsPeer1Voters.sqlite");
            File.Delete("StationTestsPeer2Voters.sqlite");
            File.Delete("StationTestsPeer3Voters.sqlite");
            File.Delete("StationTestsPeer4Voters.sqlite");

            File.Delete("StationsTestsManagerLog.sqlite");
            File.Delete("StationsTestsPeer1Log.sqlite");
            File.Delete("StationsTestsPeer2Log.sqlite");
            File.Delete("StationsTestsPeer3Log.sqlite");
            File.Delete("StationsTestsPeer4Log.sqlite");
        }

        public Station Manager { get; private set; }
        public Station Peer1 { get; private set; }
        public Station Peer2 { get; private set; }
        public Station Peer3 { get; private set; }
        public Station Peer4 { get; private set; }

        public Listener ManagerListener { get; private set; }
        public Listener Peer1Listener { get; private set; }
        public Listener Peer2Listener { get; private set; }
        public Listener Peer3Listener { get; private set; }

        public delegate void Listener();


        [Test]
        public void ValidMasterPasswordTest() {
            Assert.That(Manager.ValidMasterPassword("yo boii"));
            Assert.That(!Manager.ValidMasterPassword("yo homie"));
        }

        [Test]
        public void StartAndEndElectionTest() {
            Assert.That(!Manager.ElectionInProgress);
            Manager.StartElection();
            Assert.That(Manager.ElectionInProgress);
            Manager.EndElection();
            Assert.That(!Manager.ElectionInProgress);
        }

        [Test]
        public void AddAndRemovePeerTest() {
            Assert.That(!Manager.Peers.ContainsKey(Peer4.Address));
            Manager.AddPeer(Peer4.Address, Peer4.Crypto.Keys.Item1);
            Assert.That(Manager.Peers.ContainsKey(Peer4.Address));
            Manager.RemovePeer(Peer4.Address);
            Assert.That(!Manager.Peers.ContainsKey(Peer4.Address));
        }

        [Test]
        public void EnoughStationsTest() {
            AsyncManagerAnnounce(() => Assert.That(Manager.EnoughStations));
        }

        [Test]
        public void AnnounceStartAndEndElectionTest() {
            Assert.That(!(Manager.ElectionInProgress && Peer1.ElectionInProgress && Peer2.ElectionInProgress && Peer3.ElectionInProgress));
            AsyncManagerAnnounce(() => Manager.AnnounceStartElection());
            Assert.That(Manager.ElectionInProgress && Peer1.ElectionInProgress && Peer2.ElectionInProgress && Peer3.ElectionInProgress);
            AsyncManagerAnnounce(() => Manager.AnnounceEndElection());
            Assert.That(!(Manager.ElectionInProgress && Peer1.ElectionInProgress && Peer2.ElectionInProgress && Peer3.ElectionInProgress));
        }

        [Test]
        public void BallotReceivedAndRevoked() {
            var vn = new VoterNumber(250000);
            var cpr = new CPR(2312881234);
            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.Unavailable);
            Peer1.Database.Import(new List<EncryptedVoterData> { new EncryptedVoterData(new CipherText(Peer1.Crypto.AsymmetricEncrypt(Bytes.From(vn.Value), Peer1.Crypto.VoterDataEncryptionKey)), new CipherText(Peer1.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value), Peer1.Crypto.VoterDataEncryptionKey)), new CipherText(Peer1.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value + (uint)BallotStatus.NotReceived), Peer1.Crypto.VoterDataEncryptionKey))) });

            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.NotReceived);
            Peer1.BallotReceived(vn, cpr);
            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.Received);
            Peer1.RevokeBallot(vn, cpr);
            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.NotReceived);

            Assert.That(Peer1.Database[cpr, "yo boii"] == BallotStatus.NotReceived);
            Peer1.BallotReceived(cpr, "yo boii");
            Assert.That(Peer1.Database[cpr, "yo boii"] == BallotStatus.Received);
            Peer1.RevokeBallot(cpr, "yo boii");
            Assert.That(Peer1.Database[cpr, "yo boii"] == BallotStatus.NotReceived);
        }


        [Test]
        public void ElectNewManager() {
            Assert.That(Peer1.Manager.Equals(Manager.Address));
            AsyncManagerAnnounce(() => {
                //"Have" to send bogus command to kill the listener.
                // ReSharper disable ReturnValueOfPureMethodIsNotUsed
                Manager.StationActive(Peer1.Address);
                // ReSharper restore ReturnValueOfPureMethodIsNotUsed
                Peer1.ElectNewManager();
            });
            Assert.That(!Peer1.Manager.Equals(Manager.Address));
        }

        [Test]
        public void AnnounceAddAndRemovePeerTest() {
            Manager.StartListening();
            Peer1.StartListening();
            Peer2.StartListening();
            Peer3.StartListening();
            Peer4.StartListening();
            Assert.That(!Manager.Peers.ContainsKey(Peer4.Address) && !Peer1.Peers.ContainsKey(Peer4.Address) && !Peer2.Peers.ContainsKey(Peer4.Address) && !Peer3.Peers.ContainsKey(Peer4.Address));
            Manager.AnnounceAddPeer(Peer4.Address, Peer4.Crypto.Keys.Item1);
            Manager.AddPeer(Peer4.Address, Peer4.Crypto.Keys.Item1);
            Thread.Sleep(3000);
            Assert.That(Manager.Peers.ContainsKey(Peer4.Address) && Peer1.Peers.ContainsKey(Peer4.Address) && Peer2.Peers.ContainsKey(Peer4.Address) && Peer3.Peers.ContainsKey(Peer4.Address));
            Manager.AnnounceRemovePeer(Peer4.Address);
            Thread.Sleep(3000);
            Assert.That(!Manager.Peers.ContainsKey(Peer4.Address) && !Peer1.Peers.ContainsKey(Peer4.Address) && !Peer2.Peers.ContainsKey(Peer4.Address) && !Peer3.Peers.ContainsKey(Peer4.Address));
        }

        [Test]
        public void DiscoverPeersTest() {
            var peers = Manager.DiscoverPeers().ToArray();
            Assert.That(peers.Count() >= 0);
            foreach(var peer in peers) {
                Console.WriteLine(peer);
            }
        }

        [Test]
        public void RequestBallotAndAnnounceBallotReceivedAndRevokedTest() {
            var vn = new VoterNumber(250000);
            var cpr = new CPR(2312881234);
            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.Unavailable);
            Assert.That(Peer2.Database[vn, cpr] == BallotStatus.Unavailable);
            Assert.That(Peer3.Database[vn, cpr] == BallotStatus.Unavailable);
            Assert.That(Manager.Database[vn, cpr] == BallotStatus.Unavailable);
            var data = new List<EncryptedVoterData> { new EncryptedVoterData(new CipherText(Peer1.Crypto.AsymmetricEncrypt(Bytes.From(vn.Value), Peer1.Crypto.VoterDataEncryptionKey)), new CipherText(Peer1.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value), Peer1.Crypto.VoterDataEncryptionKey)), new CipherText(Peer1.Crypto.AsymmetricEncrypt(Bytes.From(cpr.Value + (uint)BallotStatus.NotReceived), Peer1.Crypto.VoterDataEncryptionKey))) };
            Peer1.Database.Import(data);
            Peer2.Database.Import(data);
            Peer3.Database.Import(data);
            Manager.Database.Import(data);


            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Peer2.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Peer3.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Manager.Database[vn, cpr] == BallotStatus.NotReceived);
            var managerListenerResult = ManagerListener.BeginInvoke(null, null);
            AsyncManagerAnnounce(() => Peer1.RequestBallot(vn, cpr));
            ManagerListener.EndInvoke(managerListenerResult);
            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.Received);
            Assert.That(Peer2.Database[vn, cpr] == BallotStatus.Received);
            Assert.That(Peer3.Database[vn, cpr] == BallotStatus.Received);
            Assert.That(Manager.Database[vn, cpr] == BallotStatus.Received);
            AsyncManagerAnnounce(() => Manager.AnnounceRevokeBallot(vn, cpr));
            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Peer2.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Peer3.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Manager.Database[vn, cpr] == BallotStatus.NotReceived);

            managerListenerResult = ManagerListener.BeginInvoke(null, null);
            AsyncManagerAnnounce(() => Peer1.RequestBallot(cpr, "yo boii"));
            ManagerListener.EndInvoke(managerListenerResult);
            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.Received);
            Assert.That(Peer2.Database[vn, cpr] == BallotStatus.Received);
            Assert.That(Peer3.Database[vn, cpr] == BallotStatus.Received);
            Assert.That(Manager.Database[vn, cpr] == BallotStatus.Received);

            AsyncManagerAnnounce(() => Manager.AnnounceRevokeBallot(cpr, "yo boii"));
            Assert.That(Peer1.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Peer2.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Peer3.Database[vn, cpr] == BallotStatus.NotReceived);
            Assert.That(Manager.Database[vn, cpr] == BallotStatus.NotReceived);
        }

        [Test]
        public void PromoteNewManagerTest() {
            var oldManager = Manager.Address;
            var newManager = Peer1.Address;
            Assert.That(Manager.Manager.Equals(oldManager) && Peer1.Manager.Equals(oldManager) && Peer2.Manager.Equals(oldManager) && Peer3.Manager.Equals(oldManager));
            Assert.That(Manager.IsManager && !Peer1.IsManager && !Peer2.IsManager && !Peer3.IsManager);
            AsyncManagerAnnounce(() => Manager.PromoteNewManager(newManager));
            Assert.That(!Manager.IsManager && Peer1.IsManager && !Peer2.IsManager && !Peer3.IsManager);
            Assert.That(Manager.Manager.Equals(newManager) && Peer1.Manager.Equals(newManager) && Peer2.Manager.Equals(newManager) && Peer3.Manager.Equals(newManager));
        }

        private void AsyncManagerAnnounce(Action invoke) {
            var peer1ListenerResult = Peer1Listener.BeginInvoke(null, null);
            var peer2ListenerResult = Peer2Listener.BeginInvoke(null, null);
            var peer3ListenerResult = Peer3Listener.BeginInvoke(null, null);
            //Waste some CPU time while the thread hopefully starts...
            var c = 0;
            while(c < 5000000)
                c++;
            Console.WriteLine(c);
            invoke();

            Peer1Listener.EndInvoke(peer1ListenerResult);
            Peer2Listener.EndInvoke(peer2ListenerResult);
            Peer3Listener.EndInvoke(peer3ListenerResult);
        }

        [Test]
        public void ListenerTest() {
            Manager.StartListening();
            //Waste some CPU time while the thread hopefully starts...
            var c = 0;
            while(c < 500000)
                c++;
            Console.WriteLine(c);
            Assert.That(Peer1.StationActive(Manager.Address));
            Assert.That(Peer1.StationActive(Manager.Address));
            Manager.StopListening();
            Assert.That(!Peer1.StationActive(Manager.Address));
        }

        [Test]
        public void ExchangePublicKeysTest() {
            var ui = new TestUi();
            using(var manager = new Station(ui, "dataEncryption.key", "sup homey", 63554, "ExchangePublicKeysTestManagerVoters.sqlite", "ExchangePublicKeysTestManagerLog.sqlite"))
            using(var station = new Station(ui, 63555, "ExchangePublicKeysTestStationVoters.sqlite")) {
                Assert.That(!manager.Peers.ContainsKey(station.Address));
                Assert.That(!station.Peers.ContainsKey(manager.Address));
                manager.ExchangePublicKeys(station.Address);
                //Wait some time while they synchronize.
                Thread.Sleep(3000);
                Assert.That(manager.Peers.ContainsKey(station.Address));
                Assert.That(station.Peers.ContainsKey(manager.Address));
            }
            File.Delete("ExchangePublicKeysTestManagerVoters.sqlite");
            File.Delete("ExchangePublicKeysTestStationVoters.sqlite");
            File.Delete("ExchangePublicKeysTestManagerLog.sqlite");
        }

        [Test]
        public void StartNewManagerElectionTest() {
            var ui = new TestUi();
            using(var manager = new Station(ui, "dataEncryption.key", "sup homey", 63554, "ExchangePublicKeysTestManagerVoters.sqlite", "ExchangePublicKeysTestManagerLog.sqlite")) {
                var pswd = manager.Crypto.VoterDataEncryptionKey;
                using(var station = new Station(ui, 63555, "ExchangePublicKeysTestStationVoters.sqlite") { Manager = manager.Address, Crypto = { VoterDataEncryptionKey = pswd }, MasterPassword = manager.MasterPassword })
                using(var station2 = new Station(ui, 63556, "ExchangePublicKeysTestStation2Voters.sqlite") { Manager = manager.Address, Crypto = { VoterDataEncryptionKey = pswd }, MasterPassword = manager.MasterPassword }) {
                    station.Logger = new Logger(station, "ExchangePublicKeysTestStationLog.sqlite");
                    station2.Logger = new Logger(station2, "ExchangePublicKeysTestStation2Log.sqlite");
                    Assert.That(station.Manager.Equals(manager.Address));
                    Assert.That(station2.Manager.Equals(manager.Address));
                    Assert.That(station2.Manager.Equals(station.Manager));

                    station.AddPeer(manager.Address, manager.Crypto.Keys.Item1);
                    station.AddPeer(station2.Address, station2.Crypto.Keys.Item1);
                    station2.AddPeer(manager.Address, manager.Crypto.Keys.Item1);
                    station2.AddPeer(station.Address, station.Crypto.Keys.Item1);

                    manager.StopListening();
                    station.StartNewManagerElection();
                    Thread.Sleep(5000);
                    Assert.That(!station.Manager.Equals(manager.Address));
                    Assert.That(!station2.Manager.Equals(manager.Address));
                    Assert.That(station2.Manager.Equals(station.Manager));
                }
            }
            File.Delete("ExchangePublicKeysTestManagerVoters.sqlite");
            File.Delete("ExchangePublicKeysTestStationVoters.sqlite");
            File.Delete("ExchangePublicKeysTestStation2Voters.sqlite");
            File.Delete("ExchangePublicKeysTestManagerLog.sqlite");
            File.Delete("ExchangePublicKeysTestStationLog.sqlite");
            File.Delete("ExchangePublicKeysTestStation2Log.sqlite");
        }
    }
}