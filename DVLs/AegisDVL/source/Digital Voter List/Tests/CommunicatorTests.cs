using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Threading;
using Aegis_DVL;
using Aegis_DVL.Commands;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Logging;
using Aegis_DVL.Util;
using Enumerable = System.Linq.Enumerable;
using NUnit.Framework;

namespace Tests {
    /// <summary>
    /// Test the communicator.
    /// </summary>
    [TestFixture]
    public class CommunicatorTests {
        public Station Sender { get; private set; }
        public Station Receiver { get; private set; }
        public IPEndPoint BadEndPoint { get; private set; }
        private Stopwatch _timer;
        public delegate void ReceiverListener();

        /// <summary>
        /// SetUp test helper properties.
        /// </summary>
        [SetUp]
        public void SetUp() {
            var ui = new TestUi();
            Sender = new Station(ui, "dataEncryption.key", "yo boii", 62345, "CommunicatorTestsSenderVoters.sqlite", "CommunicatorTestsSenderLog.sqlite");
            Receiver = new Station(ui, 62346, "CommunicatorTestsReceiverVoters.sqlite") {
                Manager = Sender.Address,
                Crypto = { VoterDataEncryptionKey = Sender.Crypto.VoterDataEncryptionKey },
                MasterPassword = Sender.Crypto.Hash(Bytes.From("_½æøåÆÅØ§.^\\,QBsa(/YHh*^#3£()cZ?\\}`|`´ '*jJxCvZ;;;<><aQ\\ ><yo boii"))
            };
            //Receiver.Logger = new Logger(Receiver, "CommunicatorTestsReceiverLog.sqlite");
            Sender.StopListening();
            Receiver.StopListening();

            BadEndPoint = new IPEndPoint(Receiver.Address.Address, Receiver.Address.Port + 5);
            _timer = new Stopwatch();
            _timer.Start();
        }

        [TearDown]
        public void TearDown() {
            Console.WriteLine("Test duration: {0}", _timer.ElapsedMilliseconds);
            _timer = null;
            Sender.Dispose();
            Receiver.Dispose();
            Sender = null;
            Receiver = null;
            try {
                File.Delete("CommunicatorTestsSenderVoters.sqlite");
                File.Delete("CommunicatorTestsReceiverVoters.sqlite");
                File.Delete("CommunicatorTestsSenderLog.sqlite");
                File.Delete("CommunicatorTestsReceiverLog.sqlite");
            }
            catch(IOException e) {
                Console.WriteLine(e.Message);
                Console.WriteLine(e.StackTrace);
            }
        }

        [Test]
        public void BigCommandSendAndReceiveTest() {
            var voters = Enumerable.Range(0, 500).Select(x =>
                new Tuple<string, string, uint, uint>("Bob Bobbersen nummer " + x, "Køge Sportshal", (uint)x + 250000, (uint)x + 2312881234));

            var crypto = Sender.Crypto;
            var key = crypto.VoterDataEncryptionKey;

            var encryptedVoters = voters.Select(v =>
                new EncryptedVoterData(
                    new CipherText(crypto.AsymmetricEncrypt(Bytes.From(v.Item3), key)),
                    new CipherText(crypto.AsymmetricEncrypt(Bytes.From(v.Item4), key)),
                    new CipherText(crypto.AsymmetricEncrypt(Bytes.From((uint)BallotStatus.NotReceived), key))));
            Sender.Database.Import(encryptedVoters);

            using(var receiver = new Station(new TestUi(), 62347, "BigCommandSendAndReceiveTestVoters.sqlite") { Manager = Sender.Address }) {
                receiver.StopListening();
                Sender.AddPeer(receiver.Address, receiver.Crypto.Keys.Item1);
                receiver.AddPeer(Sender.Address, Sender.Crypto.Keys.Item1);
                var receiverListener = new ReceiverListener(receiver.Communicator.ReceiveAndHandle);
                var receiverResult = receiverListener.BeginInvoke(null, null);

                Assert.That(!receiver.Database.AllData.Any());
                var sync = new SyncCommand(Sender);
                Console.WriteLine(Bytes.From(sync).Length);
                Sender.Communicator.Send(sync, receiver.Address);
                receiverListener.EndInvoke(receiverResult);

                Assert.That(receiver.Database.AllData.Count() == 500);
            }
            File.Delete("BigCommandSendAndReceiveTestVoters.sqlite");
        }

        /// <summary>
        /// Test whether the Send and ReceiveAndHandle methods works.
        /// </summary>
        [Test]
        public void SendAndReceiveAndHandleTest() {
            Sender.AddPeer(Receiver.Address, Receiver.Crypto.Keys.Item1);

            var receiver = new ReceiverListener(Receiver.Communicator.ReceiveAndHandle);

            //Test whether the system is able to send and receive a basic command
            var receiverResult = receiver.BeginInvoke(null, null);
            //Waste some CPU time while the thread hopefully starts...
            var c = 0;
            while(c < 500000)
                c++;
            Console.WriteLine(c);
            Assert.That(Sender.StationActive(Receiver.Address));
            receiver.EndInvoke(receiverResult);

            receiverResult = receiver.BeginInvoke(null, null);

            Sender.Communicator.Send(new EndElectionCommand(Sender.Address), Receiver.Address);
            var result = receiverResult;
            Assert.Throws<TheOnlyException>(() => receiver.EndInvoke(result));


            receiverResult = receiver.BeginInvoke(null, null);
            using(var client = new TcpClient()) {
                client.Connect(Receiver.Address);
                using(var stream = client.GetStream()) {
                    var msg = Bytes.From(new EndElectionCommand(Sender.Address));
                    stream.Write(msg, 0, msg.Length);
                }
            }

            Assert.Throws<TheOnlyException>(() => receiver.EndInvoke(receiverResult));

            //Send a command that will be wrapped in a CryptoCommand that wont be received, and that the receiver is removed from the peer-list
            Assert.That(Sender.Peers.ContainsKey(Receiver.Address));
            Sender.Communicator.Send(new ElectNewManagerCommand(Sender.Address), Receiver.Address);
            Assert.That(!Sender.Peers.ContainsKey(Receiver.Address));


            //Test bad endpoint
            Assert.That(!Sender.StationActive(BadEndPoint));
        }

        [Test]
        public void ReceiverFailureTest() {
            var ui = new TestUi();
            using(var manager = new Station(ui, "dataEncryption.key", "yo boii", 60000, "CommunicatorTestsReceiverFailureTestManagerVoters.sqlite", "CommunicatorTestsReceiverFailureTestManagerLog.sqlite")) {
                var pswd = manager.Crypto.Hash(Bytes.From("_½æøåÆÅØ§.^\\,QBsa(/YHh*^#3£()cZ?\\}`|`´ '*jJxCvZ;;;<><aQ\\ ><yo boii"));
                using(var peer1 = new Station(ui, 61000, "CommunicatorTestsReceiverFailureTestPeer1Voters.sqlite") {
                    Manager = manager.Address,
                    MasterPassword = pswd,
                    Crypto = { VoterDataEncryptionKey = manager.Crypto.VoterDataEncryptionKey }
                })
                using(var peer2 = new Station(ui, 62000, "CommunicatorTestsReceiverFailureTestPeer2Voters.sqlite") {
                    Manager = manager.Address,
                    MasterPassword = pswd,
                    Crypto = { VoterDataEncryptionKey = manager.Crypto.VoterDataEncryptionKey }
                })
                using(var peer3 = new Station(ui, 63000, "CommunicatorTestsReceiverFailureTestPeer3Voters.sqlite") {
                    Manager = manager.Address,
                    MasterPassword = pswd,
                    Crypto = { VoterDataEncryptionKey = manager.Crypto.VoterDataEncryptionKey }
                }) {
                    peer1.Logger = new Logger(peer1, "CommunicatorTestsReceiverFailureTestPeer1log.sqlite");
                    peer2.Logger = new Logger(peer2, "CommunicatorTestsReceiverFailureTestPeer2log.sqlite");
                    peer3.Logger = new Logger(peer3, "CommunicatorTestsReceiverFailureTestPeer3log.sqlite");
                    peer1.StopListening();

                    manager.AddPeer(peer1.Address, peer1.Crypto.Keys.Item1);
                    manager.AddPeer(peer2.Address, peer2.Crypto.Keys.Item1);
                    manager.AddPeer(peer3.Address, peer3.Crypto.Keys.Item1);

                    peer1.AddPeer(peer2.Address, peer2.Crypto.Keys.Item1);
                    peer1.AddPeer(peer3.Address, peer3.Crypto.Keys.Item1);
                    peer1.AddPeer(manager.Address, manager.Crypto.Keys.Item1);

                    peer2.AddPeer(peer1.Address, peer1.Crypto.Keys.Item1);
                    peer2.AddPeer(peer3.Address, peer3.Crypto.Keys.Item1);
                    peer2.AddPeer(manager.Address, manager.Crypto.Keys.Item1);

                    peer3.AddPeer(peer1.Address, peer1.Crypto.Keys.Item1);
                    peer3.AddPeer(peer2.Address, peer2.Crypto.Keys.Item1);
                    peer3.AddPeer(manager.Address, manager.Crypto.Keys.Item1);

                    Assert.That(manager.IsManager);
                    Assert.That(!peer1.IsManager);
                    Assert.That(!peer2.IsManager);
                    Assert.That(!peer3.IsManager);

                    
                    Assert.That(peer2.Peers.ContainsKey(peer1.Address) && !peer2.ElectionInProgress);
                    Assert.That(peer3.Peers.ContainsKey(peer1.Address) && !peer3.ElectionInProgress);
                    Assert.That(manager.Peers.ContainsKey(peer1.Address) && !manager.ElectionInProgress);

                    
                    manager.Communicator.Send(new StartElectionCommand(manager.Address), peer1.Address);
                    
                    Thread.Sleep(5000);
                    Assert.That(!peer2.Peers.ContainsKey(peer1.Address));
                    Assert.That(!peer3.Peers.ContainsKey(peer1.Address));
                    Assert.That(!manager.Peers.ContainsKey(peer1.Address));
                }
            }
            File.Delete("CommunicatorTestsReceiverFailureTestManagerVoters.sqlite");
            File.Delete("CommunicatorTestsReceiverFailureTestPeer1Voters.sqlite");
            File.Delete("CommunicatorTestsReceiverFailureTestPeer2Voters.sqlite");
            File.Delete("CommunicatorTestsReceiverFailureTestPeer3Voters.sqlite");
            File.Delete("CommunicatorTestsReceiverFailureTestManagerLog.sqlite");
        }

        [Test]
        public void DiscoverNetworkMachinesTest() {
            var machines = Sender.Communicator.DiscoverNetworkMachines();
            Assert.That(machines != null);
            machines = machines.ToArray();
            var count = 0;
            foreach(var machine in machines) {
                count++;
                Console.WriteLine(machine);
            }
            Assert.That(count >= 0);
        }

        [Test]
        public void IsListeningTest() {
            Assert.That(!Sender.Communicator.IsListening(Sender.Address));
            Sender.StartListening();
            //Waste some CPU time while the thread hopefully starts...
            var c = 0;
            while(c < 500000)
                c++;
            Console.WriteLine(c);
            Assert.That(Sender.Communicator.IsListening(Sender.Address));
        }
    }
}
