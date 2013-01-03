using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Threading;
using Aegis_DVL.Commands;
using Aegis_DVL.Communication;
using Aegis_DVL.Cryptography;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Database;
using Aegis_DVL.Logging;
using Aegis_DVL.Util;

namespace Aegis_DVL {
    /// <summary>
    /// A station is a client-machine that communicates with its manager, and provides a graphical user interface for voters to use when requesting a ballot.
    /// A station can also be the manager. A manager manages the various stations, and handles synchronization of the data.
    /// It also has elevated rights compared to a station, and can for example manually mark a voter as having been handed a ballot (in case he lost his voter card, or the like).
    /// </summary>
    public class Station : IDisposable {
        #region Private fields
        private bool _isDisposed;
        private IPEndPoint _manager;
        private Thread _listenerThread;
        private byte[] _masterPassword;
        private ICrypto _crypto;
        private ILogger _logger;

        #endregion

        #region Properties
        /// <summary>
        /// What is my address?
        /// </summary>
        public IPEndPoint Address { [Pure] get; private set; }

        /// <summary>
        /// Who is the manager?
        /// This station is now the manager!
        /// </summary>
        public IPEndPoint Manager {
            [Pure]
            get { return _manager; }
            set {
                Contract.Requires(value != null);
                Contract.Ensures(Manager.Equals(value));
                _manager = value;
            }
        }

        /// <summary>
        /// Is there enough active stations in the group to continue operations?
        /// </summary>
        public bool EnoughStations { [Pure] get { return Peers.Keys.Count(StationActive) > 0; } }

        /// <summary>
        /// What is the status of the election?
        /// </summary>
        public bool ElectionInProgress { [Pure] get; private set; }

        /// <summary>
        /// Who are my peers?
        /// </summary>
        public SortedDictionary<IPEndPoint, AsymmetricKey> Peers { [Pure] get; private set; }

        /// <summary>
        /// How can I manipulate my database?
        /// </summary>
        public IDatabase Database { [Pure] get; private set; }

        /// <summary>
        /// How can I communicate with my group?
        /// </summary>
        public ICommunicator Communicator { [Pure] get; private set; }

        /// <summary>
        /// How can I encrypt messages?
        /// This is how you encrypt messages!
        /// </summary>
        public ICrypto Crypto {
            [Pure]
            get { return _crypto; }
            set {
                Contract.Requires(value != null);
                Contract.Ensures(Equals(Crypto, value));
                _crypto = value;
            }
        }

        /// <summary>
        /// How can I log messages?
        /// This is how you log messages!
        /// </summary>
        public ILogger Logger {
            [Pure]
            get { return _logger; }
            set {
                Contract.Requires(value != null);
                Contract.Ensures(Equals(Logger, value));
                _logger = value;
            }
        }

        /// <summary>
        /// How can the user interact with me?
        /// </summary>
        public IDvlUi UI { [Pure] get; private set; }

        /// <summary>
        /// Am I the manager?
        /// </summary>
        public bool IsManager { [Pure] get { return Address.Equals(Manager); } }

        public bool Listening { get; private set; }

        /// <summary>
        /// What is the master password?
        /// The master password is this!
        /// </summary>
        public byte[] MasterPassword {
            set {
                Contract.Requires(value != null);
                Contract.Requires(MasterPassword == null);
                Contract.Ensures(Equals(MasterPassword, value));
                _masterPassword = value;
                value.ToFile("Master.pw");
            }
            get { return _masterPassword; }
        }
        #endregion

        #region Pure Methods
        /// <summary>
        /// Is this station active?
        /// </summary>
        /// <param name="target">The station to check.</param>
        /// <returns>True if the station is active, otherwise false.</returns>
        [Pure]
        public bool StationActive(IPEndPoint target) {
            Contract.Requires(target != null);
            return Communicator.IsListening(target);
        }

        /// <summary>
        /// What machines on the network respond that they have the digital voter list software running?
        /// </summary>
        [Pure]
        public IEnumerable<IPEndPoint> DiscoverPeers() {
            Contract.Ensures(Contract.Result<IEnumerable<IPEndPoint>>() != null);
            Contract.Ensures(Contract.Result<IEnumerable<IPEndPoint>>().All(x => x != null));
            return Communicator.DiscoverNetworkMachines().Where(address => !address.Equals(Address));
        }

        /// <summary>
        /// Is this string the masterpassword?
        /// </summary>
        /// <param name="password">The password to check.</param>
        /// <returns>True if the password is identical to the masterpassword, false otherwise.</returns>
        [Pure]
        public bool ValidMasterPassword(string password) {
            Contract.Requires(password != null);
            return _masterPassword != null && _masterPassword.SequenceEqual(Crypto.Hash(Bytes.From("_½æøåÆÅØ§.^\\,QBsa(/YHh*^#3£()cZ?\\}`|`´ '*jJxCvZ;;;<><aQ\\ ><" + password)));
        }
        #endregion

        #region Constructors
        /// <summary>
        /// Can I have a new Station that is the manager?
        /// </summary>
        /// <param name="ui">A reference to the UI.</param>
        /// <param name="voterDataEncryptionKey">The AsymmetricKey used for encrypting the data at this election venue.</param>
        /// <param name="masterpassword">The masterpassword known only by the election secretary.</param>
        /// <param name="port">The network port the station is communicating over. Defaults to 62000.</param>
        /// <param name="voterDbName">The name of the voter database. Defaults to Voters.sqlite.</param>
        /// <param name="logName">The name of the logging database. Defaults to Log.sqlite.</param>
        public Station(IDvlUi ui, AsymmetricKey voterDataEncryptionKey, string masterpassword, int port = 62000, string voterDbName = "Voters.sqlite", string logName = "Log.sqlite")
            : this(ui, port, voterDbName) {
            Contract.Requires(ui != null);
            Contract.Requires(masterpassword != null);
            Contract.Requires(voterDbName != null);
            Contract.Requires(logName != null);

            Crypto = new Crypto(voterDataEncryptionKey);
            MasterPassword = Crypto.Hash(Bytes.From("_½æøåÆÅØ§.^\\,QBsa(/YHh*^#3£()cZ?\\}`|`´ '*jJxCvZ;;;<><aQ\\ ><" + masterpassword));
            Logger = new Logger(this, logName);
            Manager = Address;
            Logger.Log("Manager initialized", Level.Info);
        }

        /// <summary>
        /// Can I have a new Station that is the manager?
        /// </summary>
        /// <param name="ui">A reference to the UI.</param>
        /// <param name="keyPath">The patch to the key-file.</param>
        /// <param name="masterPassword">The masterpassword known only by the election secretary.</param>
        /// <param name="port">The network port the station is communicating over. Defaults to 62000.</param>
        /// <param name="voterDbName">The name of the voter database. Defaults to Voters.sqlite.</param>
        /// <param name="logName">The name of the logging database. Defaults to Log.sqlite.</param>
        public Station(IDvlUi ui, string keyPath, string masterPassword, int port = 62000, string voterDbName = "Voters.sqlite", string logName = "Log.sqlite")
            : this(ui, new AsymmetricKey(Bytes.FromFile(keyPath).ToKey()), masterPassword, port, voterDbName, logName) {
            Contract.Requires(ui != null);
            Contract.Requires(keyPath != null);
            Contract.Requires(File.Exists(keyPath));
            Contract.Requires(voterDbName != null);
            Contract.Requires(logName != null);
        }

        /// <summary>
        /// Can I have a new Station?
        /// </summary>
        /// <param name="ui">A reference to the UI.</param>
        /// <param name="port">The port the station should listen to. Defaults to 62000.</param>
        /// <param name="databaseFile">The name of the database file.</param>
        public Station(IDvlUi ui, int port = 62000, string databaseFile = "Voters.sqlite") {
            Contract.Requires(ui != null);
            Contract.Requires(databaseFile != null);

            Peers = new SortedDictionary<IPEndPoint, AsymmetricKey>(new IPEndPointComparer());
            ElectionInProgress = false;
            Address = new IPEndPoint(Dns.GetHostEntry(Dns.GetHostName()).AddressList.First(ip => ip.AddressFamily == AddressFamily.InterNetwork), port);
            Database = new SqLiteDatabase(this, databaseFile);
            Communicator = new Communicator(this);
            UI = ui;
            Crypto = new Crypto();
            StartListening();
        }
        #endregion

        #region Methods
        /// <summary>
        /// The system is compromised, notify everyone and shut down the election!
        /// </summary>
        public void ShutDownElection() {
            if(Logger != null)
                Logger.Log("Compromised system, shutting down election.", Level.Fatal);
            Peers.Keys.ForEach(peer => Communicator.Send(new ShutDownElectionCommand(Address), peer));
            UI.Shutdown();
            throw new TheOnlyException();
        }

        /// <summary>
        /// Exchange public keys with this machine!
        /// </summary>
        /// <param name="target">The address of the machine to exchange public keys with.</param>
        public void ExchangePublicKeys(IPEndPoint target) {
            Contract.Requires(target != null);
            Contract.Requires(StationActive(target));
            Communicator.Send(new PublicKeyExchangeCommand(this), target);
            if(Logger != null)
                Logger.Log("Exchanging public keys with " + target, Level.Info);
        }

        /// <summary>
        /// Start listening to other stations!
        /// </summary>
        public void StartListening() {
            Contract.Requires(!Listening);
            Contract.Ensures(Listening);
            Listening = true;
            _listenerThread = new Thread(LoopListen);
            _listenerThread.SetApartmentState(ApartmentState.STA);
            _listenerThread.Start();
            while(!StationActive(Address))
                ;
        }

        /// <summary>
        /// Stop listening to other stations!
        /// </summary>
        public void StopListening() {
            Contract.Requires(Listening);
            Contract.Ensures(!Listening);
            Listening = false;
            while(StationActive(Address))
                ;
            if(_listenerThread != null)
                _listenerThread.Abort();
            _listenerThread = null;
            if(Logger != null)
                Logger.Log("Stopped listening", Level.Info);
        }

        private void LoopListen() {
            while(Listening)
                Communicator.ReceiveAndHandle();
        }

        /// <summary>
        /// Start the election!
        /// </summary>
        public void StartElection() {
            Contract.Requires(!ElectionInProgress);
            Contract.Ensures(ElectionInProgress);
            ElectionInProgress = true;
            if(Logger != null)
                Logger.Log("Election started", Level.Info);
        }

        /// <summary>
        /// End the election
        /// </summary>
        public void EndElection() {
            Contract.Requires(ElectionInProgress);
            Contract.Ensures(!ElectionInProgress);
            ElectionInProgress = false;
            if(Logger != null)
                Logger.Log("Election ended", Level.Info);
        }

        /// <summary>
        /// Add this station to the group!
        /// </summary>
        /// <param name="peer">The address of the station to add.</param>
        /// <param name="peerPublicAsymmetricKey">The public AsymmetricKey of the station to add.</param>
        public void AddPeer(IPEndPoint peer, AsymmetricKey peerPublicAsymmetricKey) {
            Contract.Requires(peer != null);
            Contract.Requires(!Peers.ContainsKey(peer));
            Contract.Ensures(Peers.ContainsKey(peer));
            Peers.Add(peer, peerPublicAsymmetricKey);
            if(EnoughStations)
                UI.EnoughPeers();
            if(Logger != null)
                Logger.Log("Peer added: " + peer, Level.Info);
        }

        /// <summary>
        /// Remove this station from the group!
        /// </summary>
        /// <param name="peer">The address of the station to remove.</param>
        public void RemovePeer(IPEndPoint peer) {
            Contract.Requires(peer != null);
            Contract.Requires(Peers.ContainsKey(peer));
            Contract.Ensures(!Peers.ContainsKey(peer));
            Peers.Remove(peer);
            if(!EnoughStations)
                UI.NotEnoughPeers();
            if(Logger != null)
                Logger.Log("Peer removed: " + peer, Level.Info);
        }

        /// <summary>
        /// Start election of a new manager!
        /// </summary>
        public void StartNewManagerElection() {
            ElectNewManager();
            Peers.Keys.ForEach(peer => Communicator.Send(new ElectNewManagerCommand(Address), peer));
            if(Logger != null)
                Logger.Log("Announced that a new manager should be elected", Level.Warn);
        }

        /// <summary>
        /// Elect a new manager!
        /// </summary>
        public void ElectNewManager() {
            Contract.Requires(!StationActive(Manager));
            Contract.Ensures(!Manager.Equals(Contract.OldValue(Manager)));
            RemovePeer(Manager);
            var candidates = new SortedSet<IPEndPoint>(new IPEndPointComparer()) { Address };
            Peers.Keys.Where(StationActive).ForEach(candidate => candidates.Add(candidate));
            Manager = candidates.First();
            if(IsManager)
                UI.IsNowManager();
            if(Logger != null)
                Logger.Log("Elected new manager: " + Manager, Level.Warn);
        }

        /// <summary>
        /// Request a ballot for this voter!
        /// </summary>
        /// <param name="voterNumber">The voternumber to request a ballot for.</param>
        /// <param name="cpr">The CPR number to request a ballot for.</param>
        public void RequestBallot(VoterNumber voterNumber, CPR cpr) {
            Contract.Requires(Database[voterNumber, cpr] == BallotStatus.NotReceived);
            Communicator.Send(new RequestBallotCommand(Address, voterNumber, cpr), Manager);
            if(Logger != null)
                Logger.Log("Requesting ballot for: voternumber=" + voterNumber + "; CPR=" + cpr, Level.Info);
        }

        /// <summary>
        /// Request a ballot for this voter!
        /// </summary>
        /// <param name="cpr">The CPR number to request a ballot for.</param>
        /// <param name="password">The masterpassword.</param>
        public void RequestBallot(CPR cpr, string password) {
            Contract.Requires(password != null);
            Contract.Requires(ValidMasterPassword(password));
            Contract.Requires(Database[cpr, password] == BallotStatus.NotReceived);
            Communicator.Send(new RequestBallotCPROnlyCommand(Address, cpr, password), Manager);
            if(Logger != null)
                Logger.Log("Requesting ballot with masterpassword for: CPR=" + cpr, Level.Info);
        }

        /// <summary>
        /// This voter received a ballot!
        /// </summary>
        /// <param name="voterNumber">The voternumber to request a ballot for.</param>
        /// <param name="cpr">The CPR number to request a ballot for.</param>
        public void BallotReceived(VoterNumber voterNumber, CPR cpr) {
            Contract.Requires(Database[voterNumber, cpr] == BallotStatus.NotReceived);
            Contract.Ensures(Database[voterNumber, cpr] == BallotStatus.Received);
            Database[voterNumber, cpr] = BallotStatus.Received;
            if(Logger != null)
                Logger.Log("Marking voternumber=" + voterNumber + "; CPR=" + cpr + " as having received a ballot.", Level.Info);
        }

        /// <summary>
        /// This voter received a ballot!
        /// </summary>
        /// <param name="cpr">The CPR number to request a ballot for.</param>
        /// <param name="password">The masterpassword.</param>
        public void BallotReceived(CPR cpr, string password) {
            Contract.Requires(password != null);
            Contract.Requires(ValidMasterPassword(password));
            Contract.Requires(Database[cpr, password] == BallotStatus.NotReceived);
            Contract.Ensures(Database[cpr, password] == BallotStatus.Received);
            Database[cpr, password] = BallotStatus.Received;
            if(Logger != null)
                Logger.Log("Marking CPR=" + cpr + " with masterpassword as having received a ballot.", Level.Info);
        }

        /// <summary>
        /// Revoke this ballot!
        /// </summary>
        /// <param name="voterNumber">The voternumber to revoke a ballot for.</param>
        /// <param name="cpr">The CPR number to revoke a ballot for.</param>
        public void RevokeBallot(VoterNumber voterNumber, CPR cpr) {
            Contract.Requires(Database[voterNumber, cpr] == BallotStatus.Received);
            Contract.Ensures(Database[voterNumber, cpr] == BallotStatus.NotReceived);
            Database[voterNumber, cpr] = BallotStatus.NotReceived;
            if(Logger != null)
                Logger.Log("Revoking ballot for voter with voternumber=" + voterNumber + "; CPR=" + cpr, Level.Warn);
        }

        /// <summary>
        /// Revoke this ballot!
        /// </summary>
        /// <param name="cpr">The CPR number to revoke a ballot for.</param>
        /// <param name="masterPassword">The masterpassword that only the election secretary should know.</param>
        public void RevokeBallot(CPR cpr, string masterPassword) {
            Contract.Requires(masterPassword != null);
            Contract.Requires(ValidMasterPassword(masterPassword));
            Contract.Requires(Database[cpr, masterPassword] == BallotStatus.Received);
            Contract.Ensures(Database[cpr, masterPassword] == BallotStatus.NotReceived);
            Database[cpr, masterPassword] = BallotStatus.NotReceived;
            if(Logger != null)
                Logger.Log("Revoking ballot with masterpassword for voter with CPR=" + cpr, Level.Warn);
        }
        #endregion

        //Methods only the manager should be able to invoke.
        #region Manager
        //Methods related to announcing changes to the list of peers.
        #region Peers
        /// <summary>
        /// Tell the group to add this station as a peer!
        /// </summary>
        /// <param name="newPeer">The address of the station to add.</param>
        /// <param name="newPeerKey">The public AsymmetricKey of the station to add.</param>
        public void AnnounceAddPeer(IPEndPoint newPeer, AsymmetricKey newPeerKey) {
            Contract.Requires(IsManager);
            Contract.Requires(newPeer != null);
            Peers.Keys.Where(peer => !peer.Equals(newPeer)).ForEach(peer => Communicator.Send(new AddPeerCommand(Address, newPeer, newPeerKey), peer));
            if(Logger != null)
                Logger.Log("Announcing that this peer should be added to the peerlist: " + newPeer, Level.Info);
        }

        /// <summary>
        /// Tell the group to remove this station as a peer!
        /// </summary>
        /// <param name="peerToRemove">The address of the station to remove.</param>
        public void AnnounceRemovePeer(IPEndPoint peerToRemove) {
            Contract.Requires(IsManager);
            Contract.Requires(peerToRemove != null);
            RemovePeer(peerToRemove);
            Peers.Keys.ForEach(peer => Communicator.Send(new RemovePeerCommand(Address, peerToRemove), peer));
            if(Logger != null)
                Logger.Log("Announcing that this peer should be removed from the peerlist: " + peerToRemove, Level.Info);
        }

        /// <summary>
        /// Make this station the new manager!
        /// </summary>
        /// <param name="newManager">The station who is to be the new manager.</param>
        public void PromoteNewManager(IPEndPoint newManager) {
            Contract.Requires(IsManager);
            Contract.Requires(newManager != null);
            Peers.Keys.ForEach(peer => Communicator.Send(new PromoteNewManagerCommand(Address, newManager), peer));
            Manager = newManager;
            if(Logger != null)
                Logger.Log("Promoting " + newManager + " to be the manager", Level.Warn);
        }
        #endregion

        //Methods related to announcing changes in the election status.
        #region Election status
        /// <summary>
        /// Announce to all stations that the election has started!
        /// </summary>
        public void AnnounceStartElection() {
            Contract.Requires(!ElectionInProgress);
            Contract.Requires(IsManager);
            Contract.Ensures(ElectionInProgress);
            StartElection();
            Peers.Keys.ForEach(peer => Communicator.Send(new StartElectionCommand(Address), peer));
            if(Logger != null)
                Logger.Log("Announcing that the election should be started.", Level.Info);
        }

        /// <summary>
        /// Announce to all stations that the election has ended!
        /// </summary>
        public void AnnounceEndElection() {
            Contract.Requires(ElectionInProgress);
            Contract.Requires(IsManager);
            Contract.Ensures(!ElectionInProgress);
            EndElection();
            Peers.Keys.ForEach(peer => Communicator.Send(new EndElectionCommand(Address), peer));
            if(Logger != null)
                Logger.Log("Announcing that the election should be ended.", Level.Info);
        }
        #endregion

        //Method related to announcing changes regarding ballot-statuses.
        #region Ballots
        /// <summary>
        /// Announce to all that they should revoke this update!
        /// </summary>
        /// <param name="voterNumber">The voternumber to revoke a ballot for.</param>
        /// <param name="cpr">The CPR number to revoke a ballot for.</param>
        public void AnnounceRevokeBallot(VoterNumber voterNumber, CPR cpr) {
            Contract.Requires(IsManager);
            Contract.Requires(Database[voterNumber, cpr] == BallotStatus.Received);
            var cmd = new RevokeBallotCommand(Address, voterNumber, cpr);
            Peers.Keys.ForEach(peer => Communicator.Send(cmd, peer));
            cmd.Execute(this);
            if(Logger != null)
                Logger.Log("Announcing that this ballot should be revoked: voternumber=" + voterNumber + "; CPR=" + cpr, Level.Warn);
        }

        /// <summary>
        /// Announce to all that they should revoke this update!
        /// </summary>
        /// <param name="cpr">The CPR number to revoke a ballot for.</param>
        /// <param name="masterPassword">The masterpassword that only the election secretary should know.</param>
        public void AnnounceRevokeBallot(CPR cpr, string masterPassword) {
            Contract.Requires(masterPassword != null);
            Contract.Requires(ValidMasterPassword(masterPassword));
            Contract.Requires(Database[cpr, masterPassword] == BallotStatus.Received);
            Contract.Requires(IsManager);
            var cmd = new RevokeBallotCPROnlyCommand(Address, cpr, masterPassword);
            Peers.Keys.ForEach(peer => Communicator.Send(cmd, peer));
            cmd.Execute(this);
            if(Logger != null)
                Logger.Log("Announcing that this ballot should be revoked with masterpassword: CPR=" + cpr, Level.Warn);
        }
        #endregion
        #endregion

        [ContractInvariantMethod]
        private void ObjectInvariant() {
            Contract.Invariant(Address != null);
            Contract.Invariant(Peers != null);
        }

        #region IDisposable
        ~Station() {
            Dispose(false);
        }

        public void Dispose() {
            if(!_isDisposed)
                Dispose(true);
            GC.SuppressFinalize(this);
        }

        private void Dispose(bool disposing) {
            _isDisposed = true;
            if(!disposing)
                return;
            if(Crypto != null)
                Crypto.Dispose();
            if(Listening)
                StopListening();
            Database.Dispose();
            if(Logger != null) {
                Logger.Log("Disposing self", Level.Info);
                Logger.Dispose();
            }
            _logger = null;
            _crypto = null;
            Database = null;
        }
        #endregion
    }
}