using System;
using System.Collections.Generic;
using System.Net;
using System.Windows;
using Aegis_DVL;
using Aegis_DVL.Cryptography;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;
using UI.ManagerWindows;
using UI.StationWindows;

namespace UI {
    public class UiHandler : IDvlUi {
        private Station _station;
        private string _masterPassword;
        private readonly StationWindow _stationWindow;

        public WaitingForManagerPage WaitingForManagerPage;
        public OverviewPage OverviewPage;
        public ManagerOverviewPage ManagerOverviewPage;
        public BallotRequestPage BallotRequestPage;
        public BallotCPRRequestWindow BallotCPRRequestWindow;

        public UiHandler(StationWindow stationWindow) {
            _stationWindow = stationWindow;
        }

        public string ManagerExchangingKey(IPEndPoint ip) {
            return WaitingForManagerPage != null ? WaitingForManagerPage.IncomingConnection(ip) : "";
        }

        public string StationExchangingKey(IPEndPoint ip) {
            if(OverviewPage != null) {
                OverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { OverviewPage.SetPasswordLabel(""); }));
                return OverviewPage.IncomingReply(ip);
            }

            if(ManagerOverviewPage != null) {
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.SetPasswordLabel(""); }));
                return ManagerOverviewPage.IncomingReply(ip);
            }
            return "";
        }

        public void ShowPasswordOnManager(string password) {
            if(OverviewPage != null)
                OverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { OverviewPage.SetPasswordLabel("Indtast dette kodeord på stationen: " + password); }));
            if(ManagerOverviewPage != null)
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.SetPasswordLabel("Indtast dette kodeord på stationen: " + password); }));
        }

        public void ShowPasswordOnStation(string password) {
            if(WaitingForManagerPage != null)
                WaitingForManagerPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { WaitingForManagerPage.SetPasswordLabel("Indtast dette kodeord på manageren: " + password); }));
        }

        public void BallotRequestReply(bool handOutBallot) {
            if(BallotRequestPage != null)
                BallotRequestPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotRequestPage.BallotResponse(handOutBallot); }));
            if(ManagerOverviewPage != null)
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.BallotResponse(handOutBallot); }));
            if(BallotCPRRequestWindow != null)
                BallotCPRRequestWindow.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotCPRRequestWindow.BallotResponse(handOutBallot); }));
        }

        public void ElectionEnded() {
            if(BallotRequestPage != null)
                BallotRequestPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotRequestPage.EndElection(); }));
        }

        public void ElectionStarted() {
            if(WaitingForManagerPage != null)
                WaitingForManagerPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { WaitingForManagerPage.StartElection(); }));
        }

        public void IsNowManager() {
            if(BallotRequestPage != null)
                BallotRequestPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotRequestPage.BecomeManager(); }));
        }

        public void Shutdown() {
            MessageBox.Show("Valget er blevet udsat for et potentielt angreb og lukkes ned", "Lukker ned",
                            MessageBoxButton.OK, MessageBoxImage.Error);
            Environment.Exit(0);
        }

        public void NotEnoughPeers() {
            _stationWindow.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { _stationWindow.MarkVoterMenuItem.IsEnabled = false; }));

            if(BallotRequestPage != null) {
                BallotRequestPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotRequestPage.Blocked = true; }));
                BallotRequestPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotRequestPage.checkValidityButton.IsEnabled = false; }));
                BallotRequestPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotRequestPage.WaitingLabel.Content = "Der er ikke nok stationer tilsluttet"; }));
            }
            if(ManagerOverviewPage != null) {
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.Blocked = true; }));
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.checkValidityButton.IsEnabled = false; }));
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.OnlyCprButton.IsEnabled = false; }));
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.WaitingLabel.Content = "Der er ikke nok stationer tilsluttet"; }));
            }

        }

        public void EnoughPeers() {
            _stationWindow.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { _stationWindow.MarkVoterMenuItem.IsEnabled = true; }));

            if(BallotRequestPage != null) {
                BallotRequestPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotRequestPage.Blocked = false; }));
                BallotRequestPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { BallotRequestPage.WaitingLabel.Content = ""; }));
            }
            if(ManagerOverviewPage != null) {
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.Blocked = false; }));
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.WaitingLabel.Content = ""; }));
            }

        }


        /// <summary>
        /// Import the election data from a serialized IEnumerable of EncryptedVoterData file
        /// </summary>
        /// <param name="filePath">the file path of the voter data</param>
        /// <returns>the voter data as a IEnumerable of EncryptedVoterData</returns>
        public IEnumerable<EncryptedVoterData> ImportElectionData(string filePath) {
            return Bytes.FromFile(filePath, 30000000).To<IEnumerable<EncryptedVoterData>>();
        }

        /// <summary>
        /// Export data in the format IEnumerable of EncryptedVoterData to a file
        /// </summary>
        /// <param name="data">the voter data to be exported</param>
        /// <param name="filePath">the file destination</param>
        public void ExportData(IEnumerable<EncryptedVoterData> data, string filePath) {
            Bytes.From(data).ToFile(filePath);
        }

        /// <summary>
        /// Marks a station as connnected in the list
        /// </summary>
        /// <param name="ip">the p address of the station</param>
        public void MarkAsConnected(IPEndPoint ip) {
            if(OverviewPage != null)
                OverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { OverviewPage.MarkAsConnected(ip); }));
            if(ManagerOverviewPage != null)
                ManagerOverviewPage.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { ManagerOverviewPage.MarkAsConnected(ip); }));
        }

        /// <summary>
        /// This method is called when a voter wants to request a ballot after entering their voternumber and CPR number
        /// </summary>
        /// <param name="voterNumber">the voternumber of the voter</param>
        /// <param name="cpr">the CPR number of the voter</param>
        public void RequestBallot(string voterNumber, string cpr) {
            var vn = new VoterNumber(uint.Parse(voterNumber));
            var ncpr = new CPR(uint.Parse(cpr));

            if(_station.Database[vn, ncpr] == BallotStatus.NotReceived)
                _station.RequestBallot(vn, ncpr);
            else {
                BallotRequestReply(false);
            }
        }

        /// <summary>
        /// This method is called when an election offical wants to mark a voter by only using their CPR number.
        /// The election official will also need to enter the master password.
        /// </summary>
        /// <param name="cpr">the CPR number of the voter</param>
        /// <param name="masterPassword">the systems master password</param>
        public void RequestBallotOnlyCPR(string cpr, string masterPassword) {

            var ncpr = new CPR(uint.Parse(cpr));

            if(_station.Database[ncpr, masterPassword] == BallotStatus.NotReceived)
                _station.RequestBallot(ncpr, masterPassword);
            else
                BallotRequestReply(false);
        }

        /// <summary>
        /// This methods asks the station for a password it can use as master password
        /// </summary>
        /// <returns>the master password</returns>
        public string GeneratePassword() {
            _masterPassword = Crypto.GeneratePassword();
            return _masterPassword;
        }

        /// <summary>
        /// Checks if a entered password matches the master password
        /// </summary>
        /// <param name="typedPassword">the entered password</param>
        /// <returns>whether or not it matches the master password</returns>
        public bool IsMasterPWCorrect(string typedPassword) {
            return _station != null && _station.ValidMasterPassword(typedPassword);
        }

        /// <summary>
        /// Called when the manager wants to remove a station from the network
        /// </summary>
        /// <param name="ip">the IP adress of the station to be removed</param>
        public void RemoveStation(string ip) {
            _station.AnnounceRemovePeer(new IPEndPoint(IPAddress.Parse(ip), 62000));
        }

        /// <summary>
        /// Gets he IP adresses of the machines in the local network running this application
        /// </summary>
        /// <returns>a list of IP adresses</returns>
        public IEnumerable<IPEndPoint> DiscoverPeers() {
            return _station.DiscoverPeers();
        }

        /// <summary>
        /// Asks the _station for the list of peers as IPEndpoints
        /// </summary>
        /// <returns>the list of peers as IPEndpoints</returns>
        public IEnumerable<IPEndPoint> GetPeerlist() {
            return _station.Peers.Keys;
        }

        /// <summary>
        /// When a manager want to start the election this method should be called
        /// to announce the start to all stations.
        /// </summary>
        public void ManagerAnnounceStartElection() {
            _station.AnnounceStartElection();
        }

        /// <summary>
        /// When a manager want to end the election this method should be called
        /// to announce the end to all stations.
        /// </summary>
        public void AnnounceEndElection() {
            _station.AnnounceEndElection();
        }

        /// <summary>
        /// When a manager wants to import voter data this is called
        /// </summary>
        /// <param name="dataPath">the file path of the data to be imported</param>
        /// <param name="keyPath">the file path of the encryption key</param>
        /// <returns>whether or not the import were succesful</returns>
        public bool ImportData(string dataPath, string keyPath) {
            _station = _station ?? new Station(this, keyPath, _masterPassword);
            _masterPassword = null;

            try {
                _station.Database.Import(ImportElectionData(dataPath));
                return true;
            }
            catch(Exception) {
                return false;
            }
        }

        /// <summary>
        /// When a manager wants to export voter data this is called
        /// </summary>
        /// <param name="filePath">the destination filepath</param>
        public void ExportData(string filePath) {
            if(_station != null)
                ExportData(_station.Database.AllData, filePath);
            else
                MessageBox.Show("Du kan ikke eksportere dataen på dette tidspunkt", "Ikke muligt", MessageBoxButton.OK);
        }

        /// <summary>
        /// When a manager wants to connect to a station, this is called to exchange the public keys
        /// </summary>
        /// <param name="ip">The IP address of the station</param>
        public void ExchangeKeys(IPEndPoint ip) {
            _station.ExchangePublicKeys(ip);
        }

        /// <summary>
        /// When a manager wants to promot another station to be the new manager this is called
        /// </summary>
        /// <param name="ip">The IP address of the new manager</param>
        /// <returns>whether or not the promotion was succesful</returns>
        public bool MakeManager(IPEndPoint ip) {
            if(_station.StationActive(ip)) {
                _station.PromoteNewManager(ip);
                return true;
            }
            return false;
        }

        /// <summary>
        /// Creates a new station and makes it start listening
        /// </summary>
        public void CreateNewStation() {
            _station = new Station(this);
        }

        /// <summary>
        /// disposes the current station
        /// </summary>
        public void DisposeStation() {
            if(_station != null)
                _station.Dispose();
            _station = null;
        }

        /// <summary>
        /// Checks whether or not a machine is reachable
        /// </summary>
        /// <param name="ip">the IP address of the machine</param>
        /// <returns>whether or not the machine is active</returns>
        public bool IsStationActive(IPEndPoint ip) {
            return _station.StationActive(ip);
        }

        /// <summary>
        /// Checks if there are enough stations in the peerlist
        /// </summary>
        /// <returns>wheter there are enough stations is hte peerlist</returns>
        public bool EnoughStations() {
            return _station.EnoughStations;
        }
    }
}
