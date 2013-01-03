using System.Net;
using Aegis_DVL;

namespace Tests {
    public class TestUi : IDvlUi {
        public string ManagerExchangingKey(IPEndPoint ip) {
            return PasswordFromManager;
        }

        public string StationExchangingKey(IPEndPoint ip) {
            return PasswordFromStation;
        }

        public void ShowPasswordOnManager(string password) {
            PasswordFromManager = password;
        }

        public string PasswordFromManager { get; private set; }

        public void ShowPasswordOnStation(string password) {
            PasswordFromStation = password;
        }

        public string PasswordFromStation { get; private set; }

        public void BallotRequestReply(bool handOutBallot) {
            HandOutBallot = handOutBallot;
        }

        public bool HandOutBallot { get; private set; }

        public void ElectionEnded() {
            OngoingElection = false;
        }

        public bool OngoingElection { get; private set; }

        public void ElectionStarted() {
            OngoingElection = true;
        }

        public void IsNowManager() {
            IsManager = true;
        }

        public void Shutdown() {
            UIShutDown = true;
        }

        public void NotEnoughPeers() {
            UIHasEnoughPeers = false;
        }

        protected bool UIHasEnoughPeers { get; set; }

        public void EnoughPeers() {
            UIHasEnoughPeers = true;
        }

        protected bool UIShutDown { get; set; }

        public bool IsManager { get; private set; }
    }
}