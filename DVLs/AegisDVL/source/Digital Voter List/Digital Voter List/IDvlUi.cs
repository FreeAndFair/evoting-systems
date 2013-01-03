using System.Net;

namespace Aegis_DVL {
    /// <summary>
    /// A UI is used to interact with human beings. The UI must be able to support requirements to be able to interact with the Digital Voter List system.
    /// </summary>
    public interface IDvlUi {
        /// <summary>
        /// What is the password the user typed in to respond to the manager initiating a key-exchange?
        /// </summary>
        /// <param name="ip">The IP adress of the connecting manager.</param>
        /// <returns>The typed password.</returns>
        //When a station receives a PublicKeyExchangeCommand from a manager, this method
        // should be called. It will trigger a prompt where the user can input a password.
        string ManagerExchangingKey(IPEndPoint ip);

        /// <summary>
        /// What is the password the user typed in when a station is replying to a key-exchange?
        /// </summary>
        /// <param name="ip">The IP adress of the replying station.</param>
        /// <returns>The typed password.</returns>
        // When a manager receives a PublicKeyExchangeCommand as a reply, this method should 
        // be called. It will trigger a prompt where the user can input a password.
        string StationExchangingKey(IPEndPoint ip);

        /// <summary>
        /// Show this password on the manager machine!
        /// </summary>
        /// <param name="password">The password to display.</param>
        // When a manager wants to connect to a station a password needs to be typed on the station
        // That password is displayed on the manager via this method.
        void ShowPasswordOnManager(string password);

        /// <summary>
        /// Show this password on a station machine!
        /// </summary>
        /// <param name="password">The password to display.</param>
        // When a station replies to a connect request from a manager a password needs to be typed on the station
        // That password is displayed on the manager via this method.
        void ShowPasswordOnStation(string password);

        /// <summary>
        /// Let the UI know whether or not the voter can receive a ballot!
        /// </summary>
        /// <param name="handOutBallot">Whether or not the ballot should be handed out to the voter.</param>
        // When a station requests a ballot this method is called when the response is received.
        void BallotRequestReply(bool handOutBallot);

        /// <summary>
        /// Let the UI know that the election has ended!
        /// </summary>
        // When the election ends, the UI is notified with this method.
        void ElectionEnded();

        /// <summary>
        /// Let the UI know that the election has started!
        /// </summary>
        // When the election starts, the UI is notified with this method.
        void ElectionStarted();

        /// <summary>
        /// Let the UI know that this machine is now the manager!
        /// </summary>
        // Called on a station to signal that it has now become the new manager.
        void IsNowManager();

        /// <summary>
        /// Let the UI know that it needs to shut down!
        /// </summary>
        // Called when the election is compromised and needs to shut down.
        void Shutdown();

        /// <summary>
        /// Let the UI know that there are not enough peers to continue execution!
        /// </summary>
        // Called when the number of peers during the election falls below the required amount.
        void NotEnoughPeers();

        /// <summary>
        /// Let the UI know that there are enough peers to continue execution!
        /// </summary>
        // Called when the number of peers during the election rises above the required amount.
        void EnoughPeers();
    }
}