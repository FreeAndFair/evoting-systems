using System;
using System.Diagnostics.Contracts;
using System.IO;
using System.Net;
using System.Threading.Tasks;
using Aegis_DVL.Cryptography;
using Aegis_DVL.Data_Types;
using Org.BouncyCastle.Asn1;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class PublicKeyExchangeCommand : ICommand {
        private readonly bool _isReply;
        private readonly PublicKeyWrapper _wrapper;

        /// <summary>
        /// May I have a new command that exchanges public keys with the target?
        /// </summary>
        /// <param name="parent">The parent station starting the exchange. Should be a manager.</param>
        /// <param name="isReply">Whether it's a reply from the target. Shouldn't be set manually. Defaults to false.</param>
        public PublicKeyExchangeCommand(Station parent, bool isReply = false) {
            Contract.Requires(parent != null);
            _isReply = isReply;
            Sender = parent.Address;
            var pswd = Crypto.GeneratePassword();
            if (isReply)
                parent.UI.ShowPasswordOnStation(pswd);
            else
                parent.UI.ShowPasswordOnManager(pswd);
            _wrapper = new PublicKeyWrapper(parent.Crypto, pswd);
        }

        public IPEndPoint Sender { get; private set; }

        public void Execute(Station receiver) {
            //Don't perform key exchange when we have a manager
            if (!_isReply && receiver.Manager != null)
                receiver.ShutDownElection();

            try {
                GetPassword(receiver);
            } catch (TaskCanceledException) { return; }

            if (_isReply) {
                //Done with key-exchange, synchronize new peer
                receiver.Communicator.Send(new SyncCommand(receiver), Sender);
                receiver.AnnounceAddPeer(Sender, receiver.Peers[Sender]);
                if(receiver.ElectionInProgress)
                    receiver.Communicator.Send(new StartElectionCommand(receiver.Address), Sender);
                return;
            }
            receiver.Manager = Sender;
            //Respond with own public key
            var reply = new PublicKeyExchangeCommand(receiver, true);
            receiver.Communicator.Send(reply, Sender);
        }

        public void GetPassword(Station receiver) {
            var deObfuscationPassword = _isReply ? receiver.UI.StationExchangingKey(Sender) : receiver.UI.ManagerExchangingKey(Sender);
            try {
                if (deObfuscationPassword == "")
                    throw new TaskCanceledException();
                var key = _wrapper.GetKey(receiver.Crypto, deObfuscationPassword);
                receiver.AddPeer(Sender, key);
            } catch (Exception e) {
                if (e is ArgumentException || e is IOException || e is Asn1ParsingException)
                    GetPassword(receiver);
                else
                    throw;
            }
        }
    }
}
