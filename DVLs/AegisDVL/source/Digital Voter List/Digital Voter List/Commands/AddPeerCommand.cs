using System;
using System.Diagnostics.Contracts;
using System.Net;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class AddPeerCommand : ICommand {
        private readonly IPEndPoint _peer;
        private readonly byte[] _peerPublicAsymmetricKey;

        /// <summary>
        /// May I have a new command that tells the target to add a peer to its peer-list?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        /// <param name="peer">The address of the peer to be added to the peer-list.</param>
        /// <param name="peerPublicAsymmetricKey">The public key of the peer to be added to the peer-list.</param>
        public AddPeerCommand(IPEndPoint sender, IPEndPoint peer, AsymmetricKey peerPublicAsymmetricKey) {
            Contract.Requires(sender != null);
            Contract.Requires(peer != null);

            _peer = peer;
            _peerPublicAsymmetricKey = peerPublicAsymmetricKey.Value.ToBytes();
            Sender = sender;
        }

        public IPEndPoint Sender {
            get;
            private set;
        }

        public void Execute(Station receiver) {
            if(receiver.Manager.Equals(Sender)) {
                receiver.AddPeer(_peer, new AsymmetricKey(_peerPublicAsymmetricKey.ToKey()));
            }
        }
    }
}