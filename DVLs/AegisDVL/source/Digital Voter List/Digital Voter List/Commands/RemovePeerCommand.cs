using System;
using System.Diagnostics.Contracts;
using System.Net;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class RemovePeerCommand : ICommand {
        private readonly IPEndPoint _peer;

        /// <summary>
        /// May I have a new command that removes a peer at the target?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        /// <param name="peer">The address of the peer to remove.</param>
        public RemovePeerCommand(IPEndPoint sender, IPEndPoint peer) {
            Contract.Requires(sender != null);
            _peer = peer;
            Sender = sender;
        }

        public IPEndPoint Sender { get; private set; }

        public void Execute(Station receiver) {
            if(receiver.Manager.Equals(Sender))
                receiver.RemovePeer(_peer);
        }
    }
}