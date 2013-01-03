using System;
using System.Diagnostics.Contracts;
using System.Net;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class EndElectionCommand : ICommand {

        /// <summary>
        /// May I have a new command that ends the election at the target?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        public EndElectionCommand(IPEndPoint sender) {
            Contract.Requires(sender != null);
            Sender = sender;
        }

        public IPEndPoint Sender { get; private set; }

        public void Execute(Station receiver) {
            if(!receiver.Manager.Equals(Sender))
                return;
            receiver.EndElection();
            receiver.UI.ElectionEnded();
        }
    }
}