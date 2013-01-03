using System;
using System.Diagnostics.Contracts;
using System.Net;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class StartElectionCommand : ICommand {
        /// <summary>
        /// May I have a new Command that starts the election at the target
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        public StartElectionCommand(IPEndPoint sender) {
            Contract.Requires(sender != null);
            Sender = sender;
        }

        public IPEndPoint Sender { get; private set; }

        public void Execute(Station receiver) {
            if (!receiver.Manager.Equals(Sender)) return;
            receiver.StartElection();
            receiver.UI.ElectionStarted();
        }
    }
}