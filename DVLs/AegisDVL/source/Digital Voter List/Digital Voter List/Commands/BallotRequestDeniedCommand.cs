using System;
using System.Diagnostics.Contracts;
using System.Net;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class BallotRequestDeniedCommand : ICommand {

        /// <summary>
        /// May I have a new command that lets the recipient know that a ballot request was denied?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        public BallotRequestDeniedCommand(IPEndPoint sender) {
            Contract.Requires(sender != null);
            Sender = sender;
        }

        public IPEndPoint Sender { get; private set; }

        public void Execute(Station receiver) {
            if(!Sender.Equals(receiver.Manager))
                return;
            receiver.UI.BallotRequestReply(false);
        }
    }
}
