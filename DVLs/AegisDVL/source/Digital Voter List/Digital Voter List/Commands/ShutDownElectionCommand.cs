using System;
using System.Diagnostics.Contracts;
using System.Net;
using Aegis_DVL.Data_Types;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class ShutDownElectionCommand : ICommand {
        /// <summary>
        /// May I have a new command that shuts down the election at the target?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        public ShutDownElectionCommand(IPEndPoint sender) {
            Contract.Requires(sender != null);
            Sender = sender;
        }

        public IPEndPoint Sender {
            get;
            private set;
        }

        public void Execute(Station receiver) {
            receiver.UI.Shutdown();
            throw new TheOnlyException();
        }
    }
}