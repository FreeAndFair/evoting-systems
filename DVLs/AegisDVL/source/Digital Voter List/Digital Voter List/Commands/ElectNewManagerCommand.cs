using System;
using System.Diagnostics.Contracts;
using System.Net;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class ElectNewManagerCommand : ICommand {

        /// <summary>
        /// May I have a new command that asks the target to elect a new manager?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        public ElectNewManagerCommand(IPEndPoint sender) {
            Contract.Requires(sender != null);
            Sender = sender;
        }

        public IPEndPoint Sender {
            get;
            private set;
        }

        public void Execute(Station receiver) {
            if(!receiver.StationActive(receiver.Manager))
                receiver.ElectNewManager();
        }
    }
}