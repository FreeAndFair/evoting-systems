using System;
using System.Diagnostics.Contracts;
using System.Net;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class PromoteNewManagerCommand : ICommand {
        private readonly IPEndPoint _newManager;

        /// <summary>
        /// May I have a new command that promotes another machine to be the new manager?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        /// <param name="newManager">The address of the station that should be the new manager.</param>
        public PromoteNewManagerCommand(IPEndPoint sender, IPEndPoint newManager) {
            Contract.Requires(sender != null);
            Contract.Requires(newManager != null);
            _newManager = newManager;
            Sender = sender;
        }

        public IPEndPoint Sender { get; private set; }

        public void Execute(Station receiver) {
            if (!receiver.Manager.Equals(Sender)) return;
            receiver.Manager = _newManager;
            receiver.UI.IsNowManager();
        }
    }
}