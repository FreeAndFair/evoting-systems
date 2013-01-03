using System;
using System.Diagnostics.Contracts;
using System.Net;
using Aegis_DVL.Data_Types;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class RevokeBallotCPROnlyCommand : ICommand {
        private readonly CPR _cpr;
        private readonly string _masterPassword;

        /// <summary>
        /// May I have a a command that revokes a ballot at the target?
        /// </summary>
        /// <param name="sender">The one sending the command.</param>
        /// <param name="cpr">The CPR-number to revoke a ballot for.</param>
        /// <param name="masterPassword">The masterpassword only the election secretary should know.</param>
        public RevokeBallotCPROnlyCommand(IPEndPoint sender, CPR cpr, string masterPassword) {
            Contract.Requires(sender != null);
            _cpr = cpr;
            _masterPassword = masterPassword;
            Sender = sender;
        }

        public IPEndPoint Sender {
            get;
            private set;
        }

        public void Execute(Station receiver) {
            if(!receiver.ValidMasterPassword(_masterPassword) || !receiver.Manager.Equals(Sender) || receiver.Database[_cpr, _masterPassword] != BallotStatus.Received)
                return;
            receiver.Database[_cpr, _masterPassword] = BallotStatus.NotReceived;
        }
    }
}