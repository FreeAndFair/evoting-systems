using System;
using System.Diagnostics.Contracts;
using System.Net;
using Aegis_DVL.Data_Types;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class RevokeBallotCommand : ICommand {
        private readonly VoterNumber _voterNumber;
        private readonly CPR _cpr;

        /// <summary>
        /// May I have a a command that revokes a ballot at the target?
        /// </summary>
        /// <param name="sender">The one sending the command.</param>
        /// <param name="voterNumber">The voternumber to revoke a ballot for.</param>
        /// <param name="cpr">The CPR-number to revoke a ballot for.</param>
        public RevokeBallotCommand(IPEndPoint sender, VoterNumber voterNumber, CPR cpr) {
            Contract.Requires(sender != null);
            _voterNumber = voterNumber;
            _cpr = cpr;
            Sender = sender;
        }

        public IPEndPoint Sender {
            get;
            private set;
        }

        public void Execute(Station receiver) {
            if(!receiver.Manager.Equals(Sender) || receiver.Database[_voterNumber, _cpr] != BallotStatus.Received) return;
            receiver.Database[_voterNumber, _cpr] = BallotStatus.NotReceived;
        }
    }
}