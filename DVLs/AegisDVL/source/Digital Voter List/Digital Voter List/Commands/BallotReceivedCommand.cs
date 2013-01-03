using System;
using System.Diagnostics.Contracts;
using System.Net;
using Aegis_DVL.Data_Types;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class BallotReceivedCommand : ICommand {
        private readonly IPEndPoint _requester;
        private readonly VoterNumber _voterNumber;
        private readonly CPR _cpr;

        /// <summary>
        /// May I have a new command that tells the target that a ballot should be handed out and be marked as received?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        /// <param name="requester">The address of the station who initially requested the ballot.</param>
        /// <param name="voterNumber">The voternumber of the ballot to be handed out and to be marked as received.</param>
        /// <param name="cpr">The CPR-number of the ballot to be handed out and to be marked as received.</param>
        public BallotReceivedCommand(IPEndPoint sender, IPEndPoint requester, VoterNumber voterNumber, CPR cpr) {
            Contract.Requires(sender != null);
            Contract.Requires(requester != null);

            _requester = requester;
            _voterNumber = voterNumber;
            _cpr = cpr;
            Sender = sender;
        }

        public IPEndPoint Sender {
            get;
            private set;
        }

        public void Execute(Station receiver) {
            if(!receiver.Manager.Equals(Sender) || receiver.Database[_voterNumber, _cpr] == BallotStatus.Received)
                return;
            receiver.Database[_voterNumber, _cpr] = BallotStatus.Received;
            if(receiver.Address.Equals(_requester))
                receiver.UI.BallotRequestReply(true);
        }
    }
}
