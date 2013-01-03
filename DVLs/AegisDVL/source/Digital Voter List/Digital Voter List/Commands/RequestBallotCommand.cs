using System;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class RequestBallotCommand : ICommand {

        /// <summary>
        /// May I have a new command that requests a ballot of the target?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        /// <param name="voternumber">The voternumber to request a ballot for.</param>
        /// <param name="cpr">The CPR-number to request a ballot for.</param>
        public RequestBallotCommand(IPEndPoint sender, VoterNumber voternumber, CPR cpr) {
            Contract.Requires(sender != null);
            Sender = sender;
            _voternumber = voternumber;
            _cpr = cpr;
        }

        public IPEndPoint Sender {
            get;
            private set;
        }

        private readonly VoterNumber _voternumber;
        private readonly CPR _cpr;

        public void Execute(Station receiver) {
            if(!receiver.IsManager)
                return;
            if(receiver.Database[_voternumber, _cpr] != BallotStatus.NotReceived) {
                receiver.Communicator.Send(new BallotRequestDeniedCommand(receiver.Address), Sender);
                receiver.Logger.Log("Attempted to request a ballot that had status " + receiver.Database[_voternumber, _cpr], Level.Info);
                return;
            }
            receiver.BallotReceived(_voternumber, _cpr);

            //Send to all but requester
            receiver.Peers.Keys.Where(peer => !peer.Equals(Sender)).ForEach(peer => receiver.Communicator.Send(new BallotReceivedCommand(receiver.Address, Sender, _voternumber, _cpr), peer));

            if(Sender.Equals(receiver.Manager)) {
                receiver.UI.BallotRequestReply(true);
                return;
            }
            //Send to requester last.
            try {
                receiver.Communicator.Send(new BallotReceivedCommand(receiver.Address, Sender, _voternumber, _cpr), Sender);
            }
            catch(SocketException) {
                receiver.AnnounceRevokeBallot(_voternumber, _cpr);
            }
        }
    }
}
