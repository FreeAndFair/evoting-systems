using System;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class RequestBallotCPROnlyCommand : ICommand {
        private readonly CPR _cpr;
        private readonly string _password;

        /// <summary>
        /// May I have a new command that requests a ballot at the target?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        /// <param name="cpr">The CPR-number to request a ballot for.</param>
        /// <param name="password">The master-password that only the election secretary should know.</param>
        public RequestBallotCPROnlyCommand(IPEndPoint sender, CPR cpr, string password) {
            Contract.Requires(sender != null);
            Contract.Requires(password != null);
            _cpr = cpr;
            _password = password;
            Sender = sender;
        }

        public IPEndPoint Sender { get; private set; }

        public void Execute(Station receiver) {
            if(!receiver.IsManager)
                return;
            if(receiver.Database[_cpr, _password] != BallotStatus.NotReceived) {
                receiver.Communicator.Send(new BallotRequestDeniedCommand(receiver.Address), Sender);
                receiver.Logger.Log("Attempted to request a ballot that had status " + receiver.Database[_cpr, _password], Level.Info);
                return;
            }
            receiver.BallotReceived(_cpr, _password);
            receiver.Peers.Keys.Where(peer => !peer.Equals(Sender)).ForEach(peer => receiver.Communicator.Send(new BallotReceivedCPROnlyCommand(receiver.Address, Sender, _cpr, _password), peer));
            if(Sender.Equals(receiver.Manager)) {
                receiver.UI.BallotRequestReply(true);
                return;
            }
            try {
                receiver.Communicator.Send(new BallotReceivedCPROnlyCommand(receiver.Address, Sender, _cpr, _password), Sender);
            }
            catch(SocketException) {
                receiver.AnnounceRevokeBallot(_cpr, _password);
            }
        }
    }
}
