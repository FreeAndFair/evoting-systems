using System;
using System.Diagnostics.Contracts;
using System.Net;
using Aegis_DVL.Data_Types;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class BallotReceivedCPROnlyCommand : ICommand {
        private readonly IPEndPoint _requester;
        private readonly CPR _cpr;
        private readonly string _password;

        /// <summary>
        /// May I have a new command that requests a ballot with just the CPR number and masterpassword known?
        /// </summary>
        /// <param name="sender">The address of the one sending the command.</param>
        /// <param name="requester">The address of the station requesting the command.</param>
        /// <param name="cpr">The CPR-number of the ballot being requested.</param>
        /// <param name="password">The masterpassword for the election, that only the election secretary should know.</param>
        public BallotReceivedCPROnlyCommand(IPEndPoint sender, IPEndPoint requester, CPR cpr, string password) {
            Contract.Requires(sender != null);
            Contract.Requires(requester != null);
            Contract.Requires(password != null);

            _requester = requester;
            _cpr = cpr;
            _password = password;
            Sender = sender;
        }

        public IPEndPoint Sender {
            get;
            private set;
        }

        public void Execute(Station receiver) {
            if(!receiver.Manager.Equals(Sender) || receiver.Database[_cpr, _password] != BallotStatus.NotReceived)
                return;
            receiver.BallotReceived(_cpr, _password);
            if(receiver.Address.Equals(_requester)) {
                receiver.UI.BallotRequestReply(true);
            }
        }
    }
}
