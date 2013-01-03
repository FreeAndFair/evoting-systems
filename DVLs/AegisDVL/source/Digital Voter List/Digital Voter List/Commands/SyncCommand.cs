using System;
using System.Diagnostics.Contracts;
using System.Net;
using System.Linq;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Logging;
using Aegis_DVL.Util;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class SyncCommand : ICommand {
        private readonly byte[][][] _simpleVoterData;
        private readonly byte[] _masterPwHash;
        private readonly string[] _addresses;
        private readonly byte[][] _publicKeys;
        private readonly string _sender;
        private readonly byte[] _electionDataKey;

        /// <summary>
        /// Can I have a new command that synchronizes the target?
        /// </summary>
        /// <param name="parent">The parent-station sending the command.</param>
        public SyncCommand(Station parent) {
            Contract.Requires(parent != null);
            _sender = parent.Address.ToString();
            _simpleVoterData = parent.Database.AllData.Select(encvdata => new[] { encvdata.VoterNumber.Value, encvdata.CPR.Value, encvdata.BallotStatus.Value }).ToArray();
            _addresses = parent.Peers.Keys.Select(endpoint => endpoint.ToString()).ToArray();
            _publicKeys = parent.Peers.Values.Select(key => key.Value.ToBytes()).ToArray();
            _masterPwHash = Bytes.FromFile("Master.pw");
            _electionDataKey = parent.Crypto.VoterDataEncryptionKey.Value.ToBytes();
        }

        public IPEndPoint Sender {
            get {
                var pieces = _sender.Split(':');
                var ip = pieces[0];
                var port = pieces[1];
                return new IPEndPoint(IPAddress.Parse(ip), int.Parse(port));
            }
        }

        public void Execute(Station receiver) {
            if(!Sender.Equals(receiver.Manager))
                return;
            receiver.Crypto.VoterDataEncryptionKey = new AsymmetricKey(_electionDataKey.ToKey());
            receiver.MasterPassword = _masterPwHash;
            receiver.Logger = new Logger(receiver);

            for(var i = 0; i < _addresses.Length; i++) {
                var pieces = _addresses[i].Split(':');
                var ip = pieces[0];
                var port = pieces[1];
                var endPoint = new IPEndPoint(IPAddress.Parse(ip), int.Parse(port));
                if(!receiver.Address.Equals(endPoint))
                    receiver.AddPeer(endPoint, new AsymmetricKey(_publicKeys[i].ToKey()));
            }

            receiver.Database.Import(_simpleVoterData.Select(row => new EncryptedVoterData(new CipherText(row[0]), new CipherText(row[1]), new CipherText(row[2]))));
            receiver.Logger.Log("Synchronized by " + Sender, Level.Info);
        }
    }
}
