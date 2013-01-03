using System;
using System.Diagnostics.Contracts;
using System.Net;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;

namespace Aegis_DVL.Commands {
    [Serializable]
    public class CryptoCommand : ICommand {
        private Message _content;

        /// <summary>
        /// May I have a new command that wraps and encrypts an inner command, to be transmitted securely?
        /// </summary>
        /// <param name="parent">The parent-station sending the command.</param>
        /// <param name="to">The address of the recipient.</param>
        /// <param name="innerCommand">The command to be wrapped.</param>
        public CryptoCommand(Station parent, IPEndPoint to, ICommand innerCommand) {
            Contract.Requires(parent != null);
            Contract.Requires(to != null);
            Contract.Requires(innerCommand != null);

            Sender = parent.Address;
            var crypto = parent.Crypto;

            var cmdBytes = Bytes.From(innerCommand);
            var symmetricKey = crypto.GenerateSymmetricKey();
            crypto.NewIv();

            var symmetricallyEncryptedCmdBytes = crypto.SymmetricEncrypt(cmdBytes, new SymmetricKey(symmetricKey));

            var targetKey = parent.IsManager && to.Equals(parent.Address) ? parent.Crypto.Keys.Item1 : parent.Peers[to];
            var asymKeyBytes = crypto.AsymmetricEncrypt(symmetricKey, new AsymmetricKey(targetKey));

            var senderHashBytes = crypto.AsymmetricEncrypt(crypto.Hash(cmdBytes), new AsymmetricKey(crypto.Keys.Item2));

            var symmetricKeyCipher = new CipherText(asymKeyBytes);
            var commandCipher = new CipherText(symmetricallyEncryptedCmdBytes);
            var senderHash = new CipherText(senderHashBytes);
            var iv = crypto.Iv;

            _content = new Message(symmetricKeyCipher, commandCipher, senderHash, iv);
        }

        public IPEndPoint Sender { get; private set; }

        public void Execute(Station receiver) {
            var crypto = receiver.Crypto;
            var symmetricKey = crypto.AsymmetricDecrypt(_content.SymmetricKey, crypto.Keys.Item2);
            crypto.Iv = _content.Iv;

            var cmd = crypto.SymmetricDecrypt(_content.Command, new SymmetricKey(symmetricKey)).To<ICommand>();

            //Do we "know" the sender?
            if ((receiver.Peers.ContainsKey(cmd.Sender) || Sender.Equals(receiver.Address)) && Sender.Equals(cmd.Sender)) {
                var key = receiver.Peers.ContainsKey(cmd.Sender) ? receiver.Peers[Sender] : receiver.Crypto.Keys.Item1;
                var senderHash = crypto.AsymmetricDecrypt(_content.SenderHash, key);
                if (crypto.Hash(Bytes.From(cmd)).IsIdenticalTo(senderHash))
                    cmd.Execute(receiver);
                else receiver.ShutDownElection();
            } else receiver.ShutDownElection();
        }
    }
}
