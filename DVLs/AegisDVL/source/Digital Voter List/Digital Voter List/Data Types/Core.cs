using System;
using System.Diagnostics.Contracts;
using System.Globalization;
using Aegis_DVL.Util;
using Org.BouncyCastle.Crypto;

namespace Aegis_DVL.Data_Types {

    #region Crypto
    /// <summary>
    /// Encrypted voterdata is the encrypted combination of CPR, VoterNumber and BallotStatus.
    /// </summary>
    [Serializable]
    public struct EncryptedVoterData {
        /// <summary>
        /// What is the encrypted voter-number of this encrypted voterdata?
        /// </summary>
        public CipherText VoterNumber { get; private set; }

        /// <summary>
        /// What is the encrypted CPR-number of this encrypted voterdata?
        /// </summary>
        public CipherText CPR { get; private set; }

        /// <summary>
        /// What is the encrypted ballot status of this encrypted voterdata?
        /// </summary>
        public CipherText BallotStatus { get; private set; }

        public EncryptedVoterData(CipherText voternumber, CipherText cpr, CipherText ballotstatus)
            : this() {
            VoterNumber = voternumber;
            CPR = cpr;
            BallotStatus = ballotstatus;
        }

        public override string ToString() {
            return string.Format("VoterNumber: {0}; CPR: {1}; Ballot: {2}", VoterNumber, CPR, BallotStatus);
        }

        [ContractInvariantMethod]
        private void ObjectInvariant() {
            Contract.Invariant(!Equals(CPR, null));
            Contract.Invariant(!Equals(VoterNumber, null));
            Contract.Invariant(!Equals(BallotStatus, null));
        }
    }

    /// <summary>
    /// CipherText is encrypted data.
    /// </summary>
    [Serializable]
    public struct CipherText {

        /// <summary>
        /// What does this CipherText look like?
        /// </summary>
        public byte[] Value { get; private set; }

        /// <summary>
        /// May I have a new ciphertext?
        /// </summary>
        /// <param name="cipher">The back ciphertext. Commonly a byte-array.</param>
        public CipherText(byte[] cipher)
            : this() {
            Contract.Requires(cipher != null);
            Value = cipher;
        }

        public static implicit operator byte[](CipherText cipher) {
            return cipher.Value;
        }

        public override string ToString() {
            return Value.AsBase64();
        }

        [ContractInvariantMethod]
        private void ObjectInvariant() {
            Contract.Invariant(Value != null);
        }
    }

    /// <summary>
    ///  An asymmetric key can be used for either encryption or decryption of data.
    /// </summary>
    public struct AsymmetricKey {

        /// <summary>
        /// What does this a symmetric key look like?
        /// </summary>
        public AsymmetricKeyParameter Value { get; private set; }

        /// <summary>
        /// May I have a new asymmetric key?
        /// </summary>
        /// <param name="key">The backing asymmetric crypto-key.</param>
        public AsymmetricKey(AsymmetricKeyParameter key)
            : this() {
            Contract.Requires(key != null);
            Value = key;
        }

        public static implicit operator AsymmetricKeyParameter(AsymmetricKey asymmetricKey) {
            return asymmetricKey.Value;
        }

        [ContractInvariantMethod]
        private void ObjectInvariant() {
            Contract.Invariant(Value != null);
        }
    }

    public struct SymmetricKey {

        /// <summary>
        /// What does this symmetric key look like?
        /// </summary>
        public byte[] Value { get; private set; }

        /// <summary>
        /// May I have a new symmetric key?
        /// </summary>
        /// <param name="key">The backing symmetric crypto-key.</param>
        public SymmetricKey(byte[] key)
            : this() {
            Contract.Requires(key != null);
            Value = key;
        }

        public static implicit operator byte[](SymmetricKey symmetricKey) {
            return symmetricKey.Value;
        }

        [ContractInvariantMethod]
        private void ObjectInvariant() {
            Contract.Invariant(Value != null);
        }
    }
    #endregion

    /// <summary>
    /// A message contains the ciphertexts of a symmetric key, a message encrypted with the symmetric key and 
    /// a hash encrypted with the senders public key. Used for secure communication.
    /// </summary>
    [Serializable]
    public struct Message {
        /// <summary>
        /// What is the initialization vector used to encrypt the command?
        /// </summary>
        public byte[] Iv { get; private set; }

        /// <summary>
        /// What is the CipherText of the symmetric key used to encrypt the command?
        /// </summary>
        public CipherText SymmetricKey { get; private set; }

        /// <summary>
        /// What is the CipherText of the encrypted command?
        /// </summary>
        public CipherText Command { get; private set; }

        /// <summary>
        /// What is the CipherText of the senderhash of the command?
        /// </summary>
        public CipherText SenderHash { get; private set; }

        /// <summary>
        /// May I have a new Message?
        /// </summary>
        /// <param name="symmetricKey">The asymetrically-encrypted symmetric key.</param>
        /// <param name="content">The content of the message. Should be a symmetrically encrypted command.</param>
        /// <param name="senderHash">The asymetrically-encrypted sender-hash of the content.</param>
        /// <param name="iv">The initilization-vector for the content.</param>
        public Message(CipherText symmetricKey, CipherText content, CipherText senderHash, byte[] iv)
            : this() {
            Contract.Requires(iv != null);

            SymmetricKey = symmetricKey;
            Command = content;
            SenderHash = senderHash;
            Iv = iv;
        }

        public override string ToString() {
            return string.Format("Symmetric key: {0}\nValue: {1}\nSenderHash: {2}\nIv: {3}", SymmetricKey, Command, SenderHash, Iv.AsString());
        }

        [ContractInvariantMethod]
        private void ObjectInvariant() {
            Contract.Invariant(!Equals(SymmetricKey, null));
            Contract.Invariant(!Equals(Iv, null));
            Contract.Invariant(!Equals(Command, null));
            Contract.Invariant(!Equals(SenderHash, null));
        }
    }


    #region Voter Data
    /// <summary>
    /// A voternumber is a unique number used in conjunction with the CPR-number to request a ballot.
    /// </summary>
    [Serializable]
    public struct VoterNumber {
        /// <summary>
        /// What does this voter-number look like?
        /// </summary>
        public uint Value { get; set; }

        /// <summary>
        /// May I have a new VoterNumber?
        /// </summary>
        /// <param name="value">The value of the voternumber.</param>
        public VoterNumber(uint value)
            : this() {
            Value = value;
        }

        public static implicit operator uint(VoterNumber voterNum) {
            return voterNum.Value;
        }

        public override string ToString() {
            return Value.ToString(CultureInfo.InvariantCulture);
        }
    }

    /// <summary>
    /// A CPR-number is a number and a unique identifier for a danish citizen, consisting of the birthdate and a number.
    /// </summary>
    [Serializable]
    public struct CPR {

        /// <summary>
        /// What does this CPR-number look like?
        /// </summary>
        public uint Value { get; set; }

        /// <summary>
        /// May I have a new CPR?
        /// </summary>
        /// <param name="value">The value of the CPR-number.</param>
        public CPR(uint value)
            : this() {
            Value = value;
        }

        public static implicit operator uint(CPR cpr) {
            return cpr.Value;
        }

        public override string ToString() {
            return Value.ToString(CultureInfo.InvariantCulture);
        }

        [ContractInvariantMethod]
        private void ObjectInvariant() {
            Contract.Invariant(Value > 0);
        }
    }

    /// <summary>
    /// A ballot status is used in conjunction with a cpr-number and a voternumber, and indicates 
    /// wheither status that indicates whether the ballot has been handed out, not handed out, or 
    /// if it is unavailable at the given election venue."
    /// </summary>
    public enum BallotStatus {
        Received = 7,
        NotReceived = 11,
        Unavailable = 13
    }
    #endregion
}