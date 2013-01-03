using System;
using System.Diagnostics.Contracts;
using System.Linq;
using Aegis_DVL.Data_Types;

namespace Aegis_DVL.Cryptography {
    /// <summary>
    /// Crypto is responsible for cryptographic functions such as public-key encryption.
    /// </summary>
    [ContractClass(typeof(CryptoContract))]
    public interface ICrypto : IDisposable {
        /// <summary>
        /// What is the asymmetric key used for encrypting voterdata at this election venue?
        /// </summary>
        [Pure]
        AsymmetricKey VoterDataEncryptionKey { get; set; }

        /// <summary>
        /// What are the keys for my public key infrastructure?
        /// Item1 = Public key
        /// Item2 = Private key
        /// </summary>
        Tuple<AsymmetricKey, AsymmetricKey> Keys { get; }

        /// <summary>
        /// What does this look like when it's asymmetrically encrypted with this key?
        /// </summary>
        /// <param name="bytes">the bytes to be encrypted</param>
        /// <param name="asymmetricKey">the AsymmetricKey to ecnrypt with</param>
        /// <returns>the encrypted byte array as a ciphertext</returns>
        [Pure]
        CipherText AsymmetricEncrypt(byte[] bytes, AsymmetricKey asymmetricKey);

        /// <summary>
        /// What does this look like when it's asymmetrically decrypted with this key?
        /// </summary>
        /// <param name="cipher">the ciphertext to be decrypted</param>
        /// <param name="asymmetricKey">the AsymmetricKey to decrypt with</param>
        /// <returns>the decrypted ciphertext as a byte array</returns>
        [Pure]
        byte[] AsymmetricDecrypt(CipherText cipher, AsymmetricKey asymmetricKey);

        /// <summary>
        /// What does this look like when it's symmetrically encrypted with this key?
        /// </summary>
        /// <param name="bytes">the bytes to be encrypted</param>
        /// <param name="symmetricKey">the AsymmetricKey to ecnrypt with</param>
        /// <returns>the encrypted byte array as a ciphertext</returns>
        [Pure]
        CipherText SymmetricEncrypt(byte[] bytes, SymmetricKey symmetricKey);

        /// <summary>
        /// What does this look like when it's symmetrically decrypted with this key?
        /// </summary>
        /// <param name="cipher">the ciphertext to be decrypted</param>
        /// <param name="symmetricKey">the AsymmetricKey to decrypt with</param>
        /// <returns>the decrypted ciphertext as a byte array</returns>
        [Pure]
        byte[] SymmetricDecrypt(CipherText cipher, SymmetricKey symmetricKey);

        /// <summary>
        /// What is the current initilization vector?
        /// The initilization vector is this!
        /// </summary>
        byte[] Iv { [Pure] get; set; }

        /// <summary>
        /// Generate a new initialization vector to be used for symmetric encryption!
        /// </summary>
        void NewIv();

        /// <summary>
        /// May I have a new randomly generated symmetric key?
        /// </summary>
        /// <returns></returns>
        [Pure]
        byte[] GenerateSymmetricKey();

        /// <summary>
        /// What is the hashed value of this?
        /// </summary>
        /// <param name="bytes">The bytes to be hashed.</param>
        /// <returns>The hashed bytes.</returns>
        [Pure]
        byte[] Hash(byte[] bytes);
    }

    [ContractClassFor(typeof(ICrypto))]
    public abstract class CryptoContract : ICrypto {
        public AsymmetricKey VoterDataEncryptionKey {
            get {
                return default(AsymmetricKey);
            }
            set {}
        }

        public Tuple<AsymmetricKey, AsymmetricKey> Keys {
            get {
                var res = Contract.Result<Tuple<AsymmetricKey, AsymmetricKey>>();
                Contract.Ensures(res != null && !Equals(res.Item1, null) && !Equals(res.Item2, null));
                return default(Tuple<AsymmetricKey, AsymmetricKey>);
            }
        }

        public CipherText AsymmetricEncrypt(byte[] bytes, AsymmetricKey asymmetricKey) {
            Contract.Requires(bytes != null);
            return default(CipherText);
        }

        public byte[] AsymmetricDecrypt(CipherText cipher, AsymmetricKey asymmetricKey) {
            Contract.Ensures(Contract.Result<byte[]>() != null);
            return default(byte[]);
        }

        public CipherText SymmetricEncrypt(byte[] bytes, SymmetricKey symmetricKey) {
            Contract.Requires(bytes != null);
            return default(CipherText);
        }

        public byte[] SymmetricDecrypt(CipherText cipher, SymmetricKey symmetricKey) {
            Contract.Ensures(Contract.Result<byte[]>() != null);
            return default(byte[]);
        }

        public byte[] Iv {
            get {
                Contract.Ensures(Contract.Result<byte[]>() != null);
                return default(byte[]);
            }
            set {
                Contract.Requires(value != null);
                Contract.Ensures(Iv.SequenceEqual(value));
            }
        }

        public void NewIv() {
            Contract.Ensures(Iv != null);
            Contract.Ensures(Contract.OldValue(Iv) == null || Contract.OldValue(Iv) != Iv);
        }

        public byte[] GenerateSymmetricKey() {
            Contract.Ensures(Contract.Result<byte[]>() != null);
            return default(byte[]);
        }

        public byte[] Hash(byte[] bytes) {
            Contract.Requires(bytes != null);
            return default(byte[]);
        }

        public void Dispose() { }
    }
}
