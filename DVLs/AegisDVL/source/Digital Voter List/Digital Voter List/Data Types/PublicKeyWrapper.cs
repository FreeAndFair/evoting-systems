using System;
using System.Diagnostics.Contracts;
using Aegis_DVL.Cryptography;
using Aegis_DVL.Util;

namespace Aegis_DVL.Data_Types {
    [Serializable]
    public class PublicKeyWrapper {
        private readonly byte[] _keyBytes;

        /// <summary>
        /// May I have a new wrapper for my this public key?
        /// </summary>
        /// <param name="crypto">The crypto service used.</param>
        /// <param name="physicalSecret">A password that obscures the public key.</param>
        public PublicKeyWrapper(ICrypto crypto, string physicalSecret) {
            Contract.Requires(crypto != null);
            Contract.Requires(physicalSecret != null);
            _keyBytes = Bytes.Obfuscate(crypto, crypto.Keys.Item1.Value.ToBytes(), physicalSecret);
        }

        /// <summary>
        /// What is the key, when deobfuscated with this string?
        /// </summary>
        /// <param name="crypto">Cryptography service used for hashing.</param>
        /// <param name="physicalSecret">The string used to deobfuscate the key.</param>
        /// <returns>The original key, assuming the string was identical to the one used to obfuscate it.</returns>
        public AsymmetricKey GetKey(ICrypto crypto, string physicalSecret) {
            Contract.Requires(physicalSecret != null);
            return new AsymmetricKey(Bytes.Obfuscate(crypto, _keyBytes, physicalSecret).ToKey());
        }
    }
}