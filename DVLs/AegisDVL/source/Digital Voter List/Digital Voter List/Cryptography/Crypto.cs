using System;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Security.Cryptography;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Modes;
using Org.BouncyCastle.Crypto.Paddings;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Security;

namespace Aegis_DVL.Cryptography {

    public class Crypto : ICrypto {
        private readonly RsaEngine _asymEngine;
        private readonly PaddedBufferedBlockCipher _symEngine;
        private readonly SHA256Managed _hasher;
        private byte[] _iv;
        private readonly SecureRandom _random;

        [Pure]
        public AsymmetricKey VoterDataEncryptionKey { get; set; }

        public Tuple<AsymmetricKey, AsymmetricKey> Keys { get; private set; }

        /// <summary>
        /// May I have a new Crypto where the VoterDataEncryptionKey is set to this?
        /// </summary>
        /// <param name="encryptionAsymmetricKey">The VoterDataEncryptionKey.</param>
        public Crypto(AsymmetricKey encryptionAsymmetricKey)
            : this() {
            Contract.Ensures(VoterDataEncryptionKey.Equals(encryptionAsymmetricKey));
            VoterDataEncryptionKey = encryptionAsymmetricKey;
        }

        /// <summary>
        /// May I have a new Crypto?
        /// </summary>
        public Crypto() {
            _random = new SecureRandom();

            //RSA initialization
            _asymEngine = new RsaEngine();
            var rsaKeyPairGnr = new RsaKeyPairGenerator();
            rsaKeyPairGnr.Init(new KeyGenerationParameters(new SecureRandom(), 3072));
            var keys = rsaKeyPairGnr.GenerateKeyPair();

            //AES initialization
            //TODO: Should probably use CCM-mode instead of CBC (since bouncy doesn't have CWC..), but we couldn't get it to work because we're stupid as hell.
            _symEngine = new PaddedBufferedBlockCipher(new CbcBlockCipher(new AesEngine()));
            NewIv();

            //SHA256 initilization
            _hasher = new SHA256Managed();

            Keys = new Tuple<AsymmetricKey, AsymmetricKey>(new AsymmetricKey(keys.Public), new AsymmetricKey(keys.Private));
        }

        public CipherText AsymmetricEncrypt(byte[] bytes, AsymmetricKey asymmetricKey) {
            _asymEngine.Init(true, asymmetricKey.Value);
            return new CipherText(_asymEngine.ProcessBlock(new byte[] { 1 }.Merge(bytes), 0, bytes.Length + 1));
        }

        public byte[] AsymmetricDecrypt(CipherText cipher, AsymmetricKey asymmetricKey) {
            _asymEngine.Init(false, asymmetricKey.Value);
            return _asymEngine.ProcessBlock(cipher, 0, cipher.Value.Length).Skip(1).ToArray();
        }

        public CipherText SymmetricEncrypt(byte[] bytes, SymmetricKey symmetricKey) {
            _symEngine.Init(true, new ParametersWithIV(new KeyParameter(symmetricKey), Iv));
            return new CipherText(_symEngine.DoFinal(bytes));
        }

        public byte[] SymmetricDecrypt(CipherText cipher, SymmetricKey symmetricKey) {
            _symEngine.Init(false, new ParametersWithIV(new KeyParameter(symmetricKey), Iv));
            return _symEngine.DoFinal(cipher);
        }

        public byte[] Iv {
            get { return _iv; }
            set { _iv = value; }
        }

        public void NewIv() {
            var oldIv = _iv;
            do {
                _iv = new byte[_symEngine.GetBlockSize()];
                _random.NextBytes(Iv);
                oldIv = oldIv ?? _iv;
            } while (oldIv.SequenceEqual(_iv));
        }

        public byte[] GenerateSymmetricKey() {
            var key = new byte[32];
            _random.NextBytes(key);
            return key;
        }

        public byte[] Hash(byte[] bytes) {
            return _hasher.ComputeHash(bytes);
        }

        /// <summary>
        /// May I have a new randomly generated human-readable password?
        /// </summary>
        /// <returns>A randomly generated password.</returns>
        [Pure]
        public static string GeneratePassword() {
            Contract.Ensures(Contract.Result<string>() != null && Contract.Result<string>().Length > 0);
            var random = new SecureRandom();
            var bytes = new byte[128];
            random.NextBytes(bytes);
            return new string(bytes.AsBase64().Take(10).ToArray());
        }


        #region IDisposable
        ~Crypto() {
            Dispose(false);
        }

        private bool _isDisposed;
        public void Dispose() {
            if (!_isDisposed)
                Dispose(true);
            GC.SuppressFinalize(this);
        }

        private void Dispose(bool disposing) {
            _isDisposed = true;
            if (disposing)
                _hasher.Dispose();
        }
        #endregion
    }
}