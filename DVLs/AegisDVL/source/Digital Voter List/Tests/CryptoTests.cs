using System.IO;
using Aegis_DVL;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Cryptography;
using Aegis_DVL.Util;
using NUnit.Framework;

namespace Tests {
    [TestFixture]
    public class CryptoTests {
        public ICrypto Crypto { get; private set; }
        private Station _station;
        /// <summary>
        /// SetUp test helper properties.
        /// </summary>
        [SetUp]
        public void SetUp() {
            _station = new Station(new TestUi(), "dataEncryption.key", "yo boii", 62001, "CryptoTestVoters.sqlite");
            Crypto = _station.Crypto;
        }

        [TearDown]
        public void TearDown() {
            _station.Dispose();
            _station = null;
            File.Delete("CryptoTestVoters.sqlite");
        }

        /// <summary>
        /// 
        /// </summary>
        [Test]
        public void AsymmetricTest() {
            //Encrypt/decrypt
            const string testString = "Howdy there, partner!";
            var bytes = Bytes.From(testString);
            var ciphertext = Crypto.AsymmetricEncrypt(bytes, Crypto.Keys.Item1);
            Assert.That(!bytes.IsIdenticalTo(ciphertext));
            var decryptedBytes = Crypto.AsymmetricDecrypt(ciphertext, Crypto.Keys.Item2);
            Assert.That(bytes.IsIdenticalTo(decryptedBytes));
            Assert.That(decryptedBytes.To<string>().Equals(testString));

            //Encrypt/decrypt using reversed keys
            ciphertext = Crypto.AsymmetricEncrypt(bytes, Crypto.Keys.Item2);
            decryptedBytes = Crypto.AsymmetricDecrypt(ciphertext, Crypto.Keys.Item1);
            Assert.That(bytes.IsIdenticalTo(decryptedBytes));

            //Test that the same content/key give the same result
            ciphertext = Crypto.AsymmetricEncrypt(bytes, Crypto.Keys.Item1);
            Assert.That(ciphertext.Value.IsIdenticalTo(Crypto.AsymmetricEncrypt(bytes, Crypto.Keys.Item1)));
        }

        [Test]
        public void SymmetricTest() {
            var key = new SymmetricKey(Crypto.GenerateSymmetricKey());
            const string testString = "Howdy there, partner!";
            var bytes = Bytes.From(testString);
            var ciphertext = Crypto.SymmetricEncrypt(bytes, key);
            Assert.That(!bytes.IsIdenticalTo(ciphertext));
            var decryptedBytes = Crypto.SymmetricDecrypt(ciphertext, key);
            Assert.That(bytes.IsIdenticalTo(decryptedBytes));
            Assert.That(decryptedBytes.To<string>().Equals(testString));
        }

        [Test]
        public void IvTest() {
            var oldIv = Crypto.Iv;
            Crypto.NewIv();
            Assert.That(!oldIv.IsIdenticalTo(Crypto.Iv));
            Crypto.Iv = oldIv;
            Assert.That(oldIv.IsIdenticalTo(Crypto.Iv));
        }

        [Test]
        public void HashTest() {
            const string str1 = "hello";
            const string str2 = "hello";
            Assert.That(Crypto.Hash(Bytes.From(str1)).IsIdenticalTo(Crypto.Hash(Bytes.From(str2))));
        }

        [Test]
        public void GeneratePasswordTest() {
            var pswd = Aegis_DVL.Cryptography.Crypto.GeneratePassword();
            Assert.That(!string.IsNullOrEmpty(pswd));
        }
    }
}
