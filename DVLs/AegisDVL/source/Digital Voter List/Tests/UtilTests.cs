using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Cryptography;
using Aegis_DVL.Util;
using NUnit.Framework;

namespace Tests {
    [TestFixture]
    public class UtilTests {
        public byte[] TestByteArray { get; private set; }

        /// <summary>
        /// SetUp test helper properties.
        /// </summary>
        [SetUp]
        public void SetUp() {
            TestByteArray = new byte[] { 1, 2, 3, 4, 5 };
        }

        /// <summary>
        /// Test all the various byte and enumerable utility methods
        /// </summary>
        [Test]
        public void BytesAndEnumerableTest() {
            Assert.That(TestByteArray.AsBase64().Equals("AQIDBAU="));
            Assert.That(TestByteArray.AsString().Equals("[1] [2] [3] [4] [5] "));
            var sum = 0;
            TestByteArray.ForEach(x => sum += x);
            Assert.That(sum == 15);
            Assert.That(TestByteArray.IsIdenticalTo(TestByteArray));

            var mergeArray = TestByteArray.Merge(TestByteArray);
            Assert.That(mergeArray.Length == 10);

            var xorArray = TestByteArray.Xor(new byte[] { 5, 4, 3 });
            Assert.That(!xorArray.IsIdenticalTo(TestByteArray));

            const string str = "Test string";
            var strBytes = Bytes.From(str);
            Assert.That(strBytes.To<string>().Equals(str));

            using(var stream = new MemoryStream(TestByteArray)) {
                var bytes = Bytes.FromStream(stream);
                Assert.That(bytes.IsIdenticalTo(TestByteArray));

                Assert.That(bytes.IsIdenticalTo(Bytes.From(bytes)));
            }
        }

        [Test]
        public void IPEndPointComparerTest() {
            var ip1 = new IPEndPoint(IPAddress.Parse("127.0.0.1"), 56721);
            var ip2 = new IPEndPoint(IPAddress.Parse("127.0.0.1"), 56722);
            var comparer = new IPEndPointComparer();
            Assert.That(comparer.Compare(ip1, ip2) == -1);
            Assert.That(comparer.Compare(ip2, ip1) == 1);
            Assert.That(comparer.Compare(ip1, ip1) == 0);
            Assert.That(comparer.Compare(ip2, ip2) == 0);
        }

        [Test]
        public void KeyUtilTest() {
            var crypto = new Crypto(new AsymmetricKey());
            var key = crypto.Keys.Item1.Value;

            Assert.That(key.ToBytes().ToKey().Equals(key));
        }

        [Test]
        public void SerializeSizeTest() {
            const string ip = "192.68.0.1";
            const int port = 62000;
            var merged = ip + ":" + port;
            var ipendpoint = new IPEndPoint(IPAddress.Parse(ip), port);
            Console.WriteLine("Class-size: {0}", Bytes.From(ipendpoint).Length);
            Console.WriteLine("Primitive-size: {0}", Bytes.From(ip).Length + Bytes.From(port).Length);
            Console.WriteLine("Merged primitives-size: {0}", Bytes.From(merged).Length);

            var list = new List<string> { merged, merged, merged };
            var arr = new[] { merged, merged, merged };
            Console.WriteLine("List-size of merged primities: {0}", Bytes.From(list).Length);
            Console.WriteLine("Array-size of merged primities: {0}", Bytes.From(arr).Length);
        }
    }
}
