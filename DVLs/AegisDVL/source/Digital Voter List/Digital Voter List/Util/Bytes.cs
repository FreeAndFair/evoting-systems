using System;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Net.Sockets;
using System.Runtime.Serialization.Formatters.Binary;
using Aegis_DVL.Cryptography;

namespace Aegis_DVL.Util {
    public static class Bytes {
        /// <summary>
        /// What is the resulting byte array from obfuscating this byte array with this modifier?
        /// </summary>
        /// <param name="crypto">Cryptography service used for hashing.</param>
        /// <param name="source">The byte array to obfuscate.</param>
        /// <param name="modifier">The string used to obfuscate the source.</param>
        /// <returns>An obfuscated byte array.</returns>
        public static byte[] Obfuscate(ICrypto crypto, byte[] source, string modifier) {
            Contract.Requires(crypto != null);
            Contract.Requires(source != null);
            Contract.Requires(modifier != null);
            // ReSharper disable PossibleNullReferenceException
            Contract.Ensures(Contract.Result<byte[]>() != null && Contract.Result<byte[]>().Length == source.Length);
            // ReSharper restore PossibleNullReferenceException
            var modBytes = GenModifier(crypto, modifier, source.Length);
            return source.Xor(modBytes);
        }

        /// <summary>
        /// What is the obfuscation-byte array with this size based on this string?
        /// </summary>
        /// <param name="crypto">Cryptography service used for hashing.</param>
        /// <param name="fromString">The string to generate the modifier from.</param>
        /// <param name="sourceLength">The length of the byte array to be returned.</param>
        /// <returns>A byte array with length sourceLength generated using fromString.</returns>
        private static byte[] GenModifier(ICrypto crypto, string fromString, int sourceLength) {
            var output = new byte[0];
            for(var i = 0; output.Length < sourceLength; i++) {
                output = output.Merge(crypto.Hash(From(fromString + i)));
            }
            return output.Take(sourceLength).ToArray();
        }

        /// <summary>
        /// What is this object as a byte array?
        /// </summary>
        /// <typeparam name="T">The type of the object.</typeparam>
        /// <param name="source">The object to turn into a byte array. If it is already a byte array, no conversion is performed.</param>
        /// <returns>The byte array representation of the object.</returns>
        [Pure]
        public static byte[] From<T>(T source) {
            Contract.Requires(!Equals(source, null));
            Contract.Requires(source.GetType().IsSerializable);
            Contract.Ensures(!(source is byte[]) || Contract.Result<byte[]>() == source as byte[]);
            Contract.Ensures(Contract.Result<byte[]>() != null);
            if(source is byte[])
                return source as byte[];
            using(var ms = new MemoryStream()) {
                var bf = new BinaryFormatter();
                bf.Serialize(ms, source);
                return ms.ToArray();
            }
        }

        /// <summary>
        /// What are the bytes in this stream?
        /// </summary>
        /// <param name="stream">The stream to extract bytes from.</param>
        /// <param name="bufferSize">The internal buffer-size, should be big enough to handle the biggest potential objects send over the stream. Default to 4096 bytes.</param>
        /// <returns>A byte array with the size and content of the actual output of bytes from the stream.</returns>
        [Pure]
        public static byte[] FromStream(Stream stream, uint bufferSize = 16384) {
            Contract.Requires(stream != null);
            Contract.Requires(bufferSize > 0);

            var buffer = new byte[bufferSize];
            var length = stream.Read(buffer, 0, buffer.Length);
            var bytes = new byte[length];
            for(var i = 0; i < length; i++) {
                bytes[i] = buffer[i];
            }
            return bytes;
        }

        /// <summary>
        /// What are the bytes in this networkstream?
        /// </summary>
        /// <param name="stream">The networkstream to extract bytes from.</param>
        /// <param name="bufferSize">The internal buffer size. Defaults to 65535.</param>
        /// <returns></returns>
        [Pure]
        public static byte[] FromNetworkStream(NetworkStream stream, uint bufferSize = 32768) {
            using(var ms = new MemoryStream()) {
                var buffer = new byte[bufferSize];
                int bytesRead;
                while((bytesRead = stream.Read(buffer, 0, (int)bufferSize)) != 0) {
                    ms.Write(buffer, 0, bytesRead);
                }
                return ms.ToArray();
            }
        }

        /// <summary>
        /// What is the bytes from this file?
        /// </summary>
        /// <param name="filename">The name of the file to read bytes from.</param>
        /// <param name="bufferSize">The size of the byte-buffer.</param>
        /// <returns>The bytes from the file.</returns>
        [Pure]
        public static byte[] FromFile(string filename, uint bufferSize = 16384) {
            using(var file = File.OpenRead(filename)) {
                return FromStream(file, bufferSize);
            }
        }

        /// <summary>
        /// Save these bytes to this file!
        /// </summary>
        /// <param name="bytes">The bytes to write.</param>
        /// <param name="filename">The name of the file where the bytes should be saved.</param>
        public static void ToFile(this byte[] bytes, string filename) {
            using(var file = File.Create(filename)) {
                file.Write(bytes, 0, bytes.Length);
            }
        }

        #region Byte array extension methods
        /// <summary>
        /// What is the result of using the exclusive-or operation on this byte array with this other byte array?
        /// </summary>
        /// <param name="self">The original byte array.</param>
        /// <param name="xorWith">The byte array to XOR with the original byte array.</param>
        /// <returns>A byte array with the length of the original byte array, where the bytes are the result of xoring the original byte array with the xor byte array.</returns>
        [Pure]
        public static byte[] Xor(this byte[] self, byte[] xorWith) {
            Contract.Requires(self != null && xorWith != null);
            Contract.Ensures(!self.IsIdenticalTo(Contract.Result<byte[]>()));
            var result = new byte[self.Length];
            for(var i = 0; i < result.Length; i++) {
                result[i] = (byte)(self[i] ^ xorWith[i % xorWith.Length]);
            }
            return result;
        }

        /// <summary>
        /// What is the result of merging this byte array with this other byte array?
        /// </summary>
        /// <param name="self">The original byte array.</param>
        /// <param name="mergeWith">The byte array you are merging with the original byte array.</param>
        /// <returns>A byte array consisting of the original byte array appended by the other byte array.</returns>
        [Pure]
        public static byte[] Merge(this byte[] self, byte[] mergeWith) {
            Contract.Requires(self != null && mergeWith != null);
            // ReSharper disable PossibleNullReferenceException
            Contract.Ensures(Contract.Result<byte[]>() != null && Contract.Result<byte[]>().Length == self.Length + mergeWith.Length);
            // ReSharper restore PossibleNullReferenceException
            return self.Concat(mergeWith).ToArray();
        }

        /// <summary>
        /// What is the result of transforming this byte array to an object of this type?
        /// </summary>
        /// <typeparam name="T">The type of the desired object.</typeparam>
        /// <param name="bytes">The byte array to transform into the type.</param>
        /// <returns>The transformed object</returns>
        [Pure]
        public static T To<T>(this byte[] bytes) {
            Contract.Requires(bytes != null);
            using(var stream = new MemoryStream(bytes)) {
                var bf = new BinaryFormatter();
                return (T)bf.Deserialize(stream);
            }
        }

        /// <summary>
        /// What does this byte array look like as a string?
        /// </summary>
        /// <param name="self">The byte array to format.</param>
        /// <returns>A string-representation of the byte array.</returns>
        [Pure]
        public static string AsString(this byte[] self) {
            Contract.Requires(self != null);
            Contract.Ensures(Contract.Result<string>() != null);
            return self.Aggregate("", (acc, item) => acc + "[" + item + "] ");
        }

        /// <summary>
        /// What does this byte array look like when base64-encoded?
        /// </summary>
        /// <param name="self">The byte array to format.</param>
        /// <returns>A Base64-formatted string of the byte array.</returns>
        [Pure]
        public static string AsBase64(this byte[] self) {
            Contract.Requires(self != null);
            Contract.Ensures(Contract.Result<string>() != null);
            return Convert.ToBase64String(self);
        }

        /// <summary>
        /// Is every byte in this byte array identical to the corresponding byte in the other byte array?
        /// </summary>
        /// <param name="self">The initial byte array.</param>
        /// <param name="compare">The byte array to compare the initial byte array with.</param>
        /// <returns>True if every byte-pair is equal, otherwise false.</returns>
        [Pure]
        public static bool IsIdenticalTo(this byte[] self, byte[] compare) {
            Contract.Requires(self != null && compare != null);
            return self.SequenceEqual(compare);
        }
        #endregion
    }
}
