using System;
using System.IO;
using System.Linq;
using Aegis_DVL;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;
using NUnit.Framework;

namespace Tests {
    [TestFixture]
    public class LoggingTests {
        [SetUp]
        public void SetUp() {
            Station = new  Station(new TestUi(), "dataEncryption.key", "yo boii", 62000, "LoggingTestsVoters.sqlite", "LoggingTestsLog.sqlite");
        }

        [TearDown]
        public void TearDown() {
            Station.Dispose();
            Station = null;
            File.Delete("LoggingTestsVoters.sqlite");
            File.Delete("LoggingTestsLog.sqlite");
        }

        public Station Station { get; private set; }

        [Test]
        public void Test() {
            Assert.That(!Station.Logger.Export.Any(entry => entry.Message.ToString() == "Testing testing" && entry.Level == Level.Info));
            Station.Logger.Log("Testing testing", Level.Info);
            Assert.That(Station.Logger.Export.Any(entry => entry.Message.ToString() == "Testing testing" && entry.Level == Level.Info));
            Station.Logger.Export.ForEach(logentry => Console.WriteLine(logentry));
        }
    }
}
