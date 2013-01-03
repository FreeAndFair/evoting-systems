using System;
using System.Collections.Generic;
using System.Data.SQLite;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;

namespace Aegis_DVL.Logging {
    public class Logger : ILogger {
        private readonly Entities _db;

        /// <summary>
        /// May I have a new Logger?
        /// </summary>
        /// <param name="parent">The parent-station who the Logger belongs to.</param>
        /// <param name="logName">The name of the file where the log should be saved.</param>
        public Logger(Station parent, string logName = "Log.sqlite") {
            Contract.Requires(parent != null);
            Contract.Requires(logName != null);

            var password = parent.MasterPassword.AsBase64();
            InitDb(logName, password);
            var conStr = String.Format("metadata=res://*/Logging.LogModel.csdl|res://*/Logging.LogModel.ssdl|res://*/Logging.LogModel.msl;provider=System.Data.SQLite;provider connection string='data source={0};Password={1}'", logName, password);
            _db = new Entities(conStr);
            _db.Connection.Open();
            Log("Logger created", Level.Info);
        }

        public void Log(object message, Level level) {
            lock(_db) {
                _db.Logs.AddObject(Logging.Log.CreateLog(++_i, Bytes.From(new LogEntry(message, level))));
                _db.SaveChanges();
            }
        }

        private int _i;
        public IEnumerable<LogEntry> Export {
            get { return _db.Logs.ToArray().Select(data => data.LogEntry.To<LogEntry>()); }
        }

        private static void InitDb(string logName, string password) {
            if(File.Exists(logName)) {
                var now = DateTime.Now;
                File.Move(logName, string.Format("Log{0}.sqlite", now.Date.Day + "." + now.Date.Month + "." + now.Date.Year + "-" + now.Hour + "." + now.Minute + "." + now.Second + "." + now.Millisecond));
            }
            SQLiteConnection.CreateFile(logName);
            var connString = string.Format("data source={0};Password={1}", logName, password);
            using(var db = new SQLiteConnection(connString)) {
                db.Open();
                using(var cmd = db.CreateCommand()) {
                    cmd.CommandText = "CREATE TABLE Logs(Id INTEGER PRIMARY KEY AUTOINCREMENT, LogEntry BLOB NOT NULL)";
                    cmd.ExecuteNonQuery();
                }
            }
        }

        #region IDisposable
        ~Logger() {
            Dispose(false);
        }

        private bool _isDisposed;
        public void Dispose() {
            if(!_isDisposed)
                Dispose(true);
            GC.SuppressFinalize(this);
        }

        private void Dispose(bool disposing) {
            _isDisposed = true;
            _db.SaveChanges();
            if(disposing)
                _db.Dispose();
        }
    }
        #endregion
}
