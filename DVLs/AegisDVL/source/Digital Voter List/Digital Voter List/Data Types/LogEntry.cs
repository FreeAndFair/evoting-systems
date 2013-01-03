using System;
using System.Diagnostics.Contracts;

namespace Aegis_DVL.Data_Types {
    /// <summary>
    /// A log entry is an entry in a log. It contains a message, a time and a level indicating its type.
    /// </summary>
    [Serializable]
    public struct LogEntry {
        /// <summary>
        /// What is the message of the log entry?
        /// </summary>
        public object Message { get; private set; }
        
        /// <summary>
        /// What type of log entry is this?
        /// </summary>
        public Level Level { get; private set; }

        /// <summary>
        /// At what time was the log entry added?
        /// </summary>
        public DateTime Timestamp { get; private set; }

        /// <summary>
        /// May I have a new LogEntry?
        /// </summary>
        /// <param name="message">The object to log. Typically a string.</param>
        /// <param name="level">The severity-level of the log-entry. Typically Info</param>
        public LogEntry(object message, Level level)
            : this() {
            Contract.Requires(message != null);

            Message = message;
            Level = level;
            Timestamp = DateTime.Now;
        }

        public override string ToString() {
            return Timestamp + "; " + Level + "; " + Message;
        }

        [ContractInvariantMethod]
        private void ObjectInvariant() {
            Contract.Invariant(Message != null);
            Contract.Invariant(!Equals(Level, null));
            Contract.Invariant(!Equals(Timestamp, null));
        }
    }
}
