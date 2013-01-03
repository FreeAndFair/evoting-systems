using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Aegis_DVL.Data_Types;

namespace Aegis_DVL.Logging {
    /// <summary>
    /// A log is used to track events in the system.
    /// </summary>
    [ContractClass(typeof(LoggerContract))]
    public interface ILogger : IDisposable {
        /// <summary>
        /// Log this message!
        /// </summary>
        /// <param name="message">The message to log.</param>
        /// <param name="level">The logging level the message.</param>
        void Log(object message, Level level);

        /// <summary>
        /// What does the entire log look like?
        /// </summary>
        IEnumerable<LogEntry> Export { get; }
    }

    [ContractClassFor(typeof(ILogger))]
    public abstract class LoggerContract : ILogger {
        public void Log(object message, Level level) {
            Contract.Requires(message != null);
            Contract.Ensures(Export.Any(entry => entry.Message.Equals(message) && entry.Level == level));
        }

        public IEnumerable<LogEntry> Export {
            get {
                Contract.Ensures(Contract.Result<IEnumerable<LogEntry>>() != null);
                return default(IEnumerable<LogEntry>);
            }
        }

        public void Dispose() {
        }
    }
}