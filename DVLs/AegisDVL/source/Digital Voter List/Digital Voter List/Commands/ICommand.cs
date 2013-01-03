using System.Diagnostics.Contracts;
using System.Net;

namespace Aegis_DVL.Commands {

    /// <summary>
    /// A command is sent over the network and can be executed at the destination.
    /// </summary>
    [ContractClass(typeof(CommandContract))]
    public interface ICommand {
        /// <summary>
        /// Who sent this command?
        /// </summary>
        IPEndPoint Sender { get; }

        /// <summary>
        /// Execute this command!
        /// </summary>
        /// <param name="receiver">The station the command will execute commands on.</param>
        void Execute(Station receiver);
    }

    [ContractClassFor(typeof(ICommand))]
    public abstract class CommandContract : ICommand {
        public IPEndPoint Sender {
            get {
                Contract.Ensures(Contract.Result<IPEndPoint>() != null);
                return default(IPEndPoint);
            }
        }

        public void Execute(Station receiver) {
            Contract.Requires(receiver != null);
        }
    }
}
