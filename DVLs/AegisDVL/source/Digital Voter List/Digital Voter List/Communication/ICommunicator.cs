using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Net;
using Aegis_DVL.Commands;

namespace Aegis_DVL.Communication {
    /// <summary>
    /// A communicator is responsible for securely passing commands between two parties.
    /// </summary>
    [ContractClass(typeof(CommunicatorContract))]
    public interface ICommunicator {
        /// <summary>
        /// Who is my parent?
        /// </summary>
        Station Parent { get; }

        /// <summary>
        /// Is this machine listening on this port?
        /// </summary>
        /// <param name="address">The address of the machine to check.</param>
        /// <returns>True if the machine is listening on the port, false otherwise.</returns>
        bool IsListening(IPEndPoint address);

        /// <summary>
        /// What are the addresses of machines in the local network?
        /// </summary>
        /// <returns>A collection of IPEndPoints containing the addresses of discovered computers.</returns>
        IEnumerable<IPEndPoint> DiscoverNetworkMachines();

        /// <summary>
        /// Send this command securely to this target!
        /// </summary>
        /// <param name="command">The command to be sent.</param>
        /// <param name="target">The target that should receive and execute the command.</param>
        void Send(ICommand command, IPEndPoint target);

        /// <summary>
        /// Receive and handle all commands!
        /// </summary>
        void ReceiveAndHandle();
    }

    [ContractClassFor(typeof(ICommunicator))]
    public abstract class CommunicatorContract : ICommunicator {
        public bool IsListening(IPEndPoint address) {
            Contract.Requires(address != null);
            return default(bool);
        }

        public IEnumerable<IPEndPoint> DiscoverNetworkMachines() {
            Contract.Ensures(Contract.Result<IEnumerable<IPEndPoint>>() != null);
            Contract.Ensures(Contract.ForAll(Contract.Result<IEnumerable<IPEndPoint>>(), x => x != null));
            return default(IEnumerable<IPEndPoint>);
        }

        public void Send(ICommand command, IPEndPoint target) {
            Contract.Requires(target != null);
            Contract.Requires(command != null);
        }

        public Station Parent {
            get {
                Contract.Ensures(Contract.Result<Station>() != null);
                return default(Station);
            }
        }

        public void ReceiveAndHandle() {
        }
    }
}
