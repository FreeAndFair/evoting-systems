using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Net;
using System.Net.Sockets;
using System.Threading;
using Aegis_DVL.Commands;
using Aegis_DVL.Data_Types;
using Aegis_DVL.Util;

namespace Aegis_DVL.Communication {
    public class Communicator : ICommunicator {

        /// <summary>
        /// May I have a new Communicator?
        /// </summary>
        /// <param name="parent">The parent station of the communicator.</param>
        public Communicator(Station parent) {
            Contract.Requires(parent != null);
            Parent = parent;
        }

        public Station Parent { get; private set; }

        public void Send(ICommand command, IPEndPoint target) {
            if(Parent.Logger != null && !(command is IsAliveCommand))
                Parent.Logger.Log("Attempting to send " + command.GetType() + " to " + target, Level.Info);
            var isBallotReceived = command is BallotReceivedCommand || command is BallotReceivedCPROnlyCommand;

            if(!(command is PublicKeyExchangeCommand || command is IsAliveCommand || command is CryptoCommand))
                command = new CryptoCommand(Parent, target, command);
            try {
                using(var client = new TcpClient()) {
                    var ar = client.BeginConnect(target.Address, target.Port, null, null);
                    var wh = ar.AsyncWaitHandle;
                    try {
                        if(!ar.AsyncWaitHandle.WaitOne(TimeSpan.FromMilliseconds(1000), false)) {
                            throw new SocketException();
                        }
                        client.EndConnect(ar);
                    }
                    finally {
                        wh.Close();
                    }

                    var bytes = Bytes.From(command);
                    const int packetSize = 2048;
                    var packetAmount = (int)Math.Ceiling((double)bytes.Length / packetSize);
                    using(var stream = client.GetStream()) {
                        for(var i = 0; i < packetAmount; i++) {
                            var offset = i * packetSize;
                            var size = (i == packetAmount - 1 ? bytes.Length % packetSize : packetSize);
                            stream.Write(bytes, offset, size);
                        }
                    }
                }
            }
            catch(SocketException) {
                if(command is IsAliveCommand || isBallotReceived)
                    throw;
                if(Parent.Logger != null)
                    Parent.Logger.Log("SocketException thrown while sending, attempting to handle.", Level.Error);
                if(Parent.IsManager && Parent.Peers.ContainsKey(target))
                    Parent.AnnounceRemovePeer(target);
                else if(target.Equals(Parent.Manager)) {
                    Parent.StartNewManagerElection();
                    Send(command, target);
                }
                else if(Parent.Peers.ContainsKey(target))
                    Parent.RemovePeer(target);
            }
            catch(IOException) {
                if(Parent.Logger != null)
                    Parent.Logger.Log("Problem sending due to IOException, retrying send.", Level.Error);
                Send(command, target);
            }
        }

        public void ReceiveAndHandle() {
            var listener = new TcpListener(Parent.Address);
            listener.Start();
            try {
                using(var client = listener.AcceptTcpClient()) {
                    using(var stream = client.GetStream()) {
                        var bytes = Bytes.FromNetworkStream(stream);
                        if(bytes.Length == 0)
                            return;
                        var cmd = bytes.To<ICommand>();
                        if(cmd is PublicKeyExchangeCommand || cmd is CryptoCommand || cmd is IsAliveCommand) {
                            if(Parent.Logger != null && !(cmd is IsAliveCommand))
                                Parent.Logger.Log("Received " + cmd.GetType() + " from " + cmd.Sender, Level.Info);
                            cmd.Execute(Parent);
                        }
                        else {
                            if(Parent.Logger != null)
                                Parent.Logger.Log("Received a command that wasn't PublicKeyExchangeCommand, CryptoCommand or IsAliveCommand from " + client.Client.RemoteEndPoint + ". Shutting down.", Level.Fatal);
                            Parent.ShutDownElection();
                        }
                    }
                }
            }
            finally {
                listener.Stop();
            }
        }

        [Pure]
        public bool IsListening(IPEndPoint address) {
            try {
                Send(new IsAliveCommand(Parent.Address), address);
            }
            catch(SocketException) {
                return false;
            }
            return true;
        }

        [Pure]
        public IEnumerable<IPEndPoint> DiscoverNetworkMachines() {
            var res = new List<IPEndPoint>();
            using(var e = new CountdownEvent(1)) {
                for(var i = 1; i < 255; i++) {
                    e.AddCount();
                    ThreadPool.QueueUserWorkItem(element => {
                        var elem = (Tuple<int, CountdownEvent>)element;
                        var endpoint = new IPEndPoint(IPAddress.Parse("192.168.1." + elem.Item1), 62000);
                        if(IsListening(endpoint))
                            res.Add(endpoint);
                        elem.Item2.Signal();
                    }, new Tuple<int, CountdownEvent>(i, e));
                }
                e.Signal();
                e.Wait();
            }
            return res;
        }
    }
}