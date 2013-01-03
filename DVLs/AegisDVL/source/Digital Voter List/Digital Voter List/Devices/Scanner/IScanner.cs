using Aegis_DVL.Data_Types;

namespace Aegis_DVL.Devices.Scanner {
    /// <summary>
    /// A scanner can read a physical voter card and extract required information from it.
    /// </summary>
    public interface IScanner {
        /// <summary>
        /// What is the voter number from this voter card?
        /// </summary>
        /// <returns>the voternumber</returns>
        VoterNumber Scan();
    }
}
