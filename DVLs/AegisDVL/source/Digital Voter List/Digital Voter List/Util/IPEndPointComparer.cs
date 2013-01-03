using System.Collections.Generic;
using System.Net;

namespace Aegis_DVL.Util {
    /// <summary>
    /// A IPEndPointComparer is used to compare IPEndPoints with eachother.
    /// </summary>
    public class IPEndPointComparer : IComparer<IPEndPoint> {
        public int Compare(IPEndPoint x, IPEndPoint y) {
            return System.String.CompareOrdinal(x.ToString(), y.ToString());
        }
    }
}
