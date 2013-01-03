/*
 * Authors: Michael
 * Team: PX3
 * Date: 12-12-2011
 * Rights: LBushkin@http://stackoverflow.com/questions/1563191/c-sharp-cleanest-way-to-write-retry-logic
 */



using System;
using System.Threading;

namespace DigitalVoterList.Utilities
{
    /// <summary>
    /// A simple, static class to retry actions
    /// </summary>
    public static class RetryUtility
    {
        /// <summary>
        /// Try this action (and retry if neces)!
        /// </summary>
        /// <param name="act">The action to try</param>
        /// <param name="retries">The number of retries before giving up, 0 means infinite.</param>
        /// <param name="timeout">A timeout time in milliseconds to wait between each retry (0 means don't wait)</param>
        public static void RetryAction(Action act, int retries = 0, int timeout = 0)
        {
            act = act ?? (() => { });
            do
            {
                try
                {
                    act();
                    return;
                }
                catch
                {
                    if (retries <= 0) throw;
                    else Thread.Sleep(timeout);
                }
            } while (retries-- > 0);
        }
    }
}