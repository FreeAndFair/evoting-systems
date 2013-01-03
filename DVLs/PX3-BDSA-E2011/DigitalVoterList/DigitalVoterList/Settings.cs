/*
 * Authors: Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using DigitalVoterList.Election;

namespace DigitalVoterList
{

    /// <summary>
    /// Settings for project
    /// </summary>
    public static class Settings
    {
        public static readonly string DbHost = "localhost";
        public static readonly string DbName = "PX3";
        public static readonly string DbUser = "root";
        public static readonly string DbPassword = "abcd1234";
        public static readonly ElectionEvent Election = new GeneralElection(
            new DateTime(2012, 06, 05), "Dansk Folketingsvalg, Juni 2012");
    }
}
