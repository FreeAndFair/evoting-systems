/*
 * Authors: Jens
 * Team: PX3
 * Date: 12-12-2011
 */

namespace DigitalVoterList.Utilities
{
    using System;
    using System.Text;

    /// <summary>
    /// A generator that can produce random strings of a given size
    /// </summary>
    public class RandomStringGenerator
    {
        private static readonly Random random = new Random((int)DateTime.Now.Ticks);
        public static string RandomString(int size)
        {
            var builder = new StringBuilder();
            char ch;
            for (int i = 0; i < size; i++)
            {
                ch = Convert.ToChar(Convert.ToInt32(Math.Floor(26 * random.NextDouble() + 65)));
                builder.Append(ch);
            }

            return builder.ToString();
        }

    }
}
