using System;
using System.Collections.Generic;

namespace Vec.Apps.Nominations
{
    public static class BallotDrawHelper
    {
        private static readonly Random random = new Random();
        private static readonly object syncLock = new object(); 

        public static int[] GenerateRandomPositions(int count)
        {
            if (count <= 0)
                throw new ArgumentOutOfRangeException("count");

            lock (syncLock)
            {
                var positions = new List<int>(count);

                for (int i = 0; i < count; i++)
                {
                    int next;
                    do
                    {
                        next = random.Next(1, count + 1);
                    } while (positions.Contains(next));

                    positions.Add(next);
                }
                return positions.ToArray();
            }
        }
    }
}
