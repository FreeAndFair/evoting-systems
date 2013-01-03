using System;
using System.Collections.Generic;
using System.Linq;

namespace Aegis_DVL.Util {
    public static class Enumerable {
        /// <summary>
        /// Perform this action for every item in the collection!
        /// </summary>
        /// <typeparam name="T">The type of the items the collection holds.</typeparam>
        /// <param name="self">The collection to perform the action on.</param>
        /// <param name="lambda">The action to perform.</param>
        public static void ForEach<T>(this IEnumerable<T> self, Action<T> lambda) {
            var collection = self.ToArray();
            foreach (var item in collection)
                lambda(item);
        }
    }
}
