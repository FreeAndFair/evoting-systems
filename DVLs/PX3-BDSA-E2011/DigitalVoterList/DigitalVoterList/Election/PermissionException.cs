/*
 * Authors: Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

namespace DigitalVoterList.Election
{
    using System;

    /// <summary>
    /// Exception for indicating a permission violation. That is when a user tries to access a method, which he has no permission to use.
    /// </summary>
    public class PermissionException : Exception
    {
        private readonly SystemAction _systemAction;
        private readonly User _user;

        public PermissionException(SystemAction systemAction, User user, string msg = "You don't have permission to perform this SystemAction.")
            : base(msg)
        {
            _systemAction = systemAction;
            _user = user;
        }

        public PermissionException(User user, string msg = "You don't have permission to do this.")
            : base(msg)
        {
            _user = user;
        }

        public SystemAction SystemAction { get; private set; }

        public User User { get; private set; }
    }
}
