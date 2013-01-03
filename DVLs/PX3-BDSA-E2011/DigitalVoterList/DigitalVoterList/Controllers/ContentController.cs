/*
 * Authors: Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System.Collections.Generic;
using System.Windows.Controls;
using DigitalVoterList.Election;

namespace DigitalVoterList.Controllers
{
    using System.Diagnostics.Contracts;

    /// <summary>
    /// General behavior for system controls
    /// </summary>
    public partial class ContentController
    {
        protected HashSet<SystemAction> _neededPermissions;
        public UserControl View { get; private set; }

        public ContentController(UserControl view)
            : base()
        {
            Contract.Requires(view != null);
            View = view;
            _neededPermissions = new HashSet<SystemAction>();
        }

        public bool HasPermissionToUse(User u)
        {
            Contract.Requires(u != null);
            return u.Permissions.IsSupersetOf(_neededPermissions);
        }

        [ContractInvariantMethod]
        [System.Diagnostics.CodeAnalysis.SuppressMessage("Microsoft.Performance", "CA1822:MarkMembersAsStatic", Justification = "Required for code contracts.")]
        private void ObjectInvariant()
        {
            Contract.Invariant(View != null);
            Contract.Invariant(_neededPermissions != null);
        }
    }
}
