/*
 * Authors: Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using System.Windows.Input;
using System.Windows.Media;
using DigitalVoterList.Election;
using DigitalVoterList.Views;

namespace DigitalVoterList.Controllers
{
    using System.Diagnostics.Contracts;

    /// <summary>
    /// A controller to handle change of password
    /// </summary>
    public class ChangeOwnPasswordController
    {
        private ChangePasswordWindow _view;

        public ChangeOwnPasswordController(ChangePasswordWindow view)
        {
            Contract.Requires(view != null);
            _view = view;
            _view.SaveBtn.Click += ChangePassword;
            _view.KeyDown += ChangePassword;
        }

        private void ChangePassword(object sender, EventArgs e)
        {
            if (e is KeyEventArgs && ((KeyEventArgs)e).Key != Key.Enter) return;
            if (_view.OldPassword.Password.Length == 0)
            {
                ShowError("Please enter your old password");
                return;
            }
            if (_view.NewPassword.Password.Length == 0)
            {
                ShowError("Please enter your new password");
                return;
            }
            if (_view.RepeatNewPassword.Password.Length == 0)
            {
                ShowError("Please repeat your new password");
                return;
            }
            if (!_view.NewPassword.Password.Equals(_view.RepeatNewPassword.Password))
            {
                ShowError("New passwords are different");
                return;
            }
            if (User.GetUser(VoterListApp.CurrentUser.Username, _view.OldPassword.Password) == null)
            {
                ShowError("The supplied old password is not correct");
                return;
            }

            try
            {
                VoterListApp.CurrentUser.ChangePassword(_view.OldPassword.Password, _view.NewPassword.Password);
                ShowSuccess("Password changed.");
            }
            catch (Exception ex)
            {
                ShowError(ex.Message, 10);
            }
        }

        public void ShowError(string msg, int fontSize = 12)
        {
            _view.StatusText.Text = msg;
            _view.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(215, 0, 0));
            _view.StatusText.FontSize = fontSize;
        }

        public void ShowSuccess(string msg, int fontSize = 12)
        {
            _view.StatusText.Text = msg;
            _view.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(0, 215, 0));
            _view.StatusText.FontSize = fontSize;
        }
    }
}
