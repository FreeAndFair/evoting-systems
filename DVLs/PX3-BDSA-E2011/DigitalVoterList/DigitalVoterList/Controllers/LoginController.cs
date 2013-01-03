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

    /// <summary>
    /// A controller for managing the login process
    /// </summary>
    public class LoginController
    {
        private LoginWindow _window;

        public LoginController(LoginWindow window)
        {
            _window = window;
            _window.LoginBtn.Click += (s, e) => Login();
            _window.KeyDown += (s, e) =>
                                 {
                                     if (e.Key == Key.Enter) Login();
                                 };
            _window.Show();
        }

        private void Login()
        {
            _window.StatusText.Text = "";
            string uname = _window.Username.Text;
            string pwd = _window.Password.Password;
            if (String.IsNullOrWhiteSpace(uname))
            {
                ShowError("Please enter a username");
                return;
            }
            if (String.IsNullOrWhiteSpace(pwd))
            {
                ShowError("Please enter a password");
                return;
            }
            try
            {
                User u = User.GetUser(uname, pwd);
                if (u == null)
                {
                    ShowError("Wrong username/password.");
                    return;
                }
                ShowSuccess("Login was successfull. Loading the Digital Voter List.");
                VoterListApp.RunApp(u);
                _window.Close();
            }
            catch (Exception ex)
            {
                ShowError(ex.Message, 10);
            }
        }

        private void ShowSuccess(string msg, int fontSize = 12)
        {
            _window.StatusText.Text = msg;
            _window.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(0, 210, 0));
            _window.StatusText.FontSize = fontSize;
        }

        private void ShowError(string msg, int fontSize = 12)
        {
            _window.StatusText.Text = msg;
            _window.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(210, 0, 0));
            _window.StatusText.FontSize = fontSize;
        }
    }
}
