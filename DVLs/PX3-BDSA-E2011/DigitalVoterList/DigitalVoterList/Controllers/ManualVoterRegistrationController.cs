/*
 * Authors: Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using System.Collections.Generic;
using System.Text.RegularExpressions;
using System.Windows;
using DigitalVoterList.Election;
using DigitalVoterList.Views;

namespace DigitalVoterList.Controllers
{
    using System.Diagnostics.Contracts;
    using System.Windows.Controls;

    /// <summary>
    /// A controller for the manual registration project
    /// </summary>
    public class ManualVoterRegistrationController : VoterRegistrationController
    {
        private readonly VoterRegistrationView _view;
        private readonly SearchCitizenController _searchController;
        private readonly SearchCitizenView _searchView;
        private readonly ManualVoterValidationController _validationController;
        private Window _currentSearchWindow;

        public ManualVoterRegistrationController(VoterRegistrationView view)
            : base(view)
        {
            Contract.Requires(view != null);

            _neededPermissions.Add(SystemAction.FindCitizen);
            _neededPermissions.Add(SystemAction.SetHasVotedManually);

            _view = view;
            _searchView = new SearchCitizenView();
            _searchView.QuitButton.Click += (s, e) =>
                {
                    _currentSearchWindow.Close();
                    _view.VoterIdentification.VoterCardNumber.Focus();
                };
            _searchController = new SearchCitizenController(_searchView);

            _view.VoterValidation.Children.Clear();
            var validationView = new ManualVoterValidationView();
            _validationController = new ManualVoterValidationController(validationView);
            _view.VoterValidation.Children.Add(validationView);
            _view.Height = 420;

            _view.VoterIdentification.VoterCardNumber.TextChanged += (s, e) =>
                {
                    if (!((TextBox)s).Text.Equals(""))
                    {
                        _view.VoterIdentification.VoterCprBirthday.Text = "";
                        _view.VoterIdentification.VoterCprDigits.Password = "";
                    }
                };
            _view.VoterIdentification.VoterCprBirthday.TextChanged += (s, e) =>
                {
                    var t = (TextBox)s;
                    if (t.Text.Length == 6)
                    {
                        _view.VoterIdentification.VoterCprDigits.Password = "";
                        _view.VoterIdentification.VoterCprDigits.Focus();
                    }
                    if (!t.Text.Equals("")) _view.VoterIdentification.VoterCardNumber.Text = "";
                    CheckCpr();
                };
            _view.VoterIdentification.VoterCprBirthday.TextChanged += DigitsOnlyText;
            _view.VoterIdentification.VoterCprDigits.PasswordChanged += (s, e) =>
                {
                    if (!((PasswordBox)s).Password.Equals("")) _view.VoterIdentification.VoterCardNumber.Text = "";
                    CheckCpr();
                };
            _view.VoterIdentification.VoterCprDigits.PasswordChanged += DigitsOnlyPassword;

            _view.SearchVoterButton.Click += (s, e) => ShowSearchVoterWindow();
            _searchController.CitizenFound += SearchCitizenFound;
            _searchView.LostFocus += (s, e) => _searchView.Focus();
            CitizenChanged += LoadVoterValidation;
        }

        private void CheckCpr()
        {
            string cprDate = _view.VoterIdentification.VoterCprBirthday.Text;
            string cprDigits = _view.VoterIdentification.VoterCprDigits.Password;
            if (cprDate.Length != 6 || cprDigits.Length != 4)
            {
                Citizen = null;
                return;
            }
            try
            {
                var result = DAOFactory.CurrentUserDAO.FindCitizens(new Dictionary<CitizenSearchParam, object>()
                                                                            {
                                                                                {CitizenSearchParam.Cpr,cprDate + cprDigits}
                                                                            }, SearchMatching.Similair);
                if (result.Count == 0)
                {
                    ShowWarning("No person found with the supplied CPR.");
                    Citizen = null;
                    return;
                }
                Citizen = result[0];
            }
            catch (Exception ex)
            {
                ShowError(ex.Message);
            }
        }

        private void ShowSearchVoterWindow()
        {
            if (_currentSearchWindow != null)
            {
                _currentSearchWindow.Focus();
                return;
            }
            var win = new Window();
            win.Content = _searchView;
            win.Closed += (s, e) =>
            {
                ((Window)s).Content = null;
                _currentSearchWindow = null;
                _searchController.Clear();
            };
            win.Height = _searchView.Height + 30;
            win.Width = _searchView.Width + 10;
            win.ResizeMode = ResizeMode.NoResize;
            win.Show();
            win.LostFocus += (s, e) => win.Focus(); //Force focus
            _currentSearchWindow = win;
        }

        private void DigitsOnlyPassword(object sender, EventArgs e)
        {
            var p = (PasswordBox)sender;
            string input = p.Password;
            string digits = Regex.Replace(input, "[^0-9]", "");
            if (!input.Equals(digits))
            {
                p.Password = digits;
            }
        }

        private void DigitsOnlyText(object sender, EventArgs e)
        {
            var t = (TextBox)sender;
            int i = t.CaretIndex - 1;
            string input = t.Text;
            string digits = Regex.Replace(input, "[^0-9]", "");
            if (!input.Equals(digits))
            {
                t.Text = digits;
                t.CaretIndex = i;
            }
        }

        private void SearchCitizenFound(Citizen c)
        {
            Citizen = c;
            _currentSearchWindow.Close();
        }

        protected void LoadVoterValidation()
        {
            if (Citizen == null)
            {
                _validationController.Clear();
                return;
            }
            _validationController.Show(Citizen);
        }

        protected override void RegisterVoter(object sender, EventArgs e)
        {
            if (Citizen == null)
            {
                ShowError("An unexpected error occured. Please try again.");
                return;
            }
            if (!Citizen.EligibleToVote)
            {
                ShowError("Citizen is not eligible to vote!");
                return;
            }
            if (Citizen.HasVoted)
            {
                ShowError("Citizen has already voted");
                return;
            }
            try
            {
                DAOFactory.CurrentUserDAO.SetHasVoted(Citizen);
                ShowSuccess("Voter registered!");
                Disable(_view.RegisterVoterButton);
                _searchView.SearchResultsGrid.Items.Refresh();
            }
            catch (Exception ex)
            {
                //SKIPPEDTODO: Log the exception for security / maintainance...
                ShowError(ex.Message);
            }
        }

        protected override void CheckAbilityToVote()
        {
            Disable(_view.RegisterVoterButton);
            if (Citizen == null) return;
            if (!Citizen.EligibleToVote)
            {
                ShowError("Citizen is not eligible to vote!");
                return;
            }
            if (Citizen.HasVoted)
            {
                ShowError("Citizen has allready voted");
                return;
            }
            Enable(_view.RegisterVoterButton);
        }
    }
}
