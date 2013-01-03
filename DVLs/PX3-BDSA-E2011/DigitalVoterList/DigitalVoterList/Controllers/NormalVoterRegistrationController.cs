/*
 * Authors: Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System.Windows;
using System.Windows.Controls;
using DigitalVoterList.Election;
using DigitalVoterList.Views;

namespace DigitalVoterList.Controllers
{
    using System;
    using System.Diagnostics.Contracts;

    /// <summary>
    /// A controller to handle normal voter registration with cpr-digits as extra security measure and no ability to search.
    /// </summary>
    public class NormalVoterRegistrationController : VoterRegistrationController
    {
        private readonly VoterRegistrationView _view;
        private int _cprTries = 0;

        public NormalVoterRegistrationController(VoterRegistrationView view)
            : base(view)
        {
            Contract.Requires(view != null);
            _view = view;
            _view.Height = 314;

            Disable(_view.VoterIdentification.VoterCprBirthday);
            _view.VoterIdentification.VoterCprBirthday.Text = "XXXXXX";
            Disable(_view.RegisterVoterButton);
            _view.SearchVoterButton.Visibility = Visibility.Hidden;

            _view.VoterValidation.Children.Clear();
            _view.VoterValidation.Children.Add(new SecurityQuesitonView());

            _view.VoterIdentification.VoterCprDigits.PasswordChanged += CheckCpr;

            base.CitizenChanged += LoadVoterValidation;
            base.CitizenChanged += () =>
                                       {
                                           _view.VoterIdentification.VoterCprDigits.Password = "";
                                           _cprTries = 0;
                                       };
        }

        private void CheckCpr(object sender, EventArgs e)
        {
            _view.VoterIdentification.CprSuccessImage.Visibility = Visibility.Hidden;
            CheckAbilityToVote();
            string cprDigits = _view.VoterIdentification.VoterCprDigits.Password;

            if (cprDigits.Length != 4 || Citizen == null) { return; }

            string checkCprDigits = Citizen.Cpr.Substring(6, 4);
            if (cprDigits.Equals(checkCprDigits) && _cprTries < 3)
            {
                ClearStatusMessage();
                _cprTries = -1;
                _view.VoterIdentification.CprSuccessImage.Visibility = Visibility.Visible;
            }
            else
            {
                ShowWarning("The last four digits of the cpr number are wrong. Try again");
                _view.VoterIdentification.VoterCprDigits.Password = "";
            }

            _cprTries++;

            if (_cprTries > 2)
            {
                ShowError("The maximum number of tries exceeded. Go to manual validation");
            }
        }

        private void LoadVoterValidation()
        {
            _view.VoterValidation.Children.Clear();
            var questionView = new SecurityQuesitonView();
            _view.VoterValidation.Children.Add(questionView);
            if (Citizen != null)
            {
                new RandomQuestionController(questionView, Citizen);
            }
        }

        protected override void RegisterVoter(object sender, EventArgs e)
        {
            if (Citizen == null)
            {
                ShowWarning("No person found with the inserted information");
                return;
            }
            if (Citizen.HasVoted)
            {
                ShowError("Voter has allready voted!");
                return;
            }
            if (!Citizen.EligibleToVote)
            {
                ShowError("Citizen is not eligible to vote!");
                return;
            }
            string cprDigits = _view.VoterIdentification.VoterCprDigits.Password;
            if (!Citizen.Cpr.Substring(6, 4).Equals(cprDigits))
            {
                ShowError("CPR-Digits are incorrect!");
                return;
            }
            try
            {
                DAOFactory.CurrentUserDAO.SetHasVoted(Citizen, cprDigits);
                ShowSuccess("Citizen registered!");
                Disable(_view.RegisterVoterButton);
            }
            catch (Exception ex)
            {
                //SKIPPEDTODO: Log the exception for security / maintainance...
                ShowError(ex.Message);
            }
        }

        protected override void CheckAbilityToVote()
        {
            Button regBtn = _view.RegisterVoterButton;
            Disable(regBtn);
            if (Citizen == null) return;
            if (Citizen.HasVoted)
            {
                ShowError("Citizen has already voted!");
                return;
            }
            if (!Citizen.EligibleToVote)
            {
                ShowError("Citizen is not eligible to vote!");
                return;
            }
            if (_view.VoterIdentification.VoterCprDigits.Password.Length != 4) return;
            if (!_view.VoterIdentification.VoterCprDigits.Password.Equals(Citizen.Cpr.Substring(6, 4))) return;
            Enable(regBtn);
        }
    }
}