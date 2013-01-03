/*
 * Authors: Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using System.Windows.Media;
using DigitalVoterList.Election;
using DigitalVoterList.Views;

namespace DigitalVoterList.Controllers
{
    using System.Diagnostics.Contracts;

    /// <summary>
    /// A controller for handling the registration of voters
    /// </summary>
    public abstract class VoterRegistrationController : ContentController
    {
        private Citizen _citizen;
        public Action CitizenChanged;
        public Citizen Citizen
        {
            get { return _citizen; }
            set
            {
                SetCitizen(value);
            }
        }

        protected VoterRegistrationController(VoterRegistrationView view)
            : base(view)
        {
            Contract.Requires(view != null);
            _neededPermissions.Add(SystemAction.ScanVoterCard);
            _neededPermissions.Add(SystemAction.LoadCitizen);
            _neededPermissions.Add(SystemAction.SetHasVoted);

            Disable(_view.VoterIdentification.VoterName);
            Disable(_view.VoterIdentification.VoterAddress);
            Disable(_view.RegisterVoterButton);

            _view.StatusImageSucces.Visibility = Visibility.Hidden;
            _view.StatusImageError.Visibility = Visibility.Hidden;
            _view.StatusImageWarning.Visibility = Visibility.Hidden;

            _view.VoterIdentification.VoterCardNumber.TextChanged += VoterCardNumberChanged;
            _view.RegisterVoterButton.Click += RegisterVoterWrapper;
            _view.RegisterVoterButton.KeyDown += RegisterVoterWrapper;
        }

        private VoterRegistrationView _view
        {
            get
            {
                return (VoterRegistrationView)View;
            }
        }

        public void SetCitizen(Citizen c)
        {
            if (c == _citizen) return;
            if (c != null && c.Equals(_citizen)) return;
            _citizen = c;
            LoadVoterData();
            CheckAbilityToVote();
            CitizenChanged.Invoke();
        }

        private void RegisterVoterWrapper(object sender, EventArgs e)
        {
            if (e is KeyEventArgs && ((KeyEventArgs)e).Key != Key.Enter) return;
            RegisterVoter(sender, e);
        }

        protected abstract void RegisterVoter(object sender, EventArgs e);

        private void VoterCardNumberChanged(object sender, EventArgs e)
        {
            var voterCardNumberBox = (TextBox)sender;
            if (voterCardNumberBox.Text.Length == 8)
            {
                try
                {
                    VoterCard voterCard = DAOFactory.CurrentUserDAO.LoadVoterCard(voterCardNumberBox.Text);
                    if (voterCard != null && voterCard.Valid)
                    {
                        Citizen = voterCard.Citizen;
                    }
                    else if (voterCard != null && !voterCard.Valid)
                    {
                        ShowError("Voter card is invalid!");
                    }
                }
                catch (Exception ex)
                {
                    ShowError(ex.Message);
                }
            }
            else
            {
                Citizen = null;
            }
            CheckAbilityToVote();
            voterCardNumberBox.Text = voterCardNumberBox.Text.ToUpper();
            voterCardNumberBox.CaretIndex = 8;
        }

        private void LoadVoterData()
        {
            if (Citizen == null)
            {
                _view.VoterIdentification.VoterName.Text = "";
                _view.VoterIdentification.VoterAddress.Text = "";
                _view.VoterIdentification.VoterCprDigits.Password = "";
                Citizen = null;
            }
            else
            {
                _view.VoterIdentification.VoterName.Text = Citizen.Name;
                _view.VoterIdentification.VoterAddress.Text = Citizen.Address;
            }
            ClearStatusMessage();
        }

        protected void ClearStatusMessage()
        {
            _view.StatusText.Text = "";
            HideImages();
        }

        protected void Disable(TextBox t)
        {
            t.IsEnabled = false;
            t.IsTabStop = false;
        }

        protected void Disable(Button b)
        {
            b.IsEnabled = false;
            b.IsTabStop = false;
        }

        protected void Enable(Button b)
        {
            b.IsEnabled = true;
            b.IsTabStop = true;
        }

        protected void HideImages()
        {
            _view.StatusImageSucces.Visibility = Visibility.Hidden;
            _view.StatusImageError.Visibility = Visibility.Hidden;
            _view.StatusImageWarning.Visibility = Visibility.Hidden;
        }

        protected void ShowSuccess(string msg)
        {
            _view.StatusText.Text = msg;
            _view.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(0, 140, 0));
            _view.StatusImageSucces.Visibility = Visibility.Visible;
        }

        protected void ShowWarning(string msg)
        {
            _view.StatusText.Text = msg;
            _view.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(190, 0, 0));
            _view.StatusImageWarning.Visibility = Visibility.Visible;
        }

        protected void ShowError(string msg)
        {
            _view.StatusText.Text = msg;
            _view.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(190, 0, 0));
            _view.StatusImageError.Visibility = Visibility.Visible;
        }

        protected abstract void CheckAbilityToVote();
    }
}
