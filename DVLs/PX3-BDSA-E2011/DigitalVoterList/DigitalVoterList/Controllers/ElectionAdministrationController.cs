/*
 * Authors:Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System.Windows.Media;
using DigitalVoterList.Election;
using DigitalVoterList.Election.Administration;
using DigitalVoterList.Views;

namespace DigitalVoterList.Controllers
{
    using System;
    using System.Diagnostics.Contracts;

    /// <summary>
    /// Controller for collection administration
    /// </summary>
    public class ElectionAdministrationController : ContentController
    {

        public ElectionAdministrationController(ElectionAdministrationView view)
            : base(view)
        {
            Contract.Requires(view != null);
            _neededPermissions.Add(SystemAction.AllVotingPlaces);
            _neededPermissions.Add(SystemAction.LoadCitizen);
            _neededPermissions.Add(SystemAction.LoadVoterCard);
            _neededPermissions.Add(SystemAction.FindCitizen);
            _neededPermissions.Add(SystemAction.FindVotingVenue);
            _neededPermissions.Add(SystemAction.UpdateCitizens);
            _neededPermissions.Add(SystemAction.UpdateVoterCards);
            _neededPermissions.Add(SystemAction.PrintVoterCards);

            _view.ImportDataBtn.Click += (s, e) => ImportData();
            _view.UpdateVoterCardsBtn.Click += (s, e) => UpdateVoterCards();
            _view.PrintVoterCardsBtn.Click += (s, e) => PrintVoterCards();
            _view.LostFocus += (s, e) => _view.StatusTextBox.Text = "";
        }

        private ElectionAdministrationView _view
        {
            get
            {
                return (ElectionAdministrationView)View;
            }
        }

        /// <summary>
        /// Imports data from the raw person information to the correct tables in the database
        /// </summary>
        private void ImportData()
        {
            _view.StatusTextBox.Text = "";
            try
            {
                var dataTransformer = new DataTransformer();
                dataTransformer.TransformData();
                ShowSuccess("Data was successfully imported.");
            }
            catch (Exception ex)
            {
                ShowError(ex.Message + ". Data could not be imported.");
            }
        }

        /// <summary>
        /// Updates the votercards in the database
        /// </summary>
        private void UpdateVoterCards()
        {
            _view.StatusTextBox.Text = "";
            try
            {
                DAOFactory.CurrentUserDAO.UpdateVoterCards();
                ShowSuccess("Voter cards was successfully updated.");
            }
            catch (Exception ex)
            {
                ShowError(ex.Message + ". Voter cards could not be updated.");
            }
        }

        /// <summary>
        /// Prints the votercards in the database
        /// </summary>
        private void PrintVoterCards()
        {
            _view.StatusTextBox.Text = "";
            try
            {
                var printer = new VoterCardPrinter();
                DAOFactory.CurrentUserDAO.PrintVoterCards(printer);
                ShowSuccess("All voter cards printed successfully");
            }
            catch (Exception ex)
            {
                ShowError(ex.Message + ". Some voter cards may not have been printed.");
            }
        }

        public void ShowSuccess(string msg, int fontSize = 14)
        {
            _view.StatusTextBox.Text = msg;
            _view.StatusTextBox.Foreground = new SolidColorBrush(Color.FromRgb(0, 190, 0));
            _view.StatusTextBox.FontSize = fontSize;
        }

        public void ShowError(string msg, int fontSize = 14)
        {
            _view.StatusTextBox.Text = msg;
            _view.StatusTextBox.Foreground = new SolidColorBrush(Color.FromRgb(190, 0, 0));
            _view.StatusTextBox.FontSize = fontSize;
        }
    }
}
