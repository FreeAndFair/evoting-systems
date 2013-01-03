/*
 * Authors: Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System.Collections.Generic;
using DigitalVoterList.Election;
using DigitalVoterList.Utilities;
using DigitalVoterList.Views;

namespace DigitalVoterList.Controllers
{
    using System.Diagnostics.Contracts;

    class ManualVoterValidationController
    {
        private ManualVoterValidationView _view;

        public ManualVoterValidationController(ManualVoterValidationView view)
        {
            Contract.Requires(view != null);
            _view = view;
            _view.QuestionsGrid.FontSize = 14;
        }

        public void Show(Citizen c)
        {
            if (c == null) return;
            _view.QuestionsGrid.ItemsSource = new List<Quiz>(c.SecurityQuestions);
            _view.Cpr.Text = c.Cpr.Substring(1, 6) + " - " + c.Cpr.Substring(6, 4);
            _view.PassportNumber.Text = c.PassportNumber;
            _view.PlaceOfBirth.Text = c.PlaceOfBirth;
            _view.EliglbeToVote.Text = c.EligibleToVote ? "Yes" : "No";
            _view.HasVoted.Text = c.HasVoted ? "Yes" : "No";
        }

        public void Clear()
        {
            _view.Cpr.Text = "";
            _view.PassportNumber.Text = "";
            _view.PlaceOfBirth.Text = "";
            _view.EliglbeToVote.Text = "";
            _view.HasVoted.Text = "";
            _view.QuestionsGrid.ItemsSource = new List<Quiz>();
        }
    }
}
