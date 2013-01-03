/*
 * Authors: Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using System.Windows.Media;
using DigitalVoterList.Election;
using DigitalVoterList.Utilities;
using DigitalVoterList.Views;

namespace DigitalVoterList.Controllers
{
    using System.Diagnostics.Contracts;

    /// <summary>
    /// A controller for asking random security questions for a given citizen
    /// </summary>
    public class RandomQuestionController
    {
        public event EventHandler<EventArgs> QuestionRequest;
        private Quiz[] _questions;
        private int _usedCount;
        private SecurityQuesitonView _view;

        public RandomQuestionController(SecurityQuesitonView view, Citizen voter)
        {
            Contract.Requires(view != null);
            Contract.Requires(voter != null);
            _view = view;
            _questions = new Quiz[voter.SecurityQuestions.Count];
            voter.SecurityQuestions.CopyTo(_questions);
            _usedCount = 0;
            RequestQuestion(null, null);
            QuestionRequest += RequestQuestion;
            _view._newQuestionBtn.Click += NewQuestionBtnEvent;
        }

        public void RequestQuestion(object caller, EventArgs e)
        {
            if (_questions.Length == 0)
            {
                if (_questions.Length == 0) _view.StatusText.Text = "No security quesitons could be found for this citizen.";
                _view.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(220, 0, 0));
                return;
            }
            Random r = new Random();
            int rValue = r.Next(0, _questions.Length);
            Quiz q = _questions[rValue];
            if (_questions.Length - 1 >= _usedCount)
            {
                while (_questions[rValue] == null)
                {
                    rValue = r.Next(0, _questions.Length);
                }
                SetQuestion(_questions[rValue]);
                _usedCount++;
                _questions[rValue] = null;
            }
            else
            {
                _view.StatusText.Text = "No more questions for this person";
                _view.StatusText.Foreground = new SolidColorBrush(Color.FromRgb(220, 0, 0));
            }
        }

        private void FireQuestionRequest(EventArgs e)
        {
            if (QuestionRequest != null) QuestionRequest(this, e);
        }

        private void NewQuestionBtnEvent(object sender, System.Windows.RoutedEventArgs e)
        {
            FireQuestionRequest(e);
        }

        public void SetQuestion(Quiz q)
        {
            _view.Question.Text = q.Question;
            _view.Answer.Text = q.Answer;
        }

        public void Reset()
        {
            _view.Question.Text = "";
            _view.Answer.Text = "";
        }
    }
}
