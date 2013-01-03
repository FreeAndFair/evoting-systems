/*
 * Authors: Morten, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using System.Collections.Generic;
using System.Windows.Media;
using DigitalVoterList.Views;

namespace DigitalVoterList.Controllers
{
    using System.Diagnostics.Contracts;
    using System.Windows.Input;

    using DigitalVoterList.Election;

    class SearchCitizenController
    {
        private SearchCitizenView _view;
        private List<Citizen> _searchCitizen;
        public Action<Citizen> CitizenFound;
        public List<Citizen> SearchResult
        {
            get { return new List<Citizen>(_searchCitizen); }
        }

        public SearchCitizenController(SearchCitizenView view)
        {
            Contract.Requires(view != null);

            _view = view;

            _view.SearchButton.Click += (s, e) => Search();
            _view.KeyDown += (s, e) =>
                                    {
                                        if (e.Key == Key.Enter) Search();
                                    };

            _view.SelectButton.Click += (s, e) => Select();
            _view.SearchResultsGrid.MouseDoubleClick += (s, e) => Select();

            _view.addressTextBox.TextChanged += (s, e) => _view.statusTextBlock.Text = "";
            _view.nameTextBox.TextChanged += (s, e) => _view.statusTextBlock.Text = "";
            _view.cprTextBox.TextChanged += (s, e) => _view.statusTextBlock.Text = "";
        }

        /// <summary>
        /// Clear the listbox and the textblocks in the view
        /// </summary>
        public void Clear()
        {
            _searchCitizen = null;
            LoadListBox();
            _view.nameTextBox.Text = "";
            _view.addressTextBox.Text = "";
            _view.cprTextBox.Text = "";
        }

        /// <summary>
        /// Search for a person with the information inserted in the textblocks and insert
        /// every person as an item in the listbox
        /// </summary>
        public void Search()
        {
            _view.statusTextBlock.Text = "";
            var searchParams = new Dictionary<CitizenSearchParam, object>();
            if (_view.nameTextBox.Text != "")
            {
                searchParams.Add(CitizenSearchParam.Name, _view.nameTextBox.Text);
            }
            if (_view.addressTextBox.Text != "")
            {
                searchParams.Add(CitizenSearchParam.Address, _view.addressTextBox.Text);
            }
            if (_view.cprTextBox.Text != "")
            {
                searchParams.Add(CitizenSearchParam.Cpr, _view.cprTextBox.Text);
            }
            if (searchParams.Count > 0)
            {
                try
                {
                    _searchCitizen = DAOFactory.CurrentUserDAO.FindCitizens(searchParams, SearchMatching.Similair);
                    if (_searchCitizen.Count == 0)
                    {
                        _view.statusTextBlock.Text = "No citizens found with the specified information";
                        return;
                    }
                }
                catch (Exception ex)
                {
                    _view.statusTextBlock.Text = ex.Message;
                    _view.statusTextBlock.Foreground = new SolidColorBrush(Color.FromRgb(210, 0, 0));
                }
            }
            LoadListBox();
        }

        private void LoadListBox()
        {
            var citizenData = new List<CitizenData>();
            if (_searchCitizen != null)
            {
                foreach (var c in _searchCitizen)
                {
                    citizenData.Add(new CitizenData()
                                        {
                                            Name = c.Name,
                                            Address = c.Address,
                                            Cpr = c.Cpr,
                                            EligibleToVote = c.EligibleToVote,
                                            HasVoted = c.HasVoted
                                        });
                }
            }
            _view.SearchResultsGrid.ItemsSource = citizenData;
        }

        /// <summary>
        /// Invoke the Citizen found event with the currently selected citizen from the search results
        /// </summary>
        private void Select()
        {
            int index = _view.SearchResultsGrid.SelectedIndex;
            if (index < 0 || _searchCitizen == null || index >= _searchCitizen.Count) return;
            CitizenFound.Invoke(_searchCitizen[index]);
        }

        /// <summary>
        /// A struct to make the datagrid with the right columns
        /// </summary>
        struct CitizenData
        {
            public string Name { get; set; }
            public string Address { get; set; }
            public string Cpr { get; set; }
            public bool EligibleToVote { get; set; }
            public bool HasVoted { get; set; }
        }
    }
}
