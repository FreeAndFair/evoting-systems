/*
 * Authors: Morten
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using System.Windows;

namespace DigitalVoterList.Election.Administration
{
    //using System.Drawing;

    using System.Diagnostics;
    using System.Diagnostics.Contracts;

    using Color = System.Windows.Media.Color;

    /// <summary>
    /// Interaction logic for PrintVoterCard.xaml
    /// </summary>
    public partial class PrintVoterCard : Window
    {
        public PrintVoterCard(VoterCard voterCard)
        {
            Contract.Requires(voterCard != null);

            InitializeComponent();
            
            ElectionNameTextBlock.Text = voterCard.ElectionEvent.Name;
            VotingVenueTextBlock.Text = voterCard.Citizen.VotingPlace.Name;
            IdLabel.Content = voterCard.Id;
            BarcodeLabel.Content = voterCard.IdKey;
            BarCodeTextBlock.Text = "*"+voterCard.IdKey+"*";
            AddressTextBlock.Text = voterCard.Citizen.Name + Environment.NewLine + voterCard.Citizen.Address;
        }
    }
}