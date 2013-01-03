using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using UI.Data;


namespace UI
{
    /// <summary>
    /// Interaction logic for ManagerOverview.xaml
    /// </summary>
    public partial class ManagerOverview : Page
    {
        public ManagerOverview()
        {
            InitializeComponent();
            var ss = new StationStatuses();
            ss.Clear();
            
            ss.Add(new StationStatus { IpAdress = "lolllll", Connected = true});
            ss.Add(new StationStatus { IpAdress = "lollll2l", Connected = false });

            ManagerstationGrid.ItemsSource = ss;
        }

        private void ManagerRemoveButtonClick(object sender, RoutedEventArgs e)
        {
            if (ManagerstationGrid.SelectedItem != null)
            {
                //((StationStatus) stationGrid.SelectedItem).Connected = false;
                ManagerstationGrid.Items.Refresh();
            }
        }

        private void ManagerAddButtonClick(object sender, RoutedEventArgs e)
        {
            if (ManagerstationGrid.SelectedItem != null)
            {
                //((StationStatus) stationGrid.SelectedItem).Connected = true;
                ManagerstationGrid.Items.Refresh();
            }
        }

        private void CheckValidityButtonClick(object sender, RoutedEventArgs e)
        {
            Environment.Exit(0);
        }

        private static bool IsNumeric(string text)
        {
            int result;
            return int.TryParse(text, out result);
        }

        private void PreviewTextInputHandler(Object sender, TextCompositionEventArgs e)
        {
            e.Handled = !IsNumeric(e.Text);
        }

        // Use the DataObject.Pasting Handler 
        private void PastingHandler(object sender, DataObjectPastingEventArgs e)
        {
            if (e.DataObject.GetDataPresent(typeof(String)))
            {
                var text = (String)e.DataObject.GetData(typeof(String));
                if (!IsNumeric(text)) e.CancelCommand();
            }
            else e.CancelCommand();
        }

    }
}
