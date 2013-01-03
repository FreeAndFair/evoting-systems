using System;
using System.Windows;
using Microsoft.Win32;
using UI.ManagerWindows;

namespace UI {
    /// <summary>
    /// Interaction logic for StationWindow.xaml
    /// </summary>
    public partial class StationWindow
    {
        private readonly UiHandler _ui;

        /// <summary>
        /// Constructor
        /// </summary>
        public StationWindow()
        {
            InitializeComponent();
            _ui = new UiHandler(this);
            MainFrame.Navigate(new TypeChoicePage(MainFrame,_ui));
        }

        /// <summary>
        /// Make sure that the red X in the corner doesn't close the window
        /// </summary>
        /// <param name="e">the event argument</param>
        protected override void OnClosing(System.ComponentModel.CancelEventArgs e) {
            e.Cancel = true;
        }

        /// <summary>
        /// Called when File -> Mark voter is clicked
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void MarkVoterClick(object sender, RoutedEventArgs e)
        {
            var ballotCPRRequestWindow = new BallotCPRRequestWindow(_ui);
            ballotCPRRequestWindow.ShowDialog();
        }

        /// <summary>
        /// Called whn File -> Export data is clicked
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void ExportDataClick(object sender, RoutedEventArgs e)
        {         
            var d = new CheckMasterPasswordDialog(_ui);
            d.ShowDialog();

            if (d.DialogResult.HasValue && d.DialogResult == true)
            {
                if(d.IsCancel)
                    return;

                var saveDialog = new SaveFileDialog {Title = "Eksporter Valg Data"};
                saveDialog.Filter = "Data files (*.data)|*.data|All files (*.*)|*.*";
                saveDialog.ShowDialog();
                if(!saveDialog.FileName.Equals(""))
                    _ui.ExportData(saveDialog.FileName);
            }
            else
            {
                MessageBox.Show("Det kodeord du indtastede er ikke korrekt, prøv igen", "Forkert Master Kodeord", MessageBoxButton.OK);
            }
        }

        /// <summary>
        /// Called when File -> Exit is clicked
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void ExitClick(object sender, RoutedEventArgs e)
        {
            var d = new CheckMasterPasswordDialog(_ui);
            d.ShowDialog();

            if (d.DialogResult.HasValue && d.DialogResult == true)
            {
                if (d.IsCancel)
                    return;

                Environment.Exit(0);
            }
            else
            {
                MessageBox.Show("Det kodeord du indtastede er ikke korret, prøv igen", "Forkert Master Kodeord", MessageBoxButton.OK);
            }
        }

        /// <summary>
        /// Called when Help -> User Manual is clicked
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void HelpClick(object sender, RoutedEventArgs e)
        {
            System.Diagnostics.Process.Start(@"Manual.pdf");
        }

    }
}
