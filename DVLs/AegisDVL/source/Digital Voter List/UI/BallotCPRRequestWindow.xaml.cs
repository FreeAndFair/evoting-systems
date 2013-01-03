
using System;
using System.Windows;
using System.Windows.Input;
using UI.ManagerWindows;

namespace UI
{
    /// <summary>
    /// Interaction logic for BallotCPRRequestWindow.xaml
    /// </summary>
    public partial class BallotCPRRequestWindow
    {
        private readonly UiHandler _ui;

        /// <summary>
        /// Constructor
        /// </summary>
        /// <param name="ui">the UIHandler of the UI</param>
        public BallotCPRRequestWindow(UiHandler ui)
        {
            _ui = ui;
            _ui.BallotCPRRequestWindow = this;
            InitializeComponent();
            doneButton.IsEnabled = false;
            WaitingLabel.Content = "";
            Focus();
            Title = "CPR";
        }

        /// <summary>
        /// Called when the Done button is clicked
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void DoneButtonClick(object sender, RoutedEventArgs e)
        {
            var d = new CheckMasterPasswordDialog(_ui);
            d.ShowDialog();

            if (d.DialogResult.HasValue && d.DialogResult == true)
            {
                if (d.IsCancel)
                    return;

                if (!CPRTextbox.Text.Equals(""))
                {
                    WaitingLabel.Content = "Venter på svar...";
                    doneButton.IsEnabled = false;
                    CancelButton.IsEnabled = false;
                    _ui.RequestBallotOnlyCPR(CPRTextbox.Text, d.TypedPassword);
                }
            }
            else
            {
                MessageBox.Show("Det kodeord du indtastede er ikke korret, prøv igen", "Forkert Master Kodeord", MessageBoxButton.OK);
            }
        }

        /// <summary>
        /// Used to check that only number can be typed in the textboxes
        /// </summary>
        /// <param name="text"></param>
        /// <returns></returns>
        private static bool IsNumeric(string text)
        {
            int result;
            return int.TryParse(text, out result);
        }

        /// <summary>
        /// When someone typed something into a textbox this is called
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void PreviewTextInputHandler(Object sender, TextCompositionEventArgs e)
        {
            e.Handled = !IsNumeric(e.Text);
        }

        /// <summary>
        /// When someone pastes something into a textbox this is called
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void PastingHandler(object sender, DataObjectPastingEventArgs e)
        {
            if (e.DataObject.GetDataPresent(typeof(String)))
            {
                var text = (String)e.DataObject.GetData(typeof(String));
                if (!IsNumeric(text)) e.CancelCommand();
            }
            else e.CancelCommand();
        }

        /// <summary>
        /// Called when the Text in the CPRTextBox changes
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void CPRTextboxTextChanged(object sender, System.Windows.Controls.TextChangedEventArgs e)
        {
            if (CPRTextbox.Text.Length == 10 && WaitingLabel.Content.Equals(""))
                doneButton.IsEnabled = true;
            else
            {
                doneButton.IsEnabled = false;
            }
        }

        /// <summary>
        /// Called when the station object replies to a ballot request
        /// </summary>
        /// <param name="succes">whether a ballot can be handed out or not </param>
        public void BallotResponse(bool succes)
        {
            _ui.BallotCPRRequestWindow = null;

            if (succes)
            {
                WaitingLabel.Content = "";
                doneButton.IsEnabled = true;
                CancelButton.IsEnabled = true;
                MessageBox.Show("Vælgeren " + CPRTextbox.Text + " Må gives en stemmeseddel ", "Giv stemmeseddel",
                                MessageBoxButton.OK);
            }
            else{
            
                WaitingLabel.Content = "";
                doneButton.IsEnabled = true;
                CancelButton.IsEnabled = true;
                MessageBox.Show("Vælgeren " + CPRTextbox.Text + " Må IKKE gives en stemmeseddel ", "Giv ikke stemmeseddel", MessageBoxButton.OK, MessageBoxImage.Stop);
            }

            Close();
        }

        /// <summary>
        /// Called when the cancel button is pressed
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void CancelButtonClick(object sender, RoutedEventArgs e)
        {
            _ui.BallotCPRRequestWindow = null;
            Close();
        }
    }
}
