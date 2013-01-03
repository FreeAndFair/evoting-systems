using System;
using System.Windows;
using System.Windows.Controls;
using UI.ManagerWindows;
using UI.StationWindows;

namespace UI
{
    /// <summary>
    /// Interaction logic for TypeChoicePage.xaml
    /// </summary>
    public partial class TypeChoicePage
    {
        private readonly Frame _parent;
        private readonly UiHandler _ui;

        /// <summary>
        /// Constructor
        /// </summary>
        /// <param name="parent">the frame in which this page is displayed</param>
        /// <param name="ui">the UIhandler of this UI</param>
        public TypeChoicePage(Frame parent, UiHandler ui)
        {
            _parent = parent;
            _ui = ui;
            InitializeComponent();
        }

        /// <summary>
        /// Called when the station option is chosen
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void StationButtonClick(object sender, RoutedEventArgs e)
        {
            _ui.CreateNewStation();
            _parent.Navigate(new WaitingForManagerPage(_parent, _ui));
        }

        /// <summary>
        /// Called when the manager option is chosen
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void ManagerButtonClick(object sender, RoutedEventArgs e)
        {
            _parent.Navigate(new MasterPasswordPage(_parent, _ui));
        }

        /// <summary>
        /// Called when the exit button is pressed
        /// </summary>
        /// <param name="sender">auto generated</param>
        /// <param name="e">auto generated</param>
        private void ExitButtonClick(object sender, RoutedEventArgs e)
        {
            Environment.Exit(0);
        }
    }
}
