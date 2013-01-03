using System;
using System.Net;
using System.Windows;
using System.Windows.Controls;

namespace UI.StationWindows {
    /// <summary>
    /// Interaction logic for WaitingForManagerPage.xaml
    /// </summary>
    public partial class WaitingForManagerPage {
        private readonly Frame _parent;
        private readonly UiHandler _ui;
        public string TypedPassword;

        public WaitingForManagerPage(Frame parent, UiHandler ui) {
            _parent = parent;
            _ui = ui;
            InitializeComponent();
            Window.GetWindow(_parent);

            _ui.WaitingForManagerPage = this;
        }

        /// <summary>
        /// This will be called when a manager wants to connect to this station.
        /// Accessable via UIHandler.ManagerExchangingKey(IPEndPoint ip)
        /// </summary>
        /// <param name="ip">the ip adress of the manager</param>
        /// <returns>the password typed on the station</returns>
        public string IncomingConnection(IPEndPoint ip)
        {
            var amd = new AcceptManagerDialog(_parent, ip, this);
            var result = amd.ShowDialog();

            if(result.HasValue && result == true) {
                CenterLabel.Dispatcher.Invoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(delegate { CenterLabel.Content = "Venter på at valget starter..."; }));
                return TypedPassword;
            }
            return "";
        }

        /// <summary>
        /// When the manager has connected, entered the password and the station has done the same, we navigate to the next screen.
        /// </summary>
        public void StartElection() {
            _ui.WaitingForManagerPage = null;
            _parent.Navigate(new BallotRequestPage(_ui, _parent));
        }

        private void BackButtonClick(object sender, RoutedEventArgs e) {
            _ui.WaitingForManagerPage = null;
            _ui.DisposeStation();
            _parent.Navigate(new TypeChoicePage(_parent, _ui));
        }

        public void SetPasswordLabel(string content)
        {
            PasswordLabel.Content = content;
        }
    }
}
