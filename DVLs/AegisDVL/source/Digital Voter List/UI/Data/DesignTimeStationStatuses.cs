using System.Collections.Generic;

namespace UI.Data {
    public class DesignTimeStationStatuses : List<StationStatus> {
        public DesignTimeStationStatuses() {
            Add(new StationStatus { IpAdress = "127.0.0.1", Connected = true });
            Add(new StationStatus { IpAdress = "127.0.0.2", Connected = true });
            Add(new StationStatus { IpAdress = "127.0.0.3", Connected = false });
            Add(new StationStatus { IpAdress = "127.0.0.4", Connected = false });
        }
    }
}
