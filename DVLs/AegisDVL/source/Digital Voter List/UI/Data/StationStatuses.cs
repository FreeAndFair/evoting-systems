using System.Collections.Generic;

namespace UI.Data {
    public class StationStatuses : List<StationStatus> {
        public StationStatuses() {
            AddRange(new DesignTimeStationStatuses());
        }
    }
}
