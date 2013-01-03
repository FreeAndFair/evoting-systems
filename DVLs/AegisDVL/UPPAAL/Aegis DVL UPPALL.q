//This file was generated from (Academic) UPPAAL 4.0.13 (rev. 4577), September 2010

/*

*/
A[] forall(v:voter_t)  (!voters[0][v] imply forall(c:chan_t) !voters[c][v])

/*

*/
E<> forall(v:voter_t)  (voters[0][v] imply forall(c:chan_t) voters[c][v])

/*

*/
A[] forall(v:voter_t)  (ballotsHandedOut[v] imply forall(c:chan_t) (voters[0][v]))

/*

*/
A[] forall(v:voter_t) (ballotsHandedOut[v] <= 1)
