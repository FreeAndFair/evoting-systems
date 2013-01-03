/*
 * Authors: Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

namespace DigitalVoterList.Election
{

    /// <summary>
    /// You can search for this when seraching for citizens
    /// </summary>
    public enum CitizenSearchParam
    {
        Name, Cpr, Address, HasVoted, EligibleToVote, VotingPlace
    }

    public enum UserSearchParam
    {
        Name, Cpr, Address, HasVoted, EligibleToVote, VotingPlace
    }

    public enum VoterCardSearchParam
    {
        IdKey, CitizenId, Valid
    }

    public enum SearchMatching
    {
        Similair, Exact
    }
}
