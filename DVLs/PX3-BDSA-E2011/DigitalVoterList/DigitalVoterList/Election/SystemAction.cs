/*
 * Authors: Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System;
using DigitalVoterList.Election;

namespace DigitalVoterList.Election
{
    public enum SystemAction
    {
        Nothing,
        AllVotingPlaces,

        CreateUser,

        LoadCitizen,
        LoadUser,
        LoadVoterCard,
        ScanVoterCard,

        FindCitizen,
        FindUser,
        FindVotingVenue,

        SaveUser,
        SetHasVoted,
        SetHasVotedManually,
        ChangeOwnPassword,
        ChangeOthersPassword,
        UpdateCitizens,
        UpdateVoterCards,

        PrintVoterCards
    }
}

public static class SystemActions
{
    public static SystemAction getSystemAction(string name)
    {
        SystemAction output;
        return Enum.TryParse(name, true, out output) ? output : SystemAction.Nothing;
    }
}
