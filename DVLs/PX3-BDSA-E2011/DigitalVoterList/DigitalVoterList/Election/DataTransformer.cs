/*
 * Authors: Jens
 * Team: PX3
 * Date: 12-12-2011
 */

namespace DigitalVoterList.Election
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics.Contracts;

    using DigitalVoterList.Utilities;

    /// <summary>
    /// An importer able to import the raw data in to our database
    /// </summary>
    public class DataTransformer
    {
        public void TransformData()
        {
            Contract.Requires(DAOFactory.Ready);
            DAOFactory.CurrentUserDAO.UpdatePeople(this.UpdateCitizen);
        }

        /// <summary>
        /// What citizen would I get if I gave him/her this rawPersons information?
        /// </summary>
        /// <param name="person"></param>
        /// <param name="rawPerson"></param>
        /// <returns></returns>
        private Citizen UpdateCitizen(Citizen citizen, RawPerson rawPerson)
        {
            citizen.Name = rawPerson.Name;
            citizen.Cpr = rawPerson.CPR;
            citizen.Address = rawPerson.Address;
            citizen.PassportNumber = rawPerson.PassportNumber;
            citizen.PlaceOfBirth = rawPerson.Birthplace;
            citizen.EligibleToVote = Settings.Election.CitizenEligibleToVote(rawPerson);
            citizen.SecurityQuestions = this.GenerateSecurityQuestions(rawPerson);
            citizen.VotingPlace = Settings.Election.VotingVenueForCitizen(rawPerson);
            return citizen;
        }

        private HashSet<Quiz> GenerateSecurityQuestions(RawPerson rawPerson)
        {
            Contract.Ensures(Contract.Result<HashSet<Quiz>>() != null);

            var quizzes = new HashSet<Quiz>();

            if (!String.IsNullOrEmpty(rawPerson.Birthplace)) quizzes.Add(new Quiz("Where were you born?", rawPerson.Birthplace));
            if (!String.IsNullOrEmpty(rawPerson.Education)) quizzes.Add(new Quiz("What is your education?", rawPerson.Education));
            if (!String.IsNullOrEmpty(rawPerson.Address) && !String.IsNullOrEmpty(rawPerson.AddressPrevious)) quizzes.Add(new Quiz("Where did you live before you moved to " + rawPerson.Address + " ?", rawPerson.AddressPrevious));
            if (!String.IsNullOrEmpty(rawPerson.TelephoneNumber)) quizzes.Add(new Quiz("What is your telephone number?", rawPerson.TelephoneNumber));
            if (!String.IsNullOrEmpty(rawPerson.Workplace)) quizzes.Add(new Quiz("Where do you work?", rawPerson.Workplace));
            if (!String.IsNullOrEmpty(rawPerson.City)) quizzes.Add(new Quiz("In what city do you live?", rawPerson.City));
            if (!String.IsNullOrEmpty(rawPerson.DriverID)) quizzes.Add(new Quiz("What is your driver ID number", rawPerson.DriverID));
            if (!String.IsNullOrEmpty(rawPerson.PassportNumber)) quizzes.Add(new Quiz("What is your passport number", rawPerson.PassportNumber));

            //We will not ask questions about a persons parents if they are dead.
            if (!rawPerson.FatherDead)
            {
                if (rawPerson.FatherAge != null && rawPerson.FatherAge == 0) quizzes.Add(new Quiz("What is your fathers age?", rawPerson.FatherAge.ToString()));
                if (!String.IsNullOrEmpty(rawPerson.FatherBirthday)) quizzes.Add(new Quiz("When were your father born?", rawPerson.FatherBirthday));
                if (!String.IsNullOrEmpty(rawPerson.FatherEducation)) quizzes.Add(new Quiz("What is your fathers education", rawPerson.FatherEducation));
                if (!String.IsNullOrEmpty(rawPerson.FatherName)) quizzes.Add(new Quiz("What is your fathers name?", rawPerson.FatherName));
            }

            if (!rawPerson.MotherDead)
            {
                if (rawPerson.MotherAge != null && rawPerson.MotherAge == 0) quizzes.Add(new Quiz("What is your mothers age?", rawPerson.MotherAge.ToString()));
                if (!String.IsNullOrEmpty(rawPerson.MotherBirthday)) quizzes.Add(new Quiz("When were your mother born?", rawPerson.MotherBirthday));
                if (!String.IsNullOrEmpty(rawPerson.MotherEducation)) quizzes.Add(new Quiz("What is your mothers education", rawPerson.MotherEducation));
                if (!String.IsNullOrEmpty(rawPerson.MotherName)) quizzes.Add(new Quiz("What is your mothers name?", rawPerson.MotherName));
            }

            return quizzes;
        }
    }
}
