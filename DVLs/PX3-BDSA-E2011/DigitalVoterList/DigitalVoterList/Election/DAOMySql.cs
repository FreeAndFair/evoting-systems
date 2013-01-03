/*
 * Authors: Jens, Michael
 * Team: PX3
 * Date: 12-12-2011
 */

using System.Data;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using DigitalVoterList.Utilities;
using MySql.Data.MySqlClient;

namespace DigitalVoterList.Election
{
    using System;
    using System.Collections.Generic;
    using System.Text;

    using DigitalVoterList.Election.Administration;

    public class DAOMySql : IDataAccessObject
    {
        #region Constructor and factory
        private DAOMySql(string connectionString)
        {
            _connectionString = connectionString;
        }

        public static IDataAccessObject GetDAO(User u, string connectionString)
        {
            return new DAOPermissionProxy(u, new DAOMySql(connectionString));
        }
        #endregion

        #region Implementation of IDataAccessObject

        [Pure]
        public Citizen LoadCitizen(int id)
        {
            return (Citizen)LoadWithTransaction(() => PriLoadCitizen(id));
        }

        [Pure]
        private Citizen PriLoadCitizen(int id)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(PriExistsWithId("person", id), "Person must exist in the database to be loaded.");
            Contract.Requires(HasValidCpr(id), "A citizen must have a valid CPR number");
            Contract.Ensures(Contract.Result<Citizen>() != null);
            MySqlCommand command = Prepare("SELECT " +
                                           "    *, v.name venue_name, v.address venue_address " +
                                           "FROM " +
                                           "    person p " +
                                           "    LEFT JOIN " +
                                           "        voting_venue v " +
                                           "    ON " +
                                           "        v.id=p.voting_venue_id " +
                                           "WHERE " +
                                           "    p.id=@id");
            command.Parameters.AddWithValue("@id", id);
            Citizen c = null;
            Query(command, rdr =>
            {
                rdr.Read();
                c = new Citizen(id, rdr.GetString("cpr"), rdr.GetInt32("has_voted") != 0);
                c.EligibleToVote = rdr.GetInt16("eligible_to_vote") == 1;
                DoIfNotDbNull(rdr, "voting_venue_id", label =>
                {
                    c.VotingPlace = new VotingVenue(
                        rdr.GetInt32(label),
                        rdr.GetString("venue_name"),
                        rdr.GetString("venue_address"));
                });
                DoIfNotDbNull(rdr, "name", lbl => { c.Name = rdr.GetString(lbl); });
                DoIfNotDbNull(rdr, "address", lbl => { c.Address = rdr.GetString(lbl); });
                DoIfNotDbNull(rdr, "place_of_birth", lbl => { c.PlaceOfBirth = rdr.GetString(lbl); });
                DoIfNotDbNull(rdr, "passport_number", lbl => { c.PassportNumber = rdr.GetString(lbl); });
            });
            MySqlCommand findQuestions = Prepare("SELECT * FROM quiz WHERE person_id=@id");
            findQuestions.Parameters.AddWithValue("@id", id);
            Query(findQuestions, rdr =>
            {
                while (rdr.Read())
                {
                    Quiz q = new Quiz(rdr.GetString("question"), rdr.GetString("answer"));
                    c.SecurityQuestions.Add(q);
                }
            });
            return c;
        }

        /// <summary>
        /// Does this id exist in this database table?
        /// </summary>
        /// <param name="o"></param>
        /// <returns></returns>
        [Pure]
        public bool ExistsInDb(object o)
        {
            if (o is Citizen)
            {
                return (bool)LoadWithTransaction(() => PriExistsWithId("person", ((Citizen)o).DbId));
            }
            else if (o is User)
            {
                return (bool)LoadWithTransaction(() => PriExistsWithId("user", ((User)o).DbId));
            }
            else if (o is VoterCard)
            {
                return (bool)LoadWithTransaction(() => PriExistsWithId("voter_card", ((VoterCard)o).Id));
            }
            else if (o is VotingVenue)
            {
                return (bool)LoadWithTransaction(() => PriExistsWithId("voting_venue", ((VotingVenue)o).DbId));
            }
            else
            {
                throw new Exception("Input type is not supported by the ExistsWithId function");
            }
        }

        [Pure]
        private bool PriExistsWithId(string tableName, int id)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(tableName != null);
            Contract.Requires(id > 0, "No ids are smaller than 1!");
            MySqlCommand cmd = Prepare("SELECT COUNT(*) FROM " + tableName + " WHERE id=@id;");
            cmd.Parameters.AddWithValue("@id", id);
            object found = ScalarQuery(cmd);
            return found != null;
        }

        [Pure]
        private bool HasValidCpr(int citizenId)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(citizenId > 0, "A valid database id must be greater than zero.");
            MySqlCommand cmd = Prepare("SELECT cpr FROM person WHERE id=@id;");
            cmd.Parameters.AddWithValue("@id", citizenId);
            object result = ScalarQuery(cmd);
            string cpr = (string)(result ?? "");
            return Citizen.ValidCpr(cpr);
        }

        /// <summary>
        /// What user has this username?
        /// </summary>
        /// <param name="username">The username to search for</param>
        /// <returns>A user object, null if no user could be found</returns>
        [Pure]
        public User LoadUser(string username)
        {
            User user = null;
            DoTransaction(() => { user = PriLoadUser(username); });
            return user;
        }

        [Pure]
        private User PriLoadUser(string username)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(username != null, "Input username must not be null!");
            MySqlCommand cmd = Prepare("SELECT id FROM user WHERE user_name=@username");
            cmd.Parameters.AddWithValue("@username", username);
            object maybeId = ScalarQuery(cmd);
            if (maybeId == null) return null;
            int id = Convert.ToInt32(maybeId);
            return PriLoadUser(id);
        }

        /// <summary>
        /// What user has this id?
        /// </summary>
        /// <param name="id">The database id of the user to load</param>
        /// <returns>An unauthenticated user obejct.</returns>
        [Pure]
        public User LoadUser(int id)
        {
            Contract.Requires(id > 0, "The input id must be larger than zero.");
            Contract.Requires(ExistsInDb(new User(id, "")));
            return (User)LoadWithTransaction(() => PriLoadUser(id));
        }

        [Pure]
        private User PriLoadUser(int id)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(PriExistsWithId("user", id), "User must exist in the database to be loaded.");
            Contract.Requires(id > 0, "The input id must be larger than zero.");
            Contract.Ensures(Contract.Result<User>() != null);
            MySqlCommand cmd = Prepare("SELECT * FROM " +
                                       "    user u " +
                                       "    INNER JOIN " +
                                       "        person p " +
                                       "    ON " +
                                       "        u.person_id=p.id " +
                                       "WHERE " +
                                       "    u.id=@id");
            cmd.Parameters.AddWithValue("@id", id);
            User u = null;
            Query(cmd, rdr =>
                           {
                               rdr.Read();
                               string cpr = null;
                               DoIfNotDbNull(rdr, "cpr", lbl => { cpr = rdr.GetString(lbl); });
                               u = new User(id, cpr);
                               DoIfNotDbNull(rdr, "name", lbl => { u.Name = rdr.GetString(lbl); });
                               DoIfNotDbNull(rdr, "address", lbl => { u.Address = rdr.GetString(lbl); });
                               DoIfNotDbNull(rdr, "place_of_birth", lbl => { u.PlaceOfBirth = rdr.GetString(lbl); });
                               DoIfNotDbNull(rdr, "passport_number", lbl => { u.PassportNumber = rdr.GetString(lbl); });
                               u.Username = rdr.GetString("user_name");
                               u.Title = rdr.GetString("title");
                               u.UserSalt = rdr.GetString("user_salt");
                           });
            return u;
        }

        /// <summary>
        /// Is this username and hashed password combination valid?
        /// </summary>
        /// <param name="username">The username to validate</param>
        /// <param name="passwordHash">The passwordHash to validate with</param>
        /// <returns>The id of a validated user. 0 if no user can be found.</returns>
        [Pure]
        public bool ValidateUser(string username, string passwordHash)
        {
            Contract.Requires(username != null, "The username must not be null!");
            Contract.Requires(passwordHash != null, "The password hash must not be null!");
            object result = LoadWithTransaction(() => PriValidateUser(username, passwordHash));
            return (bool)result;
        }

        [Pure]
        private bool PriValidateUser(string username, string passwordHash)
        {
            Contract.Requires(Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(username != null, "The username must not be null!");
            Contract.Requires(passwordHash != null, "The password hash must not be null!");
            MySqlCommand cmd = Prepare("SELECT COUNT(*) FROM " +
                                       "    user " +
                                       "WHERE " +
                                       "    user_name=@username " +
                                       "    AND " +
                                       "    password_hash=@passwordHash");
            cmd.Parameters.AddWithValue("@username", username);
            cmd.Parameters.AddWithValue("@passwordHash", passwordHash);
            int output = Convert.ToInt32(ScalarQuery(cmd));
            return output == 1;
        }

        /// <summary>
        /// What permissions does this user have?
        /// </summary>
        /// <param name="u">The user to to look for permissions for</param>
        /// <returns>Permissions for the user</returns>
        [Pure]
        public HashSet<SystemAction> GetPermissions(User u)
        {
            Contract.Requires(u != null, "Input user must not be null!");
            Contract.Ensures(Contract.Result<HashSet<SystemAction>>() != null);
            var result = new HashSet<SystemAction>();
            DoTransaction(() => { result = PriGetPermissions(u); });
            return result;
        }

        [Pure]
        private HashSet<SystemAction> PriGetPermissions(User user)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(user != null, "The input user must not be null!");
            Contract.Ensures(Contract.Result<HashSet<SystemAction>>() != null);
            var output = new HashSet<SystemAction>();
            if (user.DbId < 1) return output; //The user CAN not exist in the database...
            MySqlCommand cmd =
                Prepare("SELECT a.label FROM " +
                        "   action a " +
                        "   INNER JOIN " +
                        "       permission p " +
                        "       ON " +
                        "       a.id = p.action_id " +
                        "WHERE " +
                        "   p.user_id=@id");
            cmd.Parameters.AddWithValue("@id", user.DbId);
            Query(cmd, rdr =>
                           {
                               while (rdr.Read())
                               {
                                   SystemAction action = SystemActions.getSystemAction(rdr.GetString(0));
                                   output.Add(action);
                               }
                           });
            return output;
        }

        /// <summary>
        /// Where does this user work?
        /// </summary>
        /// <param name="u">The user to get workplaces for</param>
        /// <returns>The voting venues where the user works</returns>
        [Pure]
        public HashSet<VotingVenue> GetWorkplaces(User u)
        {
            Contract.Requires(u != null, "Input user must not be null!");
            Contract.Ensures(Contract.Result<HashSet<VotingVenue>>() != null);
            var result = new HashSet<VotingVenue>();
            DoTransaction(() => { result = PriGetWorkplaces(u); });
            return result;
        }

        [Pure]
        private HashSet<VotingVenue> PriGetWorkplaces(User user)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(user != null, "The input user must not be null!");
            Contract.Ensures(Contract.Result<HashSet<VotingVenue>>() != null);
            var output = new HashSet<VotingVenue>();
            if (user.DbId < 1) return output; //The user CAN not exist in the database...
            MySqlCommand cmd =
                Prepare("SELECT " +
                        "   v.id, " +
                        "   v.address, " +
                        "   v.name " +
                        "FROM " +
                        "   user u " +
                        "   INNER JOIN " +
                        "       workplace w " +
                        "       ON " +
                        "       u.id = w.user_id " +
                        "   INNER JOIN " +
                        "       voting_venue v " +
                        "       ON " +
                        "       v.id = w.voting_venue_id " +
                        "WHERE " +
                        "   u.id=@id");
            cmd.Parameters.AddWithValue("@id", user.DbId);
            Query(cmd, rdr =>
            {
                while (rdr.Read())
                {
                    VotingVenue venue = new VotingVenue(
                        rdr.GetInt32("id"),
                        rdr.GetString("name"),
                        rdr.GetString("address"));
                    output.Add(venue);
                }
            });
            return output;
        }

        /// <summary>
        /// What voter card has this id?
        /// </summary>
        /// <param name="id">The database id of the voter card to load</param>
        /// <returns>A voter card</returns>
        [Pure]
        public VoterCard LoadVoterCard(int id)
        {
            return (VoterCard)LoadWithTransaction(() => PriLoadVoterCard(id));
        }

        [Pure]
        private VoterCard PriLoadVoterCard(int id)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(PriExistsWithId("voter_card", id), "Votercard must exist in the database to be loaded.");
            Contract.Ensures(Contract.Result<VoterCard>() != null);
            MySqlCommand command = Prepare("SELECT * FROM voter_card v LEFT JOIN person p ON p.id=v.person_id WHERE v.id=@id");
            command.Parameters.AddWithValue("@id", id);
            VoterCard v = new VoterCard();
            int citizenId = 0;
            Query(command, (MySqlDataReader rdr) =>
            {
                rdr.Read();
                citizenId = rdr.GetInt32("person_id");
                v.ElectionEvent = Settings.Election;
                v.Id = rdr.GetInt32("id");
                v.IdKey = rdr.GetString("id_key");
                v.Valid = (rdr.GetUInt32("valid") == 1);
            });
            v.Citizen = PriLoadCitizen(citizenId);
            return v;
        }

        /// <summary>
        /// What voter card has this id-key?
        /// </summary>
        /// <param name="idKey">The id-key to search for</param>
        /// <returns>A voter card</returns>
        [Pure]
        public VoterCard LoadVoterCard(string idKey)
        {
            List<VoterCard> result =
                FindVoterCards(new Dictionary<VoterCardSearchParam, object>() { { VoterCardSearchParam.IdKey, idKey } },
                               SearchMatching.Exact);
            return result.Count > 0 ? result[0] : null;
        }

        /// <summary>
        /// What citizens have data similiar to or exactly equal to this?
        /// </summary>
        /// <param name="data"></param>
        /// <param name="matching"></param>
        /// <returns></returns>
        [Pure]
        public List<Citizen> FindCitizens(Dictionary<CitizenSearchParam, object> data, SearchMatching matching = SearchMatching.Similair)
        {
            Contract.Requires(data != null);
            Contract.Ensures(Contract.Result<List<Citizen>>() != null);
            return (List<Citizen>)LoadWithTransaction(() => PriFindCitizens(data, matching));
        }

        [Pure]
        private List<Citizen> PriFindCitizens(Dictionary<CitizenSearchParam, object> searchData, SearchMatching matching)
        {
            Contract.Requires(Transacting(), "Must be within transaction");
            Contract.Requires(searchData != null);
            Contract.Ensures(Contract.Result<List<Citizen>>() != null);
            var searchParams = new Dictionary<string, string>()
								   {
									   {"address",null},
									   {"cpr",null},
									   {"eligible_to_vote",null},
									   {"has_voted",null},
									   {"voting_venue_id",null},
									   {"name",null}
								   };
            foreach (var kv in searchData)
            {
                switch (kv.Key)
                {
                    case CitizenSearchParam.Address:
                        searchParams["address"] = kv.Value.ToString();
                        break;
                    case CitizenSearchParam.Cpr:
                        searchParams["cpr"] = kv.Value.ToString();
                        break;
                    case CitizenSearchParam.EligibleToVote:
                        Debug.Assert(kv.Value is bool, "Eligible to vote should be a boolean value");
                        searchParams["eligible_to_vote"] = (bool)kv.Value ? "1" : "0";
                        break;
                    case CitizenSearchParam.HasVoted:
                        Debug.Assert(kv.Value is bool, "Has voted should be a boolean value");
                        searchParams["has_voted"] = (bool)kv.Value ? "1" : "0";
                        break;
                    case CitizenSearchParam.Name:
                        searchParams["name"] = kv.Value.ToString();
                        break;
                    case CitizenSearchParam.VotingPlace:
                        Debug.Assert(kv.Value is VotingVenue);
                        searchParams["voting_venue_id"] = ((VotingVenue)kv.Value).DbId.ToString();
                        break;
                }
            }
            MySqlCommand findCitizens = PrepareSearchQuery("person", searchParams, matching);
            List<int> resultIds = new List<int>();
            Query(findCitizens, (rdr) =>
                                   {
                                       while (rdr.Read())
                                       {
                                           string cpr = "";
                                           DoIfNotDbNull(rdr, "cpr", lbl => { cpr = rdr.GetString(lbl); });
                                           if (Citizen.ValidCpr(cpr))
                                           {
                                               resultIds.Add(rdr.GetInt32("id"));
                                           }
                                       }
                                   });
            List<Citizen> result = new List<Citizen>();
            foreach (int id in resultIds)
            {
                result.Add(PriLoadCitizen(id));
            }
            return result;
        }

        /// <summary>
        /// What users have data similiar to or exactly equal to this?
        /// </summary>
        /// <param name="data"></param>
        /// <param name="matching"></param>
        /// <returns></returns>
        [Pure]
        public List<User> FindUsers(Dictionary<UserSearchParam, object> data, SearchMatching matching = SearchMatching.Similair)
        {
            Contract.Requires(data != null);
            Contract.Ensures(Contract.Result<List<Citizen>>() != null);
            return (List<User>)LoadWithTransaction(() => PriFindUsers(data, matching));
        }

        private List<User> PriFindUsers(Dictionary<UserSearchParam, object> data, SearchMatching matching)
        {
            //WAIT
            throw new NotImplementedException();
        }

        /// <summary>
        /// What votercards have data similiar to or exactly equal to this?
        /// </summary>
        /// <param name="data"></param>
        /// <param name="matching"></param>
        /// <returns></returns>
        [Pure]
        public List<VoterCard> FindVoterCards(Dictionary<VoterCardSearchParam, object> data, SearchMatching matching = SearchMatching.Similair)
        {
            Contract.Requires(data != null);
            Contract.Ensures(Contract.Result<List<VoterCard>>() != null);
            return (List<VoterCard>)LoadWithTransaction(() => PriFindVoterCards(data, matching));
        }

        private List<VoterCard> PriFindVoterCards(Dictionary<VoterCardSearchParam, object> searchData, SearchMatching matching)
        {
            Contract.Requires(Transacting(), "Must be in transaction");
            Contract.Requires(searchData != null);
            Contract.Ensures(Contract.Result<List<VoterCard>>() != null);
            var searchParams = new Dictionary<string, string>()
								   {
									   {"person_id",null},
									   {"valid",null},
									   {"id_key",null}
								   };
            foreach (var kv in searchData)
            {
                switch (kv.Key)
                {
                    case VoterCardSearchParam.CitizenId:
                        searchParams["person_id"] = kv.Value.ToString();
                        break;
                    case VoterCardSearchParam.Valid:
                        Debug.Assert(kv.Value is bool, "Valid should be a boolean value");
                        searchParams["valid"] = (bool)kv.Value ? "1" : "0";
                        break;
                    case VoterCardSearchParam.IdKey:
                        searchParams["id_key"] = kv.Value.ToString();
                        break;
                }
            }
            MySqlCommand findVoterCards = PrepareSearchQuery("voter_card", searchParams, matching);
            List<int> resultIds = new List<int>();
            Query(findVoterCards, (rdr) =>
            {
                while (rdr.Read())
                {
                    resultIds.Add(rdr.GetInt32("id"));
                }
            });
            var result = new List<VoterCard>();
            foreach (int id in resultIds)
            {
                result.Add(PriLoadVoterCard(id));
            }
            return result;
        }

        private void PriSave(Citizen citizen)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(citizen != null, "Input citizen must not be null!");
            Contract.Requires(citizen.DbId > 0, "DbId must be larger than zero to update");
            Contract.Requires(PriExistsWithId("person", citizen.DbId), "DbId must be present in database in order to update anything");
            Contract.Requires(citizen.Cpr != null && Citizen.ValidCpr(citizen.Cpr), "A citizen must be saved with a valid CPR number");
            Contract.Requires(citizen.VotingPlace == null || PriExistsWithId("voting_venue", citizen.VotingPlace.DbId), "If Citizen has a VotingPlace, it must exist in the database prior to saving.");
            Contract.Ensures(PriLoadCitizen(citizen.DbId).Equals(citizen), "All changes must be saved");
            MySqlCommand cmd = Prepare("UPDATE " +
                                       "    person " +
                                       "SET " +
                                       "    name=@name, " +
                                       "    address=@address, " +
                                       "    cpr=@cpr, " +
                                       "    eligible_to_vote=@eligibleToVote, " +
                                       "    place_of_birth=@placeOfBirth, " +
                                       "    passport_number=@passportNumber, " +
                                       "    voting_venue_id=@votingVenueId " +
                                       "WHERE " +
                                       "    id=@id");
            var mapping = new Dictionary<string, string>()
							  {
								  {"id",citizen.DbId.ToString()},
								  {"name",citizen.Name},
								  {"address",citizen.Address},
								  {"cpr",citizen.Cpr},
								  {"eligibleToVote",citizen.EligibleToVote ? "1" : "0"},
								  {"placeOfBirth",citizen.PlaceOfBirth},
								  {"passportNumber",citizen.PassportNumber},
								  {"votingVenueId",citizen.VotingPlace!=null? citizen.VotingPlace.DbId.ToString() : null} //Avoid null-pointer
							  };

            foreach (var kv in mapping)
            {
                cmd.Parameters.AddWithValue("@" + kv.Key, kv.Value);
            }

            Execute(cmd);

            PriSaveQuestions(citizen.DbId, citizen.SecurityQuestions);
        }

        private void PriSaveNew(Citizen citizen)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(citizen != null, "Input citizen must not be null!");
            Contract.Requires(citizen.DbId == 0, "DbId must be equal to zero");
            Contract.Requires(citizen.Cpr != null && Citizen.ValidCpr(citizen.Cpr), "A citizen must be saved with a valid CPR number");
            Contract.Requires(citizen.VotingPlace == null || PriExistsWithId("voting_venue", citizen.VotingPlace.DbId), "If Citizen has a VotingPlace, it must exist in the database prior to saving.");
            Contract.Ensures(PriLoadCitizen(citizen.DbId).Equals(citizen), "All changes must be saved");
            MySqlCommand cmd = Prepare("INSERT INTO person (name,address,cpr,eligible_to_vote,place_of_birth,passport_number,voting_venue_id) VALUES (@name, @address, @cpr, @eligibleToVote, @placeOfBirth, @passportNumber, @votingVenueId); SELECT LAST_INSERT_ID();");
            var mapping = new Dictionary<string, string>()
							  {
								  {"name",citizen.Name},
								  {"address",citizen.Address},
								  {"cpr",citizen.Cpr},
								  {"eligibleToVote",citizen.EligibleToVote ? "1" : "0"},
								  {"placeOfBirth",citizen.PlaceOfBirth},
								  {"passportNumber",citizen.PassportNumber},
								  {"votingVenueId",citizen.VotingPlace != null ? citizen.VotingPlace.DbId.ToString() : null} //Avoid null-pointer
							  };
            foreach (var kv in mapping)
            {
                cmd.Parameters.AddWithValue("@" + kv.Key, kv.Value);
            }

            object output = ScalarQuery(cmd);
            citizen.DbId = Convert.ToInt32(output);

            PriSaveQuestions(citizen.DbId, citizen.SecurityQuestions);
        }

        private void PriSaveQuestions(int id, HashSet<Quiz> quizzes)
        {
            Contract.Requires(Transacting(), "Must be done in a transaction");
            Contract.Requires(PriExistsWithId("person", id));
            MySqlCommand deleteQuestions = Prepare("DELETE FROM quiz WHERE person_id=@id");
            deleteQuestions.Parameters.AddWithValue("@id", id);
            Execute(deleteQuestions);
            if (quizzes.Count > 0)
            {
                StringBuilder insertQuery = new StringBuilder("INSERT INTO quiz (person_id, question, answer) VALUES ");
                var first = true;
                foreach (var quiz in quizzes)
                {
                    if (!first) insertQuery.Append(",");
                    insertQuery.Append("(");
                    insertQuery.Append(id);
                    insertQuery.Append(",'");
                    insertQuery.Append(quiz.Question);
                    insertQuery.Append("','");
                    insertQuery.Append(quiz.Answer);
                    insertQuery.Append("')");
                    first = false;
                }
                insertQuery.Append(";");
                MySqlCommand insertQuestions = Prepare(insertQuery.ToString());
                Execute(insertQuestions);
            }
        }

        /// <summary>
        /// Save this user with this data!
        /// </summary>
        /// <param name="user">The user to register</param>
        /// <returns>Was the attempt successful?</returns>
        public void Save(User user)
        {
            Contract.Requires(user != null, "Input person must not be null!");
            Contract.Requires(user.DbId >= 0, "DbId must be greater than or equal to zero");
            Contract.Requires(!(user.DbId > 0) || user.PersonDbId > 0, "When updating a user, PersonDbId must be greater than zero.");
            Contract.Requires(user.Cpr == null || Citizen.ValidCpr(user.Cpr), "A user must have a valid CPR number or no CPR number");
            Contract.Requires(!(user.DbId > 0) || this.ExistsInDb(user), "DbId > 0 => UserExists. Eg. if updating, the user to update must exist.");
            Contract.Requires(!(user.DbId > 0) || ExistsInDb(new Person(user.PersonDbId)), "DbId > 0 => userPersonExists. Eg. if updating, the users person to update must exist.");
            Contract.Requires(user.Username != null);
            Contract.Requires(user.Title != null);
            Contract.Requires(user.UserSalt != null);
            if (user.DbId > 0)
            {
                DoTransaction(() => PriSave(user));
            }
            else
            {
                DoTransaction(() => PriSaveNew(user));
            }
        }

        private int PriSaveNew(User user)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(user != null, "Input user must not be null!");
            Contract.Requires(user.DbId == 0, "DbId must be zero when creating");
            Contract.Requires(user.Username != null);
            Contract.Requires(user.Title != null);
            Contract.Requires(user.UserSalt != null);
            Contract.Requires(user.Cpr == null || Citizen.ValidCpr(user.Cpr), "A user must have a valid CPR number or no CPR number");
            Contract.Ensures(LoadUser(Contract.Result<int>()).Equals(user), "All changes must be saved");
            int personId;
            MySqlCommand insertOrUpdatePerson;
            if (user.Cpr != null && PriFindCitizens(new Dictionary<CitizenSearchParam, object>() { }, SearchMatching.Exact).Count > 0)
            {
                insertOrUpdatePerson =
                    Prepare("UPDATE " +
                            "   person " +
                            "SET " +
                            "   name=@name, " +
                            "   address=@address, " +
                            "   place_of_birth=@placeOfBirth, " +
                            "   passport_number=@passportNumber " +
                            "WHERE " +
                            "   cpr=@cpr" +
                            "; " +
                            "" +
                            "SELECT " +
                            "   id " +
                            "FROM " +
                            "   person " +
                            "WHERE " +
                            "   cpr=@cpr;");
            }
            else
            {
                insertOrUpdatePerson = Prepare("INSERT INTO " +
                                               "    person (" +
                                               "        name, " +
                                               "        address, " +
                                               "        place_of_birth," +
                                               "        passport_number," +
                                               "        cpr" +
                                               "    )" +
                                               "VALUES" +
                                               "    (" +
                                               "        @name," +
                                               "        @address," +
                                               "        @placeOfBirth," +
                                               "        @passportNumber," +
                                               "        @cpr" +
                                               "    )" +
                                               ";" +
                                               "" +
                                               "SELECT LAST_INSERT_ID();");
            }
            var personMapping = new Dictionary<string, string>()
									{
										{"name",user.Name},
										{"address",user.Address},
										{"placeOfBrith",user.PlaceOfBirth},
										{"passportNumber",user.PassportNumber},
										{"id",user.PersonDbId.ToString()}
									};
            foreach (var kv in personMapping)
            {
                insertOrUpdatePerson.Parameters.AddWithValue("@" + kv.Key, kv.Value);
            }
            personId = Convert.ToInt32(ScalarQuery(insertOrUpdatePerson));

            MySqlCommand insertUser = Prepare(" INSERT INTO" +
                                              "     user (" +
                                              "         user_name," +
                                              "         title," +
                                              "         person_id," +
                                              "         user_salt" +
                                              "     )" +
                                              "VALUES" +
                                              "     (" +
                                              "         @username," +
                                              "         @title," +
                                              "         @personId," +
                                              "         @userSalt" +
                                              "     )" +
                                              ";" +
                                              "" +
                                              "SELECT LAST_INSERT_ID();");
            var userMapping = new Dictionary<string, string>()
			{
				{"username",user.Username},
				{"title",user.Title},
				{"personId",personId.ToString()},
				{"userSalt",user.UserSalt}
			};
            foreach (var kv in userMapping)
            {
                insertUser.Parameters.AddWithValue("@" + kv.Key, kv.Value);
            }
            return Convert.ToInt32(ScalarQuery(insertUser));
        }


        private void PriSave(User user)
        {
            Contract.Requires(this.Transacting(), "This method must be performed in a transaction.");
            Contract.Requires(user != null, "Input user must not be null!");
            Contract.Requires(user.DbId > 0, "DbId must be larger than zero to update");
            Contract.Requires(PriExistsWithId("user", user.DbId), "DbId must be present in database in order to update anything");
            Contract.Requires(user.Username != null);
            Contract.Requires(user.Title != null);
            Contract.Requires(user.UserSalt != null);
            Contract.Requires(user.PersonDbId > 0, "An existing user must map to a person in the database");
            Contract.Requires(PriExistsWithId("person", user.PersonDbId), "The person for this user must exist in the database");
            Contract.Requires(user.Cpr == null || Citizen.ValidCpr(user.Cpr), "A user must have a valid CPR number or no CPR number");
            Contract.Ensures(LoadUser(user.DbId).Equals(user), "All changes must be saved");

            MySqlCommand updatePerson = Prepare("UPDATE person SET name=@name, address=@address, place_of_birth=@placeOfBirth, passport_number=@passportNumber WHERE id=@id");
            var personMapping = new Dictionary<string, string>()
									{
										{"name",user.Name},
										{"address",user.Address},
										{"placeOfBrith",user.PlaceOfBirth},
										{"passportNumber",user.PassportNumber},
										{"id",user.PersonDbId.ToString()}
									};
            foreach (var kv in personMapping)
            {
                updatePerson.Parameters.AddWithValue("@" + kv.Key, kv.Value);
            }
            Execute(updatePerson);

            MySqlCommand updateUser = Prepare("UPDATE user SET user_name=@username, title=@title, user_salt=@userSalt WHERE id=@id");
            var userMapping = new Dictionary<string, string>()
							  {
								  {"username",user.Username},
								  {"title",user.Title},
								  {"userSalt",user.UserSalt},
								  {"id",user.DbId.ToString()}
							  };
            foreach (var kv in userMapping)
            {
                updateUser.Parameters.AddWithValue("@" + kv.Key, kv.Value);
            }
            Execute(updateUser);
        }

        private int PriSaveNew(VoterCard voterCard)
        {
            Contract.Requires(this.Transacting(), "Must be called within a transaction");
            Contract.Requires(voterCard != null);
            Contract.Requires(voterCard.Id == 0);
            Contract.Requires(voterCard.Citizen != null);
            Contract.Requires(PriExistsWithId("person", voterCard.Citizen.DbId), "A voter card must belong to a person in the database");
            Contract.Requires(voterCard.IdKey != null);
            /*Contract.Requires(FindVoterCards(new Dictionary<VoterCardSearchParam, object>()
                                                                        {
                                                                            {VoterCardSearchParam.IdKey,voterCard.IdKey}
                                                                        }).Count == 0, "Voter card id-key must be unique!");*/
            Contract.Requires(!(voterCard.Id > 0) || PriExistsWithId("voter_card", voterCard.Id));
            MySqlCommand saveVoterCard = Prepare("INSERT INTO " +
                                                 "  voter_card (" +
                                                 "      person_id, " +
                                                 "      valid, " +
                                                 "      id_key" +
                                                 "  )" +
                                                 "VALUES" +
                                                 "  (" +
                                                 "      @personId," +
                                                 "      @valid," +
                                                 "      @idKey" +
                                                 "  )" +
                                                 ";" +
                                                 "" +
                                                 "SELECT LAST_INSERT_ID();");
            var voterCardMapping = new Dictionary<string, string>()
															 {
																 {"personId",voterCard.Citizen.DbId.ToString()},
																 {"valid",voterCard.Valid ? "1" : "0"},
																 {"idKey",voterCard.IdKey}
															 };
            foreach (var kv in voterCardMapping)
            {
                saveVoterCard.Parameters.AddWithValue("@" + kv.Key, kv.Value);
            }
            return Convert.ToInt32(ScalarQuery(saveVoterCard));
        }

        private void PriSave(VoterCard voterCard)
        {
            Contract.Requires(this.Transacting(), "Must be called within a transaction");
            Contract.Requires(voterCard != null);
            Contract.Requires(voterCard.Id > 0);
            Contract.Requires(voterCard.Citizen != null);
            Contract.Requires(PriExistsWithId("person", voterCard.Citizen.DbId), "A voter card must belong to a person in the database");
            Contract.Requires(voterCard.IdKey != null);
            Contract.Requires(PriExistsWithId("voter_card", voterCard.Id));
            MySqlCommand updateVoterCard = Prepare("UPDATE" +
                                                   "    voter_card  " +
                                                   "SET" +
                                                   "    person_id=@personId," +
                                                   "    valid=@valid," +
                                                   "    id_key=@idKey;");
            var voterCardMapping = new Dictionary<string, string>()
													{
														{"personId",voterCard.Citizen.DbId.ToString()},
														{"valid",voterCard.Valid ? "1" : "0"},
														{"idKey",voterCard.IdKey}
													};
            foreach (var kv in voterCardMapping)
            {
                updateVoterCard.Parameters.AddWithValue("@" + kv.Key, kv.Value);
            }
            Execute(updateVoterCard);
        }

        /// <summary>
        /// Mark that a voter has voted with standard validation!
        /// </summary>
        /// <param name="citizen">The citizen who should be marked as voted</param>
        /// <param name="cprKey">The last four digits of the citizen's CPR-Number</param>
        /// <returns>Was the attempt successful?</returns>
        public void SetHasVoted(Citizen citizen, string cprKey)
        {
            Contract.Requires(citizen != null);
            Contract.Requires(cprKey != null);
            Contract.Requires(ExistsInDb(citizen));
            Contract.Requires(LoadCitizen(citizen.DbId).EligibleToVote == true);
            Contract.Requires(LoadCitizen(citizen.DbId).HasVoted == false);
            Contract.Requires(LoadCitizen(citizen.DbId).Cpr.Substring(6, 4).Equals(cprKey));
            DoTransaction(() => PriSetHasVoted(citizen));
        }

        /// <summary>
        /// Mark that a voter has voted with manual validation!
        /// </summary>
        /// <param name="citizen">The citizen who should be marked as voted</param>
        /// <returns>Was the attempt successful?</returns>
        public void SetHasVoted(Citizen citizen)
        {
            Contract.Requires(citizen != null);
            Contract.Requires(ExistsInDb(citizen));
            Contract.Requires(LoadCitizen(citizen.DbId).EligibleToVote == true);
            Contract.Requires(LoadCitizen(citizen.DbId).HasVoted == false);
            DoTransaction(() => PriSetHasVoted(citizen));
        }

        private void PriSetHasVoted(Citizen c)
        {
            Contract.Requires(_transaction != null, "This must be in a transaction");
            Contract.Requires(c != null, "Input citizen should not be null");
            Contract.Requires(PriExistsWithId("person", c.DbId), "Input citizen should be in the database");
            Contract.Requires(PriLoadCitizen(c.DbId).EligibleToVote == true, "Input citizen should be eligible to vote");
            Contract.Requires(PriLoadCitizen(c.DbId).HasVoted == false, "Input citizen must not have voted");
            Contract.Ensures(PriLoadCitizen(c.DbId).HasVoted == true, "If successfull, the citizen must have voted after the method is finished");
            MySqlCommand setHasVoted = Prepare("UPDATE person SET has_voted=1 WHERE has_voted=0 AND eligible_to_vote=1 AND id=@id; SELECT ROW_COUNT();");
            setHasVoted.Parameters.AddWithValue("@id", c.DbId);
            object result = ScalarQuery(setHasVoted);
            int affected = Convert.ToInt32(result);
            if (affected != 1)
            {
                throw new Exception("Updating that a person has voted should effect one and only one row, but was " + affected);
            }
        }


        /// <summary>
        /// Change this users pasword to this!
        /// </summary>
        /// <param name="user">The user whose password should be changed</param>
        /// <param name="newPasswordHash">The hash of the new password to use</param>
        /// <param name="oldPasswordHash">The hash of the old password for this user.</param>
        /// <returns>Was the attempt succesful?</returns>
        public void ChangePassword(User user, string newPasswordHash, string oldPasswordHash)
        {
            Contract.Requires(user != null);
            Contract.Requires(this.ExistsInDb(user));
            Contract.Requires(newPasswordHash != null);
            Contract.Requires(oldPasswordHash != null);
            Contract.Requires(ValidateUser(user.Username, oldPasswordHash));
            if (!ValidateUser(user.Username, oldPasswordHash)) throw new Exception("Wrong password for user \"" + user.Username + "\""); //Make sure that we can't change password with a wrong password..
            DoTransaction(() => PriChangePassword(user, newPasswordHash));
        }

        /// <summary>
        /// Change this users password to this!
        /// </summary>
        /// <param name="user">The user whose password should be changed</param>
        /// <param name="newPasswordHash">The hash of the new password to use</param>
        /// <returns>Was th attempt succesful?</returns>
        public void ChangePassword(User user, string newPasswordHash)
        {
            Contract.Requires(user != null);
            Contract.Requires(ExistsInDb(user));
            Contract.Requires(newPasswordHash != null);
            DoTransaction(() => PriChangePassword(user, newPasswordHash));
        }

        private void PriChangePassword(User user, string newPasswordHash)
        {
            Contract.Requires(Transacting(), "Must be done in a transaction");
            Contract.Requires(user != null);
            Contract.Requires(PriExistsWithId("user", user.DbId));
            Contract.Requires(newPasswordHash != null);
            MySqlCommand updatePassword = Prepare("UPDATE user SET password_hash=@pwdHash WHERE id=@id");
            updatePassword.Parameters.AddWithValue("@pwdHash", newPasswordHash);
            updatePassword.Parameters.AddWithValue("@id", user.DbId);
            Execute(updatePassword);
        }

        /// <summary>
        /// Update all persons in the dataset with this update
        /// </summary>
        /// <param name="updateFunc"></param>
        public void UpdatePeople(Func<Citizen, RawPerson, Citizen> updateFunc)
        {
            var connection = new MySqlConnection(this._connectionString);
            connection.Open();
            const string Query =
                "SELECT " + "p.*, " + "f.name AS fathers_name, " + "f.birthday AS fathers_birthday, "
                + "f.age AS fathers_age, " + "f.education AS fathers_education, " + "f.dead AS father_dead, "
                + "m.name AS mothers_name, " + "m.birthday AS mothers_birthday, " + "m.age AS mothers_age, "
                + "m.education AS mothers_education, " + "m.dead AS mother_dead " + "FROM raw_person_data p "
                + "LEFT JOIN raw_person_data f ON p.father_cpr = f.cpr "
                + "LEFT JOIN raw_person_data m ON p.mother_cpr = m.cpr;";
            var loadRowPeople = new MySqlCommand(Query, connection);
            MySqlDataReader rdr = null;

            try
            {
                rdr = loadRowPeople.ExecuteReader();

                while (rdr.Read())
                {
                    RawPerson rawPerson = new RawPerson();
                    DoIfNotDbNull(rdr, "address", lbl => rawPerson.Address = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "address_previous", lbl => rawPerson.AddressPrevious = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "age", lbl => rawPerson.Age = rdr.GetInt32(lbl));
                    DoIfNotDbNull(rdr, "birthday", lbl => rawPerson.Birthday = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "birthplace", lbl => rawPerson.Birthplace = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "CPR", lbl => rawPerson.CPR = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "city", lbl => rawPerson.City = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "deathdate", lbl => rawPerson.Deathdate = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "dead", lbl => rawPerson.Dead = rdr.GetBoolean(lbl));
                    DoIfNotDbNull(rdr, "disempowered", lbl => rawPerson.Disempowered = rdr.GetBoolean(lbl));
                    DoIfNotDbNull(rdr, "driver_id", lbl => rawPerson.DriverID = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "education", lbl => rawPerson.Education = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "military_served", lbl => rawPerson.MilitaryServed = rdr.GetBoolean(lbl));
                    DoIfNotDbNull(rdr, "name", lbl => rawPerson.Name = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "nationality", lbl => rawPerson.Nationality = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "passport_number", lbl => rawPerson.PassportNumber = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "telephone", lbl => rawPerson.TelephoneNumber = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "workplace", lbl => rawPerson.Workplace = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "zipcode", lbl => rawPerson.Zipcode = rdr.GetInt32(lbl));

                    DoIfNotDbNull(rdr, "fathers_name", lbl => rawPerson.FatherName = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "fathers_age", lbl => rawPerson.FatherAge = rdr.GetInt32(lbl));
                    DoIfNotDbNull(rdr, "fathers_birthday", lbl => rawPerson.FatherBirthday = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "fathers_education", lbl => rawPerson.FatherEducation = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "father_dead", lbl => rawPerson.FatherDead = rdr.GetBoolean(lbl));

                    DoIfNotDbNull(rdr, "mothers_name", lbl => rawPerson.MotherName = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "mothers_age", lbl => rawPerson.MotherAge = rdr.GetInt32(lbl));
                    DoIfNotDbNull(rdr, "mothers_birthday", lbl => rawPerson.MotherBirthday = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "mothers_education", lbl => rawPerson.MotherEducation = rdr.GetString(lbl));
                    DoIfNotDbNull(rdr, "mother_dead", lbl => rawPerson.MotherDead = rdr.GetBoolean(lbl));

                    if (rawPerson.CPR != null)
                    {

                        List<Citizen> listOfCitizens =
                            FindCitizens(
                                new Dictionary<CitizenSearchParam, object>() { { CitizenSearchParam.Cpr, rawPerson.CPR } }, SearchMatching.Exact);

                        if ((listOfCitizens.Count > 0))
                        {
                            Citizen c = updateFunc(listOfCitizens[0], rawPerson);
                            DoTransaction(() => PriSave(c));
                        }
                        else
                        {
                            Citizen c = updateFunc(new Citizen(0, rawPerson.CPR), rawPerson);
                            DoTransaction(() => PriSaveNew(c));
                        }
                    }
                }
            }
            catch (Exception)
            {
                throw;
            }
            finally
            {
                if (rdr != null) rdr.Close();
                connection.Close();
            }

            //Update people that are not in the raw data
            DoTransaction(() => this.MarkPeopleNotInRawDataUneligibleToVote());
        }

        /// <summary>
        /// Update all persons in the dataset with this update
        /// </summary>
        /// <param name="updateFunc"></param>
        public void UpdateVoterCards()
        {
            var connection = new MySqlConnection(this._connectionString);
            connection.Open();
            const string Query = "SELECT id FROM person p WHERE eligible_to_vote=1 AND p.id NOT IN (SELECT person_id FROM voter_card v WHERE v.person_id = p.id AND v.valid=1);";
            var loadEligiblePeople = new MySqlCommand(Query, connection);
            MySqlDataReader rdr = null;

            try
            {
                rdr = loadEligiblePeople.ExecuteReader();

                while (rdr.Read())
                {
                    var v = new VoterCard();
                    var id = rdr.GetInt32("id");
                    v.Citizen = LoadCitizen(id);
                    v.ElectionEvent = Settings.Election;
                    v.IdKey = VoterCard.GenerateIdKey();
                    v.Valid = true;
                    DoTransaction(() => PriSaveNew(v));
                }
            }
            catch (Exception)
            {
                throw;
            }
            finally
            {
                if (rdr != null) rdr.Close();
                connection.Close();
            }

            //Update people that are not in the raw data
            DoTransaction(
                () => this.MarkVoterCardsInvalidForCitizensUneligibleToVote()
            );
        }

        private void MarkVoterCardsInvalidForCitizensUneligibleToVote()
        {
            Contract.Requires(this.Transacting(), "This can only be done in a transaction.");
            MySqlCommand cmd = this.Prepare("UPDATE voter_card SET valid=0 WHERE person_id IN (SELECT id FROM person WHERE eligible_to_vote=0);");
            this.Execute(cmd);
        }

        private void MarkPeopleNotInRawDataUneligibleToVote()
        {
            Contract.Requires(this.Transacting(), "This can only be done in a transaction.");
            MySqlCommand cmd = this.Prepare("UPDATE person SET eligible_to_vote=0 WHERE cpr NOT IN (SELECT cpr FROM raw_person_data);");
            this.Execute(cmd);
        }

        [Pure]
        public void PrintVoterCards(VoterCardPrinter printer)
        {
            var connection = new MySqlConnection(this._connectionString);
            connection.Open();
            const string Query = "SELECT id FROM voter_card WHERE valid=1;";
            var validVotercards = new MySqlCommand(Query, connection);
            MySqlDataReader rdr = null;

            try
            {
                rdr = validVotercards.ExecuteReader();

                while (rdr.Read())
                {
                    var id = rdr.GetInt32("id");
                    var v = LoadVoterCard(id);
                    printer.Print(v);
                }
            }
            catch (Exception)
            {
                throw;
            }
            finally
            {
                if (rdr != null) rdr.Close();
                connection.Close();
            }
        }

        #endregion

        #region private SQL features
        //We keep track of all open connections, to enable later maintainance of eventual onclosed connections..
        private MySqlConnection _connection; //Current connection
        private MySqlTransaction _transaction; //Current transaction
        private readonly string _connectionString; //The string to use when connecting to the database
        private Dictionary<string, MySqlCommand> _preparedStatements = new Dictionary<string, MySqlCommand>();

        /// <summary>
        /// An open connection for the database
        /// </summary>
        private MySqlConnection Connection
        {
            get
            {
                if (_connection != null && _connection.State.Equals("Open"))
                {
                    return _connection;
                }
                else
                {
                    _preparedStatements = new Dictionary<string, MySqlCommand>();
                    try
                    {
                        RetryUtility.RetryAction(() =>
                                {
                                    _connection = new MySqlConnection(_connectionString);
                                    _connection.Open();
                                }, 5, 500);
                    }
                    catch (Exception ex)
                    {
                        throw new Exception("Could not establish connection to the central database. Please make sure you have access to the internet and try again. If the error repeats, please contact the support.", ex);
                    }
                }
                return _connection;
            }
        }

        /// <summary>
        /// Do this in a transaction, and handle all transaction and connection issues that might occur
        /// </summary>
        /// <param name="act">What to do...</param>
        /// <param name="isolationLevel">The isolation level to use</param>
        private void DoTransaction(Action act, IsolationLevel isolationLevel = IsolationLevel.Serializable)
        {
            MySqlConnection conn = Connection;
            try
            {
                RetryUtility.RetryAction(() =>
                                             {

                                                 try
                                                 {
                                                     _transaction = conn.BeginTransaction(isolationLevel);
                                                     act();
                                                     _transaction.Commit();
                                                 }
                                                 catch (Exception)
                                                 {
                                                     try
                                                     {
                                                         _transaction.Rollback();
                                                     }
                                                     catch (Exception)
                                                     {
                                                         _connection = null;
                                                         //If we can't rollback, clear the connection; something is very wrong...
                                                         //SKIPPEDTODO: Make a logging function and maybe a security alert... 
                                                     }
                                                     throw;
                                                 }
                                             }, 3, 700);
            }
            catch (Exception ex)
            {
                throw new Exception("Something unexpected went wrong. The error has been logged. Please try again.", ex);
            }
            _transaction = null;
        }

        /// <summary>
        /// Is the transaction in use
        /// </summary>
        /// <returns></returns>
        public bool Transacting()
        {
            return (_transaction != null);
        }

        /// <summary>
        /// Load this in a transaction, and handle all transaction and connection issues that might occur
        /// </summary>
        /// <param name="func">How to load this?</param>
        /// <returns></returns>
        private object LoadWithTransaction(Func<object> func)
        {
            object o = null;
            DoTransaction(() => { o = func(); });
            return o;
        }

        /// <summary>
        /// Prepare this string for query, on this 
        /// </summary>
        /// <param name="query"></param>
        /// <returns></returns>
        private MySqlCommand Prepare(string query)
        {
            if (_preparedStatements.ContainsKey(query))
            {
                var ps = _preparedStatements[query];
                ps.Parameters.Clear();
                return ps;
            }
            MySqlCommand cmd = new MySqlCommand(query);
            cmd.Connection = Connection;
            if (this.Transacting()) cmd.Transaction = _transaction;
            cmd.Prepare();
            _preparedStatements.Add(query, cmd);
            return cmd;
        }

        /// <summary>
        /// May i have a search query with this data mapping?
        /// </summary>
        /// <param name="tableName">The table to search in</param>
        /// <param name="data">The data mapping to use KEY:column name VALUE:search value</param>
        /// <param name="matching">The search matching type to use</param>
        /// <returns></returns>
        private MySqlCommand PrepareSearchQuery(string tableName, Dictionary<string, string> data, SearchMatching matching)
        {
            Contract.Requires(tableName != null);
            Contract.Requires(data != null);
            var queryBuilder = new StringBuilder("SELECT * FROM " + tableName + " WHERE ");
            var first = true;
            var wildcards = false;

            foreach (var kv in data)
            {
                if (string.IsNullOrWhiteSpace(kv.Value)) continue;
                if (!first) queryBuilder.Append(" AND ");
                queryBuilder.Append(kv.Key);
                switch (matching)
                {
                    case SearchMatching.Similair:
                        queryBuilder.Append(" LIKE ");
                        wildcards = true;
                        break;
                    case SearchMatching.Exact:
                        queryBuilder.Append(" = ");
                        break;
                }
                queryBuilder.Append("@");
                queryBuilder.Append(kv.Key);
                first = false;
            }
            queryBuilder.Append(";");

            var cmd = this.Prepare(queryBuilder.ToString());

            foreach (var kv in data)
            {
                if (!string.IsNullOrWhiteSpace(kv.Value))
                {
                    string value = kv.Value;
                    if (wildcards) value = "%" + value + "%";
                    cmd.Parameters.AddWithValue("@" + kv.Key, value);
                }
            }
            return cmd;
        }

        private void Execute(MySqlCommand cmd)
        {
            cmd.ExecuteNonQuery();
        }

        //Brug en scalar
        private void ScalarQuery(MySqlCommand cmd, Action<object> func)
        {
            object o = cmd.ExecuteScalar();
            func(o);
        }

        //Returner scalar
        private object ScalarQuery(MySqlCommand cmd)
        {
            object o = null;
            ScalarQuery(cmd, obj => o = obj);
            return o;
        }

        //Brug en reader
        private void Query(MySqlCommand cmd, Action<MySqlDataReader> func)
        {
            MySqlDataReader rdr = null;
            try
            {
                rdr = cmd.ExecuteReader();
                func(rdr);
            }
            finally
            {
                if (rdr != null) rdr.Close();
            }
        }

        //Do this only if the supplied lable on the supplied reader is not db-null
        private void DoIfNotDbNull(MySqlDataReader rdr, string label, Action<string> act)
        {
            int ordinal = rdr.GetOrdinal(label);
            if (!rdr.IsDBNull(ordinal))
            {
                act(label);
            }
        }
        #endregion
    }
}
