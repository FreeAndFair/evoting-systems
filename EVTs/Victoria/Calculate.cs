using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Vec.ComputerCount.DAL;
using Vec.ComputerCount.Entities;
using Vec.Common.Entities;
using Vec.ComputerCount.DALReporting;

namespace Vec.ComputerCount.BL
{
    public abstract class Calculate
    {
        protected IComputerCountResolver _Resolver;
        protected IReportingDAL _reporting;
        protected Guid _ElectionElectorateVacancyId;
        protected int _Vacancies;

        public Guid CalculationId { get; set; }

        public List<BallotPaperBL> BallotPapers { get; set; }
        public TieMethodType TieMethodType { get; set; }
        public CalculationMethod CalculationMethod { get; set; }
        public int InformalPapersTotal { get; set; }

        public List<MCandidate> Candidates { get; set; }
        public List<MCandidate> ExcludedCandidates { get; set; }
        public List<MCandidate> ElectedCandidates { get; set; }

        public List<MDistribution> Distributions { get; set; }
        public List<DistributionBL> DistributionQueue { get; set; }

        public CalculateState CalculationState { get; set; }

        #region Load Papers

        public virtual void LoadPapers()
        {
            IComputerCountDataContext dc = _Resolver.GetComputerCountDataContext(_ElectionElectorateVacancyId);

            var dcBallotPapers = dc.LoadBallotPapersWithFrequency();
            BallotPapers = new List<BallotPaperBL>();
            foreach (var x in dcBallotPapers)
            {
                BallotPapers.Add(new BallotPaperBL(_Resolver)
                {
                    BallotPaperId = x.BallotPaperId,
                    BallotPaperNbr = x.BallotPaperNbr,
                    BatchId = x.BatchId,
                    CycleNo = x.CycleNo,
                    Entries = x.Entries,
                    ExhaustAfter = (x.ExhaustAfter == null || x.ExhaustAfter <= 0 ? x.Entries.Count : (int)x.ExhaustAfter),
                    FormalFlag = x.FormalFlag,
                    Frequency = x.Frequency ?? 1,
                    Status = x.Status,
                    VoteType = x.VoteType,
                    WeightedTransferValue = x.WeightedTransferValue
                });
            }

            var candidates = BallotPapers.First().Entries.Select(x => x.Candidate).ToList();
            Candidates = candidates.OrderBy(x => x.Position).ToList();

            // load tickets
            var allocatedTickets = dc.GetAllocatedTickets();
            foreach (var at in allocatedTickets)
            {
                var ticketEntries = new List<MBallotPaperEntry>();
                foreach (var p in at.Preferences)
                {
                    ticketEntries.Add(new MBallotPaperEntry
                    {
                        BpValue = p.Value,
                        Candidate = new MCandidate { Position = p.Order, Name = p.Order.ToString() },
                        Mark = p.Value.ToString()
                    });
                }
                BallotPapers.Add(new BallotPaperBL(_Resolver)
                {
                    CycleNo = 0,
                    Entries = ticketEntries,
                    ExhaustAfter = at.Preferences.Count(),
                    FormalFlag = true,
                    Frequency = at.Votes,
                    Status = BallotPaperStatus.Entered,
                    VoteType = VoteType.AllVoteTypes,
                    WeightedTransferValue = 0
                });
            }

            var electorateCountState = dc.GetComputerCountElectorateState();
            InformalPapersTotal = electorateCountState.TotalInformal;

        }

        /// <summary>
        /// Load ballot papers from parameter list of papers. Typically used for testing.
        /// </summary>
        /// <param name="ballotpapers"></param>
        public void LoadPapers(List<BallotPaperBL> ballotpapers)
        {
            BallotPapers = ballotpapers;
        }

        #endregion


        #region Calculated Properties

        /// <summary>
        /// Get list of continuing candidates (those not Elected or Excluded).
        /// </summary>
        public virtual List<MCandidate> ContinuingCandidates
        {
            get
            {
                return (from c in Candidates
                        where !ElectedAndExcludedCandidates.Any(x => x.Position == c.Position)
                        select c).ToList();
            }
        }

        /// <summary>
        /// Quota
        /// </summary>
        public virtual int Quota {
            get
            {
                return ((CountPapers(BallotPapers) / (_Vacancies + 1))) + 1;
            }
        }

        /// <summary>
        /// Get list of Elected and Excluded candidates.
        /// </summary>
        public virtual List<MCandidate> ElectedAndExcludedCandidates
        {
            get
            {
                List<MCandidate> candidates = new List<MCandidate>();
                if (ElectedCandidates != null)
                {
                    candidates.AddRange(ElectedCandidates);
                }
                if (ExcludedCandidates != null)
                {
                    candidates.AddRange(ExcludedCandidates);
                }
                return candidates;
            }
        }

        /// <summary>
        /// Get the CycleNo of the most recent transfer
        /// </summary>
        public virtual int CurrentTransfer
        {
            get
            {
                return GetMostRecentTransfer().CycleNo;
            }
        }

        /// <summary>
        /// Get the candidate of the particular position
        /// </summary>
        /// <param name="Position">Position</param>
        /// <returns>Candidate</returns>
        public virtual MCandidate GetCandidate(int Position)
        {
            return Candidates.Where(c => c.Position == Position).First();
        }

        /// <summary>
        /// Returns true when all vacancies are all filled.
        /// </summary>
        /// <returns></returns>
        public virtual bool IsVacanciesFilled
        {
            get
            {
                return ElectedCandidates.Count >= _Vacancies;
            }
        }

        /// <summary>
        /// The number of vacancies still to fill.
        /// </summary>
        /// <returns></returns>
        public virtual int VacanciesToFill
        {
            get
            {
                return _Vacancies - ElectedCandidates.Count;
            }
        }

        #endregion

        #region Working with ballot papers

        /// <summary>
        /// Count ballot papers, taking Frequency into account.
        /// </summary>
        /// <param name="ballotpapers"></param>
        /// <returns></returns>
        public virtual int CountPapers(List<BallotPaperBL> ballotpapers)
        {
            return (from b in ballotpapers
                    select b.Frequency).Sum();
        }

        /// <summary>
        /// Calculates the transfer value a candidate based on their current ballot papers.
        /// </summary>
        /// <param name="candidate">Candidate for whom to calculate transfer value</param>
        /// <param name="transferValue">Calcaulated transfer value.</param>
        /// <param name="numerator">Numerator of transfer value calculation.</param>
        /// <param name="denominator">Demoninator of transfer value calculation.</param>
        protected virtual void GetCandidateTransferValue(MCandidate candidate, List<BallotPaperBL> workingBallotPapers, ref decimal transferValue, ref int numerator, ref int denominator)
        {
            // When elected by surplus of first preference votes GetCandidateBallotPapers and GetCandidateVotes are equal.
            // When elected by gaining quota through a transfer of votes, and some votes transferred are at part value, GetCandidateBallotPapers and GetCandidateVotes are not equal.
            // Calc for surplus of 1st prefs = (Papers over quota / total papers)
            // Calc for gaining quota through transfer = (Votes over quota / total papers)
            // If Papers = Votes for elected on 1st prefs, calculation is the same for either transfer type.

            // Cannot use GetCandidateVotes method on workingpapers to get total candidate Votes as candidate may have been
            // elected during Exclusion. GetCandidateVotes gets all votes if they had received all papers from the exclusion but they may have received only some.
            // Must use GetCandidateProgressTotalVotes to get their progress votes total from the Transfer log.

            numerator = GetCandidateProgressTotalVotes(candidate) - Quota;
            denominator = GetCandidateBallotPaperTotal(candidate, workingBallotPapers);
            transferValue = ((decimal)numerator / (decimal)denominator);
        }

        /// <summary>
        /// Counts the number of papers that are exhausted in a given set of papers.
        /// </summary>
        /// <param name="workingBallotPapers"></param>
        /// <returns></returns>
        public virtual int GetExhaustedBallotPapersCount(List<BallotPaperBL> workingBallotPapers)
        {
            return (from bps in workingBallotPapers
                    where bps.CurrentPreferencePosition(ElectedAndExcludedCandidates) == 0
                    select bps.Frequency).Sum();
        }

        /// <summary>
        /// Returns a list of papers currently belonging to a candidate.
        /// </summary>
        /// <param name="candidate"></param>
        /// <param name="workingBallotPapers"></param>
        /// <returns></returns>
        public virtual List<BallotPaperBL> GetCandidateBallotPapers(MCandidate candidate, List<BallotPaperBL> workingBallotPapers)
        {
            return (from w in workingBallotPapers
                    where w.CurrentPreferencePosition(ElectedAndExcludedCandidates) == candidate.Position
                    select w).ToList();
        }

        /// <summary>
        /// Gets all ballot papers for a candidate at a specific transfer value.
        /// </summary>
        /// <param name="candidate"></param>
        /// <param name="workingBallotPapers"></param>
        /// <returns></returns>
        public virtual List<BallotPaperBL> GetCandidateBallotPapersReceivedAtTransferValue(MCandidate candidate, List<BallotPaperBL> workingBallotPapers, decimal transferValue)
        {
            return (from bl in workingBallotPapers
                    where bl.CurrentPreferencePosition(ElectedAndExcludedCandidates) == candidate.Position
                    && bl.WeightedTransferValue == transferValue
                    select bl).ToList();
        }


        /// <summary>
        /// Return the total papers currently belonging to a candidate within a list of papers.
        /// </summary>
        /// <param name="candidate"></param>
        /// <param name="workingBallotPapers"></param>
        /// <returns></returns>
        protected virtual int GetCandidateBallotPaperTotal(MCandidate candidate, List<BallotPaperBL> workingBallotPapers)
        {
            return (from bps in workingBallotPapers
                    where bps.CurrentPreferencePosition(ElectedAndExcludedCandidates) == candidate.Position
                    select bps.Frequency).Sum();
        }

        /// <summary>
        /// Return a list of totals of papers belonging to candidates within a list of papers.
        /// </summary>
        /// <param name="workingBallotPapers"></param>
        /// <returns></returns>
        protected virtual List<int> GetCandidatesBallotPaperTotal(List<BallotPaperBL> workingBallotPapers)
        {
            // A candidate may have no papers, so must loop through all candidates getting count for each, cannot simply groupby
            return (from c in Candidates
                    orderby c.Position
                    select GetCandidateBallotPaperTotal(c, workingBallotPapers)).ToList();

        }

        /// <summary>
        /// Gets the total number of votes (total ballot papers taking into account transfer value) for a candidate.
        /// Assumes a single transfer value.
        /// Note that this will return 0 for elected candidates when elected candidates votes actually = quota.
        /// </summary>
        /// <param name="candidate">The candidate for whom you want the total votes</param>
        /// <returns></returns>
        protected virtual int GetCandidateVotes(MCandidate candidate, List<BallotPaperBL> workingBallotPapers)
        {
            // get sum of candidate's papers transfer value
            decimal sumvalues = (from bps in workingBallotPapers
                                 where bps.CurrentPreferencePosition(ElectedAndExcludedCandidates) == candidate.Position
                                 select (bps.WeightedTransferValue == 0 ? 1 : bps.WeightedTransferValue) * bps.Frequency).Sum();

            return (int)Math.Floor(sumvalues + (decimal)0.000000005);
        }

        /// <summary>
        /// Gets the total number of votes (total ballot papers taking into account transfer value) for a candidate.
        /// Assumes multiple transfer values in the list of papers.
        /// Total must be rounded down for each total of each set of papers at a transfer value.
        /// Note that this will return 0 for elected candidates when elected candidates votes actually = quota.
        /// </summary>
        /// <param name="candidate">The candidate for whom you want the total votes</param>
        /// <returns></returns>
        protected virtual int GetCandidateVotesMultiTransferValues(MCandidate candidate, List<BallotPaperBL> workingBallotPapers)
        {
            // get candidate's papers, grouped by transfer value
            var groupbytransfervalue = (from bps in workingBallotPapers
                                        where bps.CurrentPreferencePosition(ElectedAndExcludedCandidates) == candidate.Position
                                        group bps by bps.WeightedTransferValue into g
                                        select new { WeightedTransferValue = g.Key, SumWTV = g.Sum(w => (w.WeightedTransferValue == 0 ? 1 : w.WeightedTransferValue) * w.Frequency) });

            // return sum of the floor of each group
            // add 0.000000 etc. to ensure correct rounding in cases such as (0.33333 * 9, should = 3, not 2.999999 etc.)
            return (int)(from grouped in groupbytransfervalue
                         select Math.Floor(grouped.SumWTV + (decimal)0.000000005)).Sum();
        }

        /// <summary>
        /// Gets the total number of votes (total ballot papers taking into account transfer value) for each candidate in position order.
        /// Total must be rounded down for each total of each set of papers at a transfer value.
        /// Note that this will return 0 for elected candidates when elected candidates votes actually = quota.
        /// </summary>
        /// <returns></returns>
        protected virtual List<int> GetCandidatesVotes(List<BallotPaperBL> workingBallotPapers)
        {
            // A candidate may have no papers, so must loop through all candidates getting count for each, cannot simply groupby
            return (from c in Candidates
                    orderby c.Position ascending
                    select GetCandidateVotes(c, workingBallotPapers)).ToList();

        }

        #endregion

        #region Current Distributions and Transfers
        /// <summary>
        /// Get most recent transfer totals.
        /// </summary>
        /// <returns></returns>
        protected virtual MTransfer GetMostRecentTransfer()
        {
            if (Distributions.Count > 0)
            {
                // get last distribution
                MDistribution d = (from ds in Distributions
                                   orderby ds.Step descending
                                   select ds).First();
                // get last transfer of distribution
                return (from ts in d.Transfers
                        orderby ts.CycleNo descending
                        select ts).First();
            }
            else
            {
                //throw new Exception("This count has not completed any distributions.");

                List<MCandidateAllocation> cas = new List<MCandidateAllocation>();

                if (Candidates.Count > 0)
                {
                    foreach (MCandidate c in Candidates.OrderBy(x => x.Position))
                    {
                        cas.Add(new MCandidateAllocation
                        {
                            BallotPapers = 0,
                            Candidate = c,
                            CountStatus = CandidateCountStatus.Continuing,
                            ElectorOrExcludeOrder = 0,
                            TotalBallotPapers = 0,
                            TotalVotes = 0,
                            Votes = 0
                        });
                    }
                }

                return new MTransfer
                {
                    CycleNo = 0,
                    CandidateAllocations = cas,
                    BallotPapersTotal = 0,
                    ExhaustedPapers = 0,
                    ExhaustedVotes = 0,
                    TotalExhaustedVotes = 0,
                    TotalExhaustedPapers = 0,
                    GainLoss = 0,
                    TotalGainLoss = 0,
                    WeightedTransferValue = 0
                };
            }
        }

        /// <summary>
        /// Get the progress total as of now for a specific candidate
        /// </summary>
        /// <param name="candidate"></param>
        /// <returns></returns>
        public virtual int GetCandidateProgressTotalVotes(MCandidate candidate)
        {
            // get most recent Total Votes (progress total) for a candidate
            List<MCandidateAllocation> lastallocations = GetMostRecentTransfer().CandidateAllocations;
            return (from ca in lastallocations
                    where ca.Candidate.Position == candidate.Position
                    select ca.TotalVotes).FirstOrDefault();
        }

        /// <summary>
        /// Look through previous transfers to determine at which transfers a candidate received papers at the indicated value.
        /// </summary>
        /// <param name="candidate"></param>
        /// <param name="weightedTransferValue"></param>
        /// <returns></returns>
        protected virtual string GetFromCycleNumbers(MCandidate candidate, decimal weightedTransferValue)
        {
            string returnval = string.Empty;
            List<int> fromCycleList = new List<int>();

            foreach (MDistribution d in (from ds in Distributions where ds.DistributionType != DistributionType.Initial select ds))
            {
                foreach (MTransfer t in d.Transfers.Where(x => x.WeightedTransferValue == weightedTransferValue))
                {
                    if (t.CandidateAllocations.Where(x => x.Candidate.Position == candidate.Position).First().BallotPapers > 0)
                    {
                        fromCycleList.Add(t.CycleNo);
                    }
                }
            }

            fromCycleList.Sort();
            returnval = String.Join(",", fromCycleList);
            return returnval;
        }

        /// <summary>
        /// Looks through previous Transfers and sums all votes transferred to the candidate.
        /// Used for calculating the votes transferred from a candidate during an exclusion of a candidate.
        /// </summary>
        /// <param name="candidate"></param>
        /// <param name="weightedTransferValue"></param>
        /// <returns></returns>
        protected virtual int GetSumVotesReceivedByCandidateAtTransferValue(MCandidate candidate, decimal weightedTransferValue)
        {
            int total = 0;
            foreach (MDistribution d in Distributions)
            {
                List<MTransfer> ts = (from t in d.Transfers
                                      where t.WeightedTransferValue == weightedTransferValue
                                      select t).ToList();

                foreach (MTransfer t in ts)
                {
                    MCandidateAllocation allocation = (from ca in t.CandidateAllocations
                                                       where ca.Candidate.Position == candidate.Position
                                                       select ca).First();
                    total += allocation.Votes;
                }
            }
            return total;
        }

        /// <summary>
        /// Gets list of unelected/unexcluded candidates who have passed quota.
        /// </summary>
        /// <returns></returns>
        public virtual List<MCandidate> GetPassedQuotaCandidates()
        {
            // get unelected/unexcluded candidate(s) with total votes >= Quota
            List<MCandidateAllocation> lastallocations = GetMostRecentTransfer().CandidateAllocations;
            return (from ca in lastallocations
                    where !ElectedAndExcludedCandidates.Any(x => x.Position == ca.Candidate.Position)
                    && ca.TotalVotes >= Quota
                    orderby ca.TotalVotes descending, ca.Candidate.Position
                    select ca.Candidate).ToList();
        }

        /// <summary>
        /// Gets list of unelected/unexcluded candidates whose current progress total is the highest.
        /// Multiple would indicate a tie. Used to decide elect and surplus distributions.
        /// </summary>
        /// <returns></returns>
        public virtual List<MCandidate> GetCandidatesWithHighestVotes()
        {
            // get candidate(s) with the highest number of votes
            List<MCandidateAllocation> lastallocations = GetMostRecentTransfer().CandidateAllocations;
            int maxvotes = (from ca in lastallocations
                            where !ElectedAndExcludedCandidates.Any(x => x.Position == ca.Candidate.Position)
                            orderby ca.TotalVotes descending
                            select ca.TotalVotes).FirstOrDefault();

            return (from ca in lastallocations
                    where ca.TotalVotes == maxvotes
                    && !ElectedAndExcludedCandidates.Any(x => x.Position == ca.Candidate.Position)
                    orderby ca.Candidate.Position
                    select ca.Candidate).ToList();
        }

        /// <summary>
        /// Gets list of unelected/unexcluded candidates whose current progress total is the least.
        /// Multiple would indicate a tie. Used to decide exclusions.
        /// </summary>
        /// <returns></returns>
        public virtual List<MCandidate> GetCandidatesWithLowestVotes()
        {
            // get candidate(s) with the lowest number of votes
            List<MCandidateAllocation> lastallocations = GetMostRecentTransfer().CandidateAllocations;
            int minvotes = (from ca in lastallocations
                            where !ElectedAndExcludedCandidates.Any(x => x.Position == ca.Candidate.Position)
                            orderby ca.TotalVotes ascending
                            select ca.TotalVotes).First();
            return (from ca in lastallocations
                    where ca.TotalVotes == minvotes
                    && !ElectedAndExcludedCandidates.Any(x => x.Position == ca.Candidate.Position)
                    orderby ca.Candidate.Position
                    select ca.Candidate).ToList();
        }

        /// <summary>
        /// returns list of candidates with their surplus tie condition and their votes
        /// </summary>
        /// <param name="candidates">List of over-quota candidates</param>
        /// <returns>list of MCandidateEx</returns>
        public virtual List<MCandidateEx> GetSurplusTiedCandidates(List<MCandidate> candidates)
        {
            List<MCandidateAllocation> lastallocations = GetMostRecentTransfer().CandidateAllocations;

            /// Get the votes of the input candidates and save their current total votes
            var result = (from ca in lastallocations
                          where !ElectedAndExcludedCandidates.Any(x => x.Position == ca.Candidate.Position) &&
                          candidates.Any(x => x.Position == ca.Candidate.Position) &&
                          ca.TotalVotes >= Quota
                          let mex = new MCandidateEx(ca.Candidate) { CurrentTotalVotes = ca.TotalVotes }
                          orderby ca.TotalVotes descending, ca.Candidate.Position
                          select mex).ToList();

            /// Set the tie flag to true if exists any other candidate with the same vote
            foreach (MCandidateEx mex in result)
            {
                mex.IsTie = result.Any(x => x.CurrentTotalVotes == mex.CurrentTotalVotes && x.Position != mex.Position);
            }

            return result;
        }

        public virtual void SetCandidateCountStatus(MCandidate candidate, CandidateCountStatus ccs)
        {
            // mark last Transfer as the point this candidate was elected/excluded
            MTransfer lasttransfer = GetMostRecentTransfer();
            int maxorder = 0;
            if (lasttransfer.CandidateAllocations.Count > 0)
            {
                maxorder = lasttransfer.CandidateAllocations.Select(x => x.ElectorOrExcludeOrder).Max();
            }
            MCandidateAllocation cas = (from ca in lasttransfer.CandidateAllocations where ca.Candidate.Position == candidate.Position select ca).FirstOrDefault();
            if (cas != null)
            {
                cas.CountStatus = ccs;
                if (ccs == CandidateCountStatus.Elected || ccs == CandidateCountStatus.Excluded)
                {
                    cas.ElectorOrExcludeOrder = maxorder + 1;
                }
            }
        }

        protected virtual List<MCandidate> GetHighestDifferenceInCycle(List<MCandidate> tiedCandidatesToResolve)
        {
            List<MCandidate> resolvingCandidates = new List<MCandidate>(tiedCandidatesToResolve);

            foreach (MDistribution d in Distributions.OrderByDescending(x => x.Step))
            {
                if (resolvingCandidates.Count > 1)
                {
                    foreach (MTransfer t in d.Transfers.OrderByDescending(x => x.CycleNo))
                    {
                        var ca = (from cas in t.CandidateAllocations
                                  join tied in resolvingCandidates on cas.Candidate.Position equals tied.Position
                                  orderby cas.TotalVotes descending
                                  select new { tied.Position, cas.TotalVotes });

                        List<int> distinctTotalVotes = (from c in ca
                                                        select c.TotalVotes).Distinct().ToList();

                        // if more than one distinct value, tie may be resolved
                        if (distinctTotalVotes.Count() > 1)
                        {
                            // get the highest total in the distinct list
                            int highesttotal = distinctTotalVotes.OrderByDescending(x => x).First();

                            // get all candidates (positions) who have that total
                            var highestTotalCandidates = (from c in ca
                                                          where c.TotalVotes == highesttotal
                                                          select c).ToList();

                            List<MCandidate> candidatesToRemove = (from rc in resolvingCandidates
                                                                   where !highestTotalCandidates.Exists(x => x.Position == rc.Position)
                                                                   select rc).ToList();

                            // remove all from resolved candidates list who do not have the highest votes
                            foreach (MCandidate c in candidatesToRemove)
                            {
                                resolvingCandidates.Remove(c);
                            }

                        }
                    }
                }
            }

            return resolvingCandidates;

        }

        /// <summary>
        /// Distributes a parcel of papers to candidates.
        /// Creates new MTransfer, that holds the papers allocated to all candidates and their running totals
        /// Adds this MTransfer to the current Distribution
        /// creates a new current Distribution if a new candidate is being distributed
        /// Called by  RunNextQueuedDistribution
        /// </summary>
        /// <param name="candidate">The candidate being distributed. Null if Initial distribution.</param>
        /// <param name="workingpapers">The papers being distributed</param>
        /// <param name="distType">Distribution type</param>
        public virtual void Distribute(MCandidate candidate, List<BallotPaperBL> workingpapers, DistributionType distType, decimal transferValue, int transferVotes)
        {
            // assumes excluded candidate has been added to Excluded list
            int maxdistribution = 0;
            MDistribution lastDistribution = new MDistribution();
            MDistribution thisDistribution = new MDistribution();
            bool newDistribution = false;

            // if this is the first/initial distribution there may be no distributions
            if (Distributions.Count > 0)
            {
                maxdistribution = Distributions.Select(x => x.Step).Max();
                lastDistribution = (from ds in Distributions
                                    where ds.Step == maxdistribution
                                    select ds).FirstOrDefault();
            }

            // if this distribution is for a different candidate (or was 1st distribution/no candidate) to the previous distribution, create a new one
            if (lastDistribution.Candidate == null ||
                lastDistribution.Candidate.Position != candidate.Position)
            {
                // New distribution
                thisDistribution = new MDistribution()
                {
                    DistributionType = distType,
                    Step = maxdistribution + 1,
                    Candidate = candidate,
                    Transfers = new List<MTransfer>()
                };
                newDistribution = true;
            }
            else
            {
                thisDistribution = lastDistribution;
            }

            thisDistribution.Transfers.Add(CreateNewTransfer(distType, candidate, workingpapers, transferValue, transferVotes));

            if (newDistribution)
            {
                Distributions.Add(thisDistribution);
            }
        }


        /// <summary>
        /// Creates a new MTransfer, setting candidate allocations based on working papers.
        /// Called by Distribute.
        /// </summary>
        /// <param name="distType"></param>
        /// <param name="candidate"></param>
        /// <param name="workingpapers"></param>
        /// <returns></returns>
        protected virtual MTransfer CreateNewTransfer(DistributionType distType, MCandidate candidate, List<BallotPaperBL> workingpapers, decimal transferValue, int transferVotes)
        {
            string fromCycles = string.Empty;
            int workingpaperscount = CountPapers(workingpapers);

            MTransfer lasttransfer = GetMostRecentTransfer();
            List<MCandidateAllocation> lastallocations = (from cas in lasttransfer.CandidateAllocations
                                                          orderby cas.Candidate.Position
                                                          select cas).ToList();

            // If surplus transfer, weighted value will have changed, update papers.
            // Transfer value used by GetCandidatesVotes(workingpapers) (note this method counts 0 as 1)
            if (distType == DistributionType.Surplus && transferValue > 0 && transferValue < 1)
            {
                workingpapers.ForEach(x => x.WeightedTransferValue = transferValue);
            }

            List<int> addedpapers = GetCandidatesBallotPaperTotal(workingpapers);
            List<int> addedvotes = GetCandidatesVotes(workingpapers);
            int totaladdedvotes = addedvotes.Sum();

            // get list of cycles this candidate received papers at this transfer value
            if (distType == DistributionType.Exclusion && workingpaperscount > 0 && candidate != null)
            {
                if (transferValue == 0)
                {
                    fromCycles = "1";
                }
                else
                {
                    fromCycles = GetFromCycleNumbers(candidate, transferValue);
                }
            }

            if (distType == DistributionType.Exclusion && transferValue == 0)
            {
                workingpapers.ForEach(x => x.WeightedTransferValue = 1);
                transferValue = 1;
            }

            int exhaustedpapers = GetExhaustedBallotPapersCount(workingpapers);
            int exhaustedvalue = (int)Math.Floor((decimal)exhaustedpapers * transferValue);
            int gainloss = transferVotes - totaladdedvotes - exhaustedvalue;

            // new transfer, in pref only one transfer per distribution
            MTransfer t = new MTransfer()
            {
                BallotPapersTotal = workingpaperscount,
                VotesTotal = transferVotes,
                CycleNo = lasttransfer.CycleNo + 1,
                FromCycles = fromCycles,
                ExhaustedPapers = exhaustedpapers,
                ExhaustedVotes = exhaustedvalue,
                GainLoss = gainloss,
                TotalExhaustedPapers = lasttransfer.TotalExhaustedPapers + exhaustedpapers,
                TotalExhaustedVotes = lasttransfer.TotalExhaustedVotes + exhaustedvalue,
                TotalGainLoss = lasttransfer.TotalGainLoss + gainloss,
                WeightedTransferValue = transferValue,
                CandidateAllocations = new List<MCandidateAllocation>()
            };

            int position = 0;
            foreach (MCandidateAllocation lastca in lastallocations)
            {
                // at this point the candidate being transferred will have an added papers total of 0
                // we want it to be negative as the papers are being transferred away from them
                if (distType != DistributionType.Initial)
                {
                    if ((position + 1) == candidate.Position)
                    {
                        addedpapers[position] = (workingpaperscount * -1);
                        addedvotes[position] = (transferVotes * -1);
                    }
                }

                MCandidateAllocation newca = new MCandidateAllocation()
                {
                    BallotPapers = addedpapers[position],
                    Votes = addedvotes[position],
                    Candidate = GetCandidate(position + 1),
                    CountStatus = lastca.CountStatus,
                    ElectorOrExcludeOrder = lastca.ElectorOrExcludeOrder,
                    TotalBallotPapers = lastca.TotalBallotPapers + addedpapers[position],
                    TotalVotes = lastca.TotalVotes + addedvotes[position]
                };
                t.CandidateAllocations.Add(newca);
                position += 1;
            }

            // stamp each paper with cycle that transferred them
            workingpapers.ForEach(x => x.CycleNo = lasttransfer.CycleNo + 1);

            return t;
        }

        /// <summary>
        /// Determine the total votes being transferred in a single cycle/transfer.
        /// </summary>
        /// <param name="candidate"></param>
        /// <param name="transferValue"></param>
        /// <returns></returns>
        protected int DetermineTotalVotesForTransfer(MCandidate candidate, DistributionType distType, int ballotPaperCount, decimal transferValue)
        {
            int transferVotes = 0;
            var lasttransfer = GetMostRecentTransfer();

            if (transferValue != 1 && transferValue != 0)
            {
                switch (distType)
                {
                    case DistributionType.Exclusion:
                        transferVotes = GetSumVotesReceivedByCandidateAtTransferValue(candidate, transferValue);
                        break;
                    case DistributionType.Surplus:
                        int candidatePTotal = (from ca in lasttransfer.CandidateAllocations
                                               where ca.Candidate.Position == candidate.Position
                                               select ca.TotalVotes).First();
                        transferVotes = candidatePTotal - Quota;
                        break;
                    default:
                        transferVotes = ballotPaperCount;
                        break;
                }
            }
            else
            {
                // if transfer value is 1 (or 0, first preference paper), votes transferred = total papers
                transferVotes = ballotPaperCount;
            }
            
            return transferVotes;
        }


        #endregion

        #region Distribution Queue

        /// <summary>
        /// Adds first/initial distribution to the Distribution Cue
        /// </summary>
        public virtual void QueueDistributionOf1stPreferences()
        {
            AddDistributionToQueue(DistributionType.Initial, null, BallotPapers);
        }

        /// <summary>
        /// Queue a single surplus distribution for a candidate.
        /// </summary>
        /// <param name="candidate"></param>
        public virtual void QueueSurplusDistribution(MCandidate candidate)
        {
            List<BallotPaperBL> bps = GetCandidateBallotPapers(candidate, BallotPapers);
            List<BallotPaperBL> excludeList = new List<BallotPaperBL>();

            // Candidates elected during an exclusion should not receive any more papers.
            // GetCandidateBallotPapers returns ALL papers a candidate would receieve based purely on current Elected/Excluded candidates.
            // Papers this candidate would receive in future distributed parcels (if any) must be removed before creating surplus parcel.
            foreach (DistributionBL d in DistributionQueue)
            {
                excludeList.AddRange(d.BallotPapers);
            }

            AddDistributionToQueue(DistributionType.Surplus, candidate, bps.Except(excludeList).ToList());
        }


        /// <summary>
        /// Queue surplus distributions for a list of candidates (in distribution order)
        /// </summary>
        /// <param name="candidatesToQueue"></param>
        public virtual void QueueSurplusDistributions(List<MCandidate> candidatesToQueue)
        {
            foreach (MCandidate candidateToQueue in candidatesToQueue)
            {
                QueueSurplusDistribution(candidateToQueue);
            }
        }

        /// <summary>
        /// Create a new Queued distribution and add to the Queue (to be distributed in order).
        /// A PR exclusion may create multiple Queued distributions (one per parcel).
        /// </summary>
        /// <param name="distType"></param>
        /// <param name="candidate"></param>
        /// <param name="paperstotransfer"></param>
        public virtual void AddDistributionToQueue(DistributionType distType, MCandidate candidate, List<BallotPaperBL> paperstotransfer)
        {
            int lastQueuedStepNumber = DistributionQueue.Count;
            // if last queued > 0, must be some in cue. Get max Step of queue.
            if (lastQueuedStepNumber > 0)
            {
                lastQueuedStepNumber = DistributionQueue.Max(x => x.Step);
            }
            lastQueuedStepNumber++;

            int countOfPapersToTransfer = CountPapers(paperstotransfer);            
            
            if (distType == DistributionType.Exclusion && 
                (CalculationMethod == CalculationMethod.Proportional || CalculationMethod == CalculationMethod.Countback))
            {
                // Get distinct list of transfer values available in this candidate's papers
                List<decimal> transfervalues = paperstotransfer.Select(x => x.WeightedTransferValue).Distinct().ToList();

                // order by transfer value descending, with 0 (1st prefs) forced to be first
                List<decimal> tvsOrderDesc = new List<decimal>();

                if (transfervalues.Any(x => x == 0))
                {
                    tvsOrderDesc.Add(0);
                };
                tvsOrderDesc.AddRange((from tv in transfervalues where tv != 0 orderby tv descending select tv).ToList());

                // create a Queued distribution for each parcel of papers at each transfer value
                foreach (decimal transfervalue in tvsOrderDesc)
                {
                    // GetCandidateBallotPapersReceievedAtTransferValue will not include 1st preference papers for the candidate
                    List<BallotPaperBL> parcel = GetCandidateBallotPapersReceivedAtTransferValue(candidate, paperstotransfer, transfervalue);
                    int countOfPapersInParcel = CountPapers(parcel);
                    int votesTransferring = DetermineTotalVotesForTransfer(candidate, distType, countOfPapersInParcel, transfervalue);

                    if (parcel.Count > 0)
                    {
                        // do not update transfer value of 0 value (1st pref) papers at this point. They are updated when transferred.
                        QueueDistribution(parcel, candidate, distType, lastQueuedStepNumber, transfervalue, votesTransferring);

                        lastQueuedStepNumber++;
                    }
                }

                // if no transfer values, this candidate has no papers at all
                // Add a 0 value transfer of 0 1st pref ballot papers
                if (tvsOrderDesc.Count == 0)
                {
                    QueueDistribution(new List<BallotPaperBL>(), candidate, distType, lastQueuedStepNumber, 0, 0);
                }

            }
            else
            {
                if (distType == DistributionType.Surplus)
                {
                    // if candidate has surplus, calculate transfer value, set all papers to that transfer value and add to Queued distribution list
                    if ((GetCandidateProgressTotalVotes(candidate) - Quota) > 0)
                    {
                        int numerator = 0;
                        int denominator = 0;
                        decimal transferValue = 0;
                        GetCandidateTransferValue(candidate, paperstotransfer, ref transferValue, ref numerator, ref denominator);
                        int votesTransferring = DetermineTotalVotesForTransfer(candidate, distType, countOfPapersToTransfer, transferValue);
                        QueueDistribution(paperstotransfer, candidate, distType, lastQueuedStepNumber, transferValue, votesTransferring);
                    }

                    // if candidate has exactly quota, need to set papers as Immovable (ie. they cannot be transferred to a candidate any more)
                    else
                    {
                        foreach (BallotPaperBL bp in paperstotransfer)
                        {
                            bp.ImmovablePosition = candidate.Position;
                        }
                    }

                }
                else
                {
                    QueueDistribution(paperstotransfer, candidate, distType, lastQueuedStepNumber, 1, countOfPapersToTransfer);
                };
            }
        }


        public virtual bool IsQueuedDistributions
        {
            get
            {
                return DistributionQueue.Count() > 0;
            }
        }

        public virtual void RunNextQueuedDistribution()
        {
            if (IsQueuedDistributions)
            {
                DistributionBL nextQueuedDistribution = (from fd in DistributionQueue
                                                         orderby fd.Step ascending
                                                         select fd).FirstOrDefault();

                Distribute(nextQueuedDistribution.Candidate, nextQueuedDistribution.BallotPapers, nextQueuedDistribution.DistributionType, nextQueuedDistribution.Transfers[0].WeightedTransferValue, nextQueuedDistribution.Transfers[0].VotesTotal);

                // ensure pre-count excluded candidates (Deceased/Retired etc.) are marked as excluded in first count
                if (nextQueuedDistribution.DistributionType == DistributionType.Initial)
                {
                    ExcludedCandidates.ForEach(x => SetCandidateCountStatus(x, CandidateCountStatus.NotParticipating));
                }
                
                DistributionQueue.Remove(nextQueuedDistribution);
            }
        }

        protected virtual void QueueDistribution(List<BallotPaperBL> papers, MCandidate candidate, DistributionType distType, int step, decimal transferValue, int totalVotes)
        {
            DistributionBL dbl = new DistributionBL
            {
                BallotPapers = papers,
                DistributionType = distType,
                Candidate = candidate,
                Step = step,
                Transfers = new List<MTransfer>()
            };
            dbl.Transfers.Add(new MTransfer { WeightedTransferValue = transferValue, VotesTotal = totalVotes });
            DistributionQueue.Add(dbl);
        }


        #endregion

        #region Excluding Candidates

        /// <summary>
        /// From a list of candidates who are currently tied, determine who had the lowest votes the last time the
        /// candidates were not tied. If tie cannot be resolved (ie. candidates have always been tied) then a candidate
        /// picked randomly. If a tie can be resolved, the candidate with the lowest votes last time
        /// candidates were different will be returned.
        /// If there are >2 tied candidates and at a past distribution less are tied, work back through previous distributions only for those two.
        /// eg. T3: 10,10,10  |  T2: 9,9,10  | T1: 9,8,7  - The second candidate is picked.
        /// </summary>
        /// <param name="tiedCandidatesToResolve"></param>
        /// <returns></MCandidate></returns>
        public virtual List<MCandidate> ResolvePRExclusionTie(List<MCandidate> tiedCandidatesToResolve)
        {
            List<MCandidate> resolvedCandidates = new List<MCandidate>(tiedCandidatesToResolve);

            foreach (MDistribution d in Distributions.OrderByDescending(x => x.Step))
            {
                if (resolvedCandidates.Count > 1)
                {
                    foreach (MTransfer t in d.Transfers.OrderByDescending(x => x.CycleNo))
                    {
                        var ca = (from cas in t.CandidateAllocations
                                  from tied in resolvedCandidates
                                  where cas.Candidate.Position == tied.Position
                                  orderby cas.TotalVotes ascending
                                  select new { tied.Position, cas.TotalVotes });

                        List<int> distinctTotalVotes = (from c in ca
                                                        select c.TotalVotes).Distinct().ToList();

                        // if more than one distinct value, tie may be resolved
                        if (distinctTotalVotes.Count() > 1)
                        {
                            // get the lowest total in the distinct list
                            int lowestTotal = distinctTotalVotes.OrderBy(x => x).First();

                            // get all candidates (positions) who have that total
                            var lowestTotalCandidates = (from c in ca
                                                         where c.TotalVotes == lowestTotal
                                                         select c).ToList();

                            List<MCandidate> candidatesToRemove = (from rc in resolvedCandidates
                                                                   where !lowestTotalCandidates.Exists(x => x.Position == rc.Position)
                                                                   select rc).ToList();

                            // remove all from resolved candidates list who do not have the lowest votes
                            foreach (MCandidate c in candidatesToRemove)
                            {
                                resolvedCandidates.Remove(c);
                            }

                        }
                    }
                }
            }

            // after resolving we haven't found a single excluded candidate? Pick one at random.
            if (resolvedCandidates.Count > 1)
            {
                int resolvedCount = resolvedCandidates.Count;
                int randomIndex = RandomHelper.RandomNumberBetweenMinAndMaxInclusive(0, resolvedCount - 1);
                MCandidate randomlyPickedCandidate = resolvedCandidates[randomIndex];
                resolvedCandidates.Clear();
                resolvedCandidates.Add(randomlyPickedCandidate);
            }

            return resolvedCandidates;
        }


        /// <summary>
        /// 1. Get papers for candidates.
        /// 2. Add to Queued distributions list.
        /// </summary>
        /// <param name="candidate"></param>
        public virtual void ExcludeCandidate(MCandidate candidate)
        {
            List<BallotPaperBL> bps = GetCandidateBallotPapers(candidate, BallotPapers);
            AddDistributionToQueue(DistributionType.Exclusion, candidate, bps);
            AddExcludedCandidate(candidate);
        }

        /// <summary>
        /// Adds a candidate to the excluded list without adding a distribution to the queue.
        /// Intended for Deceased/Retired candidates who were on the ballot paper but will not be included in the count.
        /// </summary>
        /// <param name="candidate"></param>
        public virtual void ExcludeCandidateWithoutDistribution(MCandidate candidate)
        {
            AddExcludedCandidate(candidate);
        }

        /// <summary>
        /// Add excluded candidate to list. Raise exception if already excluded.
        /// </summary>
        /// <param name="candidate"></param>
        public virtual void AddExcludedCandidate(MCandidate candidate)
        {
            if (!ExcludedCandidates.Any(x => x.Position == candidate.Position))
            {
                ExcludedCandidates.Add(candidate);
                SetCandidateCountStatus(candidate, CandidateCountStatus.Excluded);
            }
            else
            {
                throw new Exception(string.Format("Candidate {0} has already been excluded.", candidate.Name));
            }
        }

        #endregion 

        #region Electing Candidates
        
        /// <summary>
        ///  Add candidate to elected list.
        /// </summary>
        /// <param name="candidate"></param>
        public virtual void ElectCandidate(MCandidate candidate)
        {
            AddElectedCandidate(candidate);
        }

        protected virtual void AddElectedCandidate(MCandidate candidate)
        {
            if (!ElectedCandidates.Any(x => x.Position == candidate.Position))
            {
                ElectedCandidates.Add(candidate);
                SetCandidateCountStatus(candidate, CandidateCountStatus.Elected);
            }
            else
            {
                throw new Exception(string.Format("Candaidate {0} has already been elected.", candidate.Name));
            }
        }

        /// <summary>
        /// Resolve tie of over quota candidates.
        /// </summary>
        /// <param name="tiedCandidatesToResolve"></param>
        /// <returns></returns>
        public List<MCandidate> ResolvePRSurplusTie(List<MCandidateEx> tiedCandidatesToResolve)
        {
            List<MCandidate> currentlyTiedCandidates = new List<MCandidate>(tiedCandidatesToResolve.Select(x => new MCandidate { Name = x.Name, Position = x.Position }).ToList());

            List<MCandidate> returnlist = new List<MCandidate>();
            do
            {
                if (currentlyTiedCandidates.Count == 1)
                {
                    returnlist.Add(currentlyTiedCandidates[0]);
                }
                else
                {
                    List<MCandidate> resolvedCandidates = GetHighestDifferenceInCycle(currentlyTiedCandidates);
                    if (resolvedCandidates.Count == 1)
                    {
                        returnlist.Add(resolvedCandidates[0]);
                    }
                    else
                    {
                        int resolvedCount = resolvedCandidates.Count;
                        int randomIndex = RandomHelper.RandomNumberBetweenMinAndMaxInclusive(0, resolvedCount - 1);
                        returnlist.Add(resolvedCandidates[randomIndex]);
                    }

                    foreach (MCandidate c in returnlist)
                    {
                        currentlyTiedCandidates.Remove(c);
                    }
                }
            } while (returnlist.Count < tiedCandidatesToResolve.Count);

            return returnlist;
        }

        #endregion

        #region Database
        /// <summary>
        /// Save the current state of the calculation to the database.
        /// Assumes correctly set connection string.
        /// </summary>
        /// <returns></returns>
        protected virtual void Save()
        {
            MCalculation currentcalc = new MCalculation
            {
                CalculationId = CalculationId,
                ElectionElectorateVacancyId = _ElectionElectorateVacancyId,
                Quota = Quota,
                TotalBallotPapers = CountPapers(BallotPapers) + InformalPapersTotal,
                TotalFormalBallotPapers = CountPapers(BallotPapers),
                TotalInformalBallotPapers = InformalPapersTotal,
                Vacancies = _Vacancies,
                CalculateDateTime = DateTime.Now,
                CalculationState = CalculationState,
                CalculationMethod = CalculationMethod,
                CalculatedByComputer = true
            };

            _Resolver.GetComputerCountDataContext(_ElectionElectorateVacancyId)
            .SaveCalculation(currentcalc, Distributions);

            //Check if state is finished and then save to ReportingWarehouse database.
            if (currentcalc.CalculationState == CalculateState.Finished)
            {
                _reporting.SaveCalculation(currentcalc, Distributions);
            }
        }

        /// <summary>
        /// Remove an existing Calculation from the database.
        /// </summary>
        protected virtual void Delete()
        {
            _Resolver.GetComputerCountDataContext(_ElectionElectorateVacancyId)
                .DeleteCalculation(CalculationId);
        }

        #endregion


    }
}
