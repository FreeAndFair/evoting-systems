using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Data;
using Vec.ComputerCount.Entities;
using System.Runtime.Serialization;
using Vec.Common.Entities;
using Vec.ComputerCount.DAL;
using Vec.ComputerCount.DALReporting;

namespace Vec.ComputerCount.BL
{

    /// <summary>
    /// 
    /// </summary>
    /// <versions><version number="1.0.0.0" date="3/08/2011" author="andrewb">Initial version.</version></versions>
    /// 
    public class CalculateBL : Calculate, ICalculateBL
    {
        #region properties

        protected string _ConnectionString;

        #endregion

        #region contructors

        public CalculateBL(IComputerCountResolver resolver, IReportingDAL reporting)
        {
            _Resolver = resolver;
            _reporting = reporting;
            Initialise();
        }


        public CalculateBL(Guid ElectionElectorateVacancyId, int Vacancies, CalculationMethod CalcMethod, TieMethodType TieMethod, IComputerCountResolver resolver, IReportingDAL reporting)
            : this(resolver, reporting)
        {
            _ElectionElectorateVacancyId = ElectionElectorateVacancyId;
            _Vacancies = Vacancies;
            TieMethodType = TieMethod;
            CalculationMethod = CalcMethod;
        }

        private void Initialise()
        {
            InformalPapersTotal = 0;
            ElectedCandidates = new List<MCandidate>();
            ExcludedCandidates = new List<MCandidate>();
            Candidates = new List<MCandidate>();
            Distributions = new List<MDistribution>();
            DistributionQueue = new List<DistributionBL>();
        }

        #endregion

    }

    public interface ICalculateBL
    {
    }

}
