#ifndef _REPORT_H
#define _REPORT_H
/* This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */
#include "hare_clark.h"
#include "fraction.h"

/* Reporting interface: start, abandon (no result), end. */
extern void report_start(const struct election *, const struct candidate *vacating);
extern void report_end(unsigned int count, const char *title);

/* reset the value of the order of election of the next electee */
extern void reset_order_elected(void);

/* return value of counter */
extern unsigned int  get_order_elected(void);

/* increment counter, return unincremented value */
extern unsigned int  increment_order_elected(void);

/* Report operations */

/* Report the number of informals at start */
extern void report_informals(unsigned int num_informals);
/* Report the quota calculation at start for Table II */
extern void report_quota(unsigned int num_formals,
			 unsigned int num_seats,
			 unsigned int quota);
/* Report the ballots and votes exhausted at a given count */
extern void report_exhausted(unsigned int count,
			     unsigned int ballots_exhausted,
			     unsigned int votes_exhausted);
/* Report the number of ballots transferred to a candidate at a given
   count */
extern void report_ballots_transferred(unsigned int count,
				       unsigned int candidx,
				       enum cand_status status,
				       unsigned int ballots_added);
/* Report the number of votes transferred to a candidate at a given
   count */
extern void report_votes_transferred(unsigned int count,
				     unsigned int candpos,
				     enum cand_status status,
				     int added,
				     unsigned int new_total);
/* Report total number of votes and ballots after a given count */
extern void report_totals(unsigned int count,
			  unsigned int votes,
			  unsigned int ballots);
/* Report transfer value, and votes transferred to table II at a given count */
extern void report_transfer(unsigned int count,
			    struct fraction value,
			    unsigned int votes_transferred);
/* Whose papers are we distributing at the given count? */
extern void report_distribution(unsigned int count, const char *name);
/* What previous count did the papers at this count come from? */
extern void report_distrib_from_count(unsigned int count,
				      unsigned int prev_count);
/* Report loss/gain by fraction at a given count */
extern void report_lost_or_gained(unsigned int count, int gained);
/* Report that a candidate has met/passed quota */
extern void report_pending(unsigned int count, const char *name);
/* Report that a tiebreak decision was needed */
extern void report_tiebreak(unsigned int count, const char *reason,
			    const char *name);
/* Report that a candidate is elected */
extern void report_elected(unsigned int count, unsigned int candpos);
/* Report that a candidate is first excluded */
extern void report_excluded(unsigned int count, unsigned int candpos);
/* Report that a candidate is partially excluded */
extern void report_partially_excluded(unsigned int count, const char *name);
/* Report that a candidate is fully excluded */
extern void report_fully_excluded(unsigned int count, const char *name);

/* Get the quota (for casual vacancy) */
extern unsigned int report_get_quota(void);

/* Report majority (for casual vacancy) */
extern void report_majority(unsigned int count, unsigned int majority);

/* Report the vacating members vote total */
extern void report_vacancy_total_votes(unsigned int total);

/* Report the vacating members ballot  total */
extern void report_vacancy_total_ballots(unsigned int total);

/* print a newline to the raw data file for table 1 (counting)*/
void counting_raw_newline(void);

#endif /*_REPORT_H*/
