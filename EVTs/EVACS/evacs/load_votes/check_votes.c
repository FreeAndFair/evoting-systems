/* This file is (C) copyright 2001 Software Improvements, Pty Ltd */

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
#include <stdlib.h>
#include <string.h>
#include <common/database.h>
#include <common/evacs.h>
#include "check_votes.h"
#include "compare_votes.h"

struct vote_list *table1_votes=NULL, *table2_votes=NULL;


/*
  Compare two integers. Return +ve one if a greater, -ve one if b greater,
  otherwise return zero. This is used by cmp_votes. 
*/
static int compare_int(int a, int b)
{
	if (a>b)
		return 1;
	if (a<b)
		return -1;
	return 0;
}

/*
  Compare 2 votes.
  Return +ve one if the first vote is higher, return -ve one if the second
  is higher, otherwise return 0.
  This function is used by qsort.
*/
static int cmp_votes(const void *a,const void *b)
{
	struct vote *a_vote,*b_vote;
	int res;

	a_vote = (struct vote *)a;
	b_vote = (struct vote *)b;

	if ((res = compare_int(a_vote->batch_number,
			       b_vote->batch_number)))
		return res;
	if ((res = compare_int(a_vote->paper_version,
			       b_vote->paper_version)))
		return res;

	if ((res = strcmp(a_vote->preference_list,
			  b_vote->preference_list)))
		return res;
	
	return 0;
}

/*
  Load the votes from the 2 databases for comparison
*/
static unsigned int get_votes_from_db(void)
{
	PGconn *conn;
	PGresult *result1, *result2;
	unsigned int num_rows, num_rows1=0,num_rows2=0,i;
	struct electorate *electorates;
	struct electorate *current_electorate;
	
	/* get electorate list from evacs*/
	conn=connect_db(DATABASE_NAME);
	electorates=get_electorates(conn);
	if (!electorates) bailout("No Electorates found in %s\n",DATABASE_NAME);
	PQfinish(conn);
	
	conn = connect_db(LOAD1DB_NAME);	
	
	for (current_electorate=electorates;
	     current_electorate;
	     current_electorate=current_electorate->next) {
		
		/* Fill out list of votes from table1 */
		result1 = SQL_query(conn,
				    "SELECT batch_number,paper_version,"
				    "time_stamp,preference_list "
				    "FROM %s_confirmed_vote "
				    "ORDER BY preference_list;",
				    current_electorate->name);
		
		num_rows = PQntuples(result1);

		/* (re)allocate memory for table 1 votes */
		if (!table1_votes)
			table1_votes= malloc(sizeof(*table1_votes) +
					     sizeof(table1_votes->vote[0])*num_rows);
		
		else
			table1_votes = realloc(table1_votes,sizeof(*table1_votes) +
					       sizeof(table1_votes->vote[0])*(num_rows1+num_rows));
		
		for (i=0; i<num_rows; i++) {
			table1_votes->vote[i+num_rows1].batch_number 
				= atoi(PQgetvalue(result1, i, 0));
			table1_votes->vote[i+num_rows1].paper_version 
				= atoi(PQgetvalue(result1,i,1));
			table1_votes->vote[i+num_rows1].timestamp
				= malloc(sizeof(char) * (strlen(PQgetvalue(result1,i,2))+1));
			strcpy(table1_votes->vote[i+num_rows1].timestamp,
				(char *)PQgetvalue(result1,i,2));
			table1_votes->vote[i+num_rows1].preference_list 
				=malloc(sizeof(char ) * (strlen(PQgetvalue(result1,i,3))+1));
			strcpy(table1_votes->vote[i+num_rows1].preference_list,
				(char *)PQgetvalue(result1,i,3));
		

		}
		
		PQclear(result1);
		num_rows1 += num_rows;
			
	}
	PQfinish(conn);
	
	conn = connect_db(LOAD2DB_NAME);	
	
	for (current_electorate=electorates;
	     current_electorate;
	     current_electorate=current_electorate->next) {
		
		
		result2 = SQL_query(conn,
				    "SELECT batch_number,paper_version,"
				    "time_stamp,preference_list "
				    "FROM %s_confirmed_vote "
				    "ORDER BY preference_list;",
				    current_electorate->name);
		
		/* Fill out list of votes from table2 */
		num_rows = PQntuples(result2);
		
				
		/* (re)allocate memory for table 2 votes */
		if (!table2_votes)
			table2_votes= malloc(sizeof(*table2_votes) +
					     sizeof(table2_votes->vote[0])*num_rows);
		
		else
			table2_votes = realloc(table2_votes,sizeof(*table2_votes) +
					       sizeof(table2_votes->vote[0])*(num_rows+num_rows2));
		
		
		for (i=0; i<num_rows; i++) {
			table2_votes->vote[i+num_rows2].batch_number 
				= atoi(PQgetvalue(result2, i, 0));
			table2_votes->vote[i+num_rows2].paper_version 
				= atoi(PQgetvalue(result2,i,1));
			table2_votes->vote[i+num_rows2].timestamp
				= malloc(sizeof(char) * strlen(PQgetvalue(result2,i,2))+1);
			strcpy(table2_votes->vote[i+num_rows2].timestamp,
				PQgetvalue(result2,i,2));
			table2_votes->vote[i+num_rows2].preference_list 
				=malloc(sizeof(char ) * strlen(PQgetvalue(result2,i,3))+1);
			strcpy(table2_votes->vote[i+num_rows2].preference_list,
				PQgetvalue(result2,i,3));
		}
		num_rows2 += num_rows;
		PQclear(result2);
	}
	PQfinish(conn);
	
	/* If different number of rows - may as well pull out now */
	if ( num_rows1 != num_rows2 ) {
		free(table1_votes);
		free(table2_votes);
		return 0;
	}

	/* Sort the first table */
	qsort(&table1_votes->vote[0],num_rows1,sizeof(table1_votes->vote[0]),
	      cmp_votes);
	
	/* Sort the second table */
	qsort(&table2_votes->vote[0],num_rows1,sizeof(table2_votes->vote[0]),
	      cmp_votes);
	
	
	return num_rows2;
}

/* DDS3.4: Check Votes */
bool check_votes (void)
{
	bool equal=false;
	unsigned int number_of_votes, i;

	number_of_votes = get_votes_from_db();
	
	for (i=0; i<number_of_votes; i++) {
		equal = compare_votes(&table1_votes->vote[i], 
				      &table2_votes->vote[i]);


		if (!equal)
			break;
	}

	if (table1_votes != NULL)
		free(table1_votes);
	if (table2_votes != NULL)
		free(table2_votes);

	if (!equal) {
		printf("Second Disk is not in agreement with "
		       "the First. Please start again.\n");
		return false;
	}
	return true;
}
