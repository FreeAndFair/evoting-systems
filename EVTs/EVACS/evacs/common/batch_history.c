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

/* This file contains implementation of batch functionality*/

#include "batch_history.h" 

/* corresponding operation descriptions */
static char *batch_op_string[] = {
	(char *)"Entry",
	(char *)"Edit",
	(char *)"Delete",
	(char *)"Destroy",
	(char *)"Append",
	(char *)"Size",
	(char *)"Approve",
	(char *)"Commit",
	(char *)"Active",
	(char *)"Insert"
};


static char *get_batch_op_string(enum batch_op opcode);
static char *get_batch_op_string(enum batch_op opcode) {
	return batch_op_string[opcode];
}

static char *generate_description(PGconn *conn, unsigned int batch_number, 
				  enum batch_op opcode, int data1, int data2);
static char *generate_description(PGconn *conn, unsigned int batch_number, 
				  enum batch_op opcode, int data1, int data2) 
{
	char *description=NULL;
	
	switch(opcode) {
	case ENTRY:
		description = sprintf_malloc(
			" %u nominal:%u actual:%u",data1,
			get_batch_size(conn,batch_number),data2);
		break;
	case EDIT:
		description = sprintf_malloc(
			" paper %u, entry %u",data1,data2);
		break;
	case DELETE:
		description = sprintf_malloc(
			" from paper %u, entry %u",data1, data2);		
		break;
	case DESTROY:
		description = sprintf_malloc(
			" paper %u, entry %u",data1, data2);		
		break;
	case APPEND:
		description = sprintf_malloc(
			" at paper %u, entry %u",data1, data2);
		break;
	case SIZE:
		description = sprintf_malloc(
			": %u to %u",data1, data2);
		break;
	case APPROVE:
		description = sprintf_malloc(
			" paper %u: %s",data1, get_error_string(data2));
		break;
	case COMMIT:
		if (data1 != 0) description = sprintf_malloc(
			"Failed: paper %u %s",data1,get_error_string(data2));
		else description = sprintf_malloc("Succeeded");
		break;
	case ACTIVE:
		description = sprintf_malloc(
			" entry for paper %u = entry %u",data1, data2);
		break;
	case INSERT:
		description = sprintf_malloc(
			" entry for paper %u, entry %u", data1, data2);
                break;
		
	}

	return description;
}


void report_batch_history(PGconn *conn,
			  unsigned int batch_number)
{
	PGresult *result;
	unsigned int num_rows,i;
	enum batch_op opcode;
	int data1, data2;
	char *timestamp, *operator_id, *polling_place_name, *electorate_name;
	char *description;
	FILE *fp;
	char tmpfile[]="/tmp/batch_history_XXXXXX";

        /* check batch exists; get ename and ppname while we're at it */
	result = SQL_query(conn,
			   "SELECT e.name, p.name "
			   "FROM batch b, polling_place p, electorate e "
			   "WHERE b.number = %u "
			   "AND b.electorate_code = e.code "
			   "AND b.polling_place_code = p.code;",
			   batch_number );
	
	num_rows = PQntuples(result);
	
	if (num_rows < 1)
	{
		fprintf(stderr, "No record of batch %u\n",batch_number);
		return;
	}
	
	/* get names */
	electorate_name=sprintf_malloc("%s",PQgetvalue(result,0,0));
	polling_place_name=sprintf_malloc("%s",PQgetvalue(result,0,1));
	
	PQclear(result);
	
	/* retrieve batch history */
	result = SQL_query(conn,
			   "SELECT time_stamp, operator_id, "
			   "op_code, data1, data2 "
			   "FROM batch_history "
			   "WHERE batch_number = %u"
			   "ORDER BY time_stamp;",
			   batch_number );
	
	num_rows = PQntuples(result);
	
        /* open temporary file */
	mkstemp(tmpfile);
	fp = fopen(tmpfile,"w");
	
	if (!fp) {
		fprintf(stderr, "Can't open '%s' for writing\n",&tmpfile[0]);
		return;
	}
	
	print_report_heading(fp);
	
	fprintf(fp,
		"History of %s batch %u (%s)\n\n"
		"\tTimeStamp\tOperator Description\n"
		"\t---------\t-------- --------------------------------------\n\n",
		electorate_name, batch_number, polling_place_name);
	
	for (i=0; i< num_rows; i++)
	{
		timestamp=sprintf_malloc("%s",PQgetvalue(result,i,0));
		operator_id=sprintf_malloc("%s",PQgetvalue(result,i,1));
		opcode=(enum batch_op) atoi(PQgetvalue(result,i,2));
		data1= atoi(PQgetvalue(result,i,3));
		data2= atoi(PQgetvalue(result,i,4));

		description = generate_description(conn,batch_number,opcode,data1,data2);
		fprintf(fp,
			"%s\t%s\t%s %s\n",
			timestamp,operator_id,
			get_batch_op_string(opcode),
			description
			);

		free(timestamp);
		free(operator_id);
		free(description);
		
	}
	
	PQclear(result);
	fclose(fp);
	printfile(tmpfile);
	printf("\nHistory of %s batch %u printed.\n",electorate_name,batch_number);
	
}


