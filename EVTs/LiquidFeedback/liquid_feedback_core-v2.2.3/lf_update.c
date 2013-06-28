#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <libpq-fe.h>

static char *escapeLiteral(PGconn *conn, const char *str, size_t len) {
  // provides compatibility for PostgreSQL versions prior 9.0
  // in future: return PQescapeLiteral(conn, str, len);
  char *res;
  size_t res_len;
  res = malloc(2*len+3);
  if (!res) return NULL;
  res[0] = '\'';
  res_len = PQescapeStringConn(conn, res+1, str, len, NULL);
  res[res_len+1] = '\'';
  res[res_len+2] = 0;
  return res;
}

static void freemem(void *ptr) {
  // to be used for "escapeLiteral" function
  // provides compatibility for PostgreSQL versions prior 9.0
  // in future: PQfreemem(ptr);
  free(ptr);
}

int main(int argc, char **argv) {

  // variable declarations:
  int err = 0;
  int i, count;
  char *conninfo;
  PGconn *db;
  PGresult *res;

  // parse command line:
  if (argc == 0) return 1;
  if (argc == 1 || !strcmp(argv[1], "-h") || !strcmp(argv[1], "--help")) {
    FILE *out;
    out = argc == 1 ? stderr : stdout;
    fprintf(out, "\n");
    fprintf(out, "Usage: %s <conninfo>\n", argv[0]);
    fprintf(out, "\n");
    fprintf(out, "<conninfo> is specified by PostgreSQL's libpq,\n");
    fprintf(out, "see http://www.postgresql.org/docs/9.1/static/libpq-connect.html\n");
    fprintf(out, "\n");
    fprintf(out, "Example: %s dbname=liquid_feedback\n", argv[0]);
    fprintf(out, "\n");
    return argc == 1 ? 1 : 0;
  }
  {
    size_t len = 0;
    for (i=1; i<argc; i++) len += strlen(argv[i]) + 1;
    conninfo = malloc(len * sizeof(char));
    if (!conninfo) {
      fprintf(stderr, "Error: Could not allocate memory for conninfo string\n");
      return 1;
    }
    conninfo[0] = 0;
    for (i=1; i<argc; i++) {
      if (i>1) strcat(conninfo, " ");
      strcat(conninfo, argv[i]);
    }
  }

  // connect to database:
  db = PQconnectdb(conninfo);
  if (!db) {
    fprintf(stderr, "Error: Could not create database handle\n");
    return 1;
  }
  if (PQstatus(db) != CONNECTION_OK) {
    fprintf(stderr, "Could not open connection:\n%s", PQerrorMessage(db));
    return 1;
  }

  // delete expired sessions:
  res = PQexec(db, "DELETE FROM \"expired_session\"");
  if (!res) {
    fprintf(stderr, "Error in pqlib while sending SQL command deleting expired sessions\n");
    err = 1;
  } else if (
    PQresultStatus(res) != PGRES_COMMAND_OK &&
    PQresultStatus(res) != PGRES_TUPLES_OK
  ) {
    fprintf(stderr, "Error while executing SQL command deleting expired sessions:\n%s", PQresultErrorMessage(res));
    err = 1;
    PQclear(res);
  } else {
    PQclear(res);
  }
 
  // check member activity:
  res = PQexec(db, "SET TRANSACTION ISOLATION LEVEL READ COMMITTED; SELECT \"check_activity\"()");
  if (!res) {
    fprintf(stderr, "Error in pqlib while sending SQL command checking member activity\n");
    err = 1;
  } else if (
    PQresultStatus(res) != PGRES_COMMAND_OK &&
    PQresultStatus(res) != PGRES_TUPLES_OK
  ) {
    fprintf(stderr, "Error while executing SQL command checking member activity:\n%s", PQresultErrorMessage(res));
    err = 1;
    PQclear(res);
  } else {
    PQclear(res);
  }

  // calculate member counts:
  res = PQexec(db, "SET TRANSACTION ISOLATION LEVEL REPEATABLE READ; SELECT \"calculate_member_counts\"()");
  if (!res) {
    fprintf(stderr, "Error in pqlib while sending SQL command calculating member counts\n");
    err = 1;
  } else if (
    PQresultStatus(res) != PGRES_COMMAND_OK &&
    PQresultStatus(res) != PGRES_TUPLES_OK
  ) {
    fprintf(stderr, "Error while executing SQL command calculating member counts:\n%s", PQresultErrorMessage(res));
    err = 1;
    PQclear(res);
  } else {
    PQclear(res);
  }

  // update open issues:
  res = PQexec(db, "SELECT \"id\" FROM \"open_issue\"");
  if (!res) {
    fprintf(stderr, "Error in pqlib while sending SQL command selecting open issues\n");
    err = 1;
  } else if (PQresultStatus(res) != PGRES_TUPLES_OK) {
    fprintf(stderr, "Error while executing SQL command selecting open issues:\n%s", PQresultErrorMessage(res));
    err = 1;
    PQclear(res);
  } else {
    count = PQntuples(res);
    for (i=0; i<count; i++) {
      char *issue_id, *escaped_issue_id;
      PGresult *res2, *old_res2;
      int j;
      issue_id = PQgetvalue(res, i, 0);
      escaped_issue_id = escapeLiteral(db, issue_id, strlen(issue_id));
      if (!escaped_issue_id) {
        fprintf(stderr, "Could not escape literal in memory.\n");
        err = 1;
        break;
      }
      old_res2 = NULL;
      for (j=0; ; j++) {
        if (j >= 20) {  // safety to avoid endless loops
          fprintf(stderr, "Function \"check_issue\"(...) returned non-null value too often.\n");
          err = 1;
          if (j > 0) PQclear(old_res2);
          break;
        }
        if (j == 0) {
          char *cmd;
          if (asprintf(&cmd, "SET TRANSACTION ISOLATION LEVEL REPEATABLE READ; SELECT \"check_issue\"(%s, NULL)", escaped_issue_id) < 0) {
            fprintf(stderr, "Could not prepare query string in memory.\n");
            err = 1;
            break;
          }
          res2 = PQexec(db, cmd);
          free(cmd);
        } else {
          char *persist, *escaped_persist, *cmd;
          persist = PQgetvalue(old_res2, 0, 0);
          escaped_persist = escapeLiteral(db, persist, strlen(persist));
          if (!escaped_persist) {
            fprintf(stderr, "Could not escape literal in memory.\n");
            err = 1;
            PQclear(old_res2);
            break;
          }
          if (asprintf(&cmd, "SET TRANSACTION ISOLATION LEVEL REPEATABLE READ; SELECT \"check_issue\"(%s, %s::\"check_issue_persistence\")", escaped_issue_id, escaped_persist) < 0) {
            freemem(escaped_persist);
            fprintf(stderr, "Could not prepare query string in memory.\n");
            err = 1;
            PQclear(old_res2);
            break;
          }
          freemem(escaped_persist);
          res2 = PQexec(db, cmd);
          free(cmd);
          PQclear(old_res2);
        }
        if (!res2) {
          fprintf(stderr, "Error in pqlib while sending SQL command to call function \"check_issue\"(...):\n");
          err = 1;
          break;
        } else if (
          PQresultStatus(res2) != PGRES_COMMAND_OK &&
          PQresultStatus(res2) != PGRES_TUPLES_OK
        ) {
          fprintf(stderr, "Error while calling SQL function \"check_issue\"(...):\n%s", PQresultErrorMessage(res2));
          err = 1;
          PQclear(res2);
          break;
        } else {
          if (PQntuples(res2) >= 1 && !PQgetisnull(res2, 0, 0)) {
            old_res2 = res2;
          } else {
            PQclear(res2);
            break;
          }
        }
      }
      freemem(escaped_issue_id);
    }
    PQclear(res);
  }

  // cleanup and exit:
  PQfinish(db);
  return err;

}
