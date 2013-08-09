#ifndef EXPORT_BALLOTS_H
#define EXPORT_BALLOTS_H 


#define PREFNUM_MAX         99

#define DIGITS_PER_PREF      6

#define DATABASE_NAME     "evacs"

#define SERVER_ADDRESS "192.168.1.75"

/* SIPL 2011-09-23 Increased from 3 to 5. */
#define MAX_ELECTORATES      5

/* SIPL 2011-09-23 Increased from 15 to 20. */
#define MAX_GROUPS          20

#define MAX_ELECTORATE_SEATS 7

#define NUM_SUPERVISORS     10
#define NUM_USERS           30

struct electorate
{
	unsigned int code;
	unsigned int num_seats;

	/* SIPL 2011-07-15 To support split groups,
	   the following fields have been copied
	   from common/ballot_contents.h. */

	/* Total number of groups */
	unsigned int num_groups;

	/* Number of candidates in each group */
	unsigned int *num_candidates;

	/* Total number of physical columns.  If no
	   groups are split, this equals num_groups. */
	unsigned int num_physical_columns;

	/* Mapping of group to "physical column".  For example,
	   suppose group 0 occupies two physical columns.  Then
	   map_group_to_physical_column[0] == 0 and
	   map_group_to_physical_column[1] == 2.
	   There is an additional dummy entry at the end for
	   convenience.  For example, if there are 5 groups,
	   and 8 physical columns,
	   map_group_to_physical_column[5] == 8.
	   This dummy value is used in voting_client/main_screen.c
	   and voting_client_stripped/main_screen.c.
	*/
	unsigned int *map_group_to_physical_column;

	/* Number of candidates in each physical column.  If no
	   groups are split, this is an identical copy of
	   num_candidates[]. */
	unsigned int *num_candidates_in_physical_column;

	/* nul-terminated string hangs off end of structure */
	char name[0];
};

struct polling_place
{
	unsigned int code;
	/* nul-terminated string hangs off end of structure */
	char name[0];
};

struct preference
{
	unsigned int prefnum;
	unsigned int group_index;
	unsigned int screen_candidate_index;
	unsigned int db_candidate_index;
};

/* A single ballot paper */
struct preference_set
{
	/* Preferences hang off end. */
        int paper_version;
	int num_preferences;
	struct preference candidates[0];
};


/* One Robson Rotation */
struct rotation
{
	/* Number of rotations which are actually used
	   ( == electorate seat count). */
	unsigned int size;
	unsigned int rotations[MAX_ELECTORATE_SEATS];
};


static void bailout(const char *fmt, ...)
__attribute__((noreturn, format (printf,1,2)));

static char *vsprintf_malloc(const char *fmt,
			     va_list arglist);

/* SIPL 2011: Only define this prototype if required by the including file.
static char *sprintf_malloc(const char *fmt, ...)
__attribute__ ((format(printf,1,2)));
*/
#ifdef DEFINE_SPRINTF_MALLOC
static char *sprintf_malloc(const char *fmt, ...)
__attribute__ ((format(printf,1,2)));
#endif

static PGconn *connect_db_host(const char *name,
			       const char *hostname);

static PGresult *SQL_query(PGconn *conn, const char *fmt, ...)
__attribute__ ((format(printf,2,3)));
/*
static PGresult *run_SQL(PGconn *conn, 
			 bool bail_on_error,
			 const char *fmt,
			 va_list arglist);
*/
/* SIPL 2011: Only define this prototype if required by the including file.
static unsigned int SQL_command(PGconn *conn, 
				const char *fmt, ...)
__attribute__ ((format(printf,2,3)));
*/
#ifdef DEFINE_SQL_COMMAND
static unsigned int SQL_command(PGconn *conn, 
				const char *fmt, ...)
__attribute__ ((format(printf,2,3)));
#endif

/*static int SQL_cmd(PGconn *conn, 
		   bool bail_on_error,
	     const char *fmt,
	     va_list arglist);*/

static char *SQL_single(PGconn *conn,const char *fmt,va_list arglist);

/* SIPL 2011: Only define this prototype if required by the including file.
static char *SQL_singleton(PGconn *conn,const char *fmt, ...)
__attribute__ ((format(printf,2,3)));
*/
#ifdef DEFINE_SQL_SINGLETON
static char *SQL_singleton(PGconn *conn,const char *fmt, ...)
__attribute__ ((format(printf,2,3)));
#endif

/* SIPL 2011: Changed from static to extern to remove warnings.
static struct rotation *fetch_rotation(PGconn *conn,
				unsigned int rotation_num,
				unsigned int seat_count);
*/
extern struct rotation *fetch_rotation(PGconn *conn,
				unsigned int rotation_num,
				unsigned int seat_count);

static void fetch_electorates(PGconn *conn, struct electorate *electorates[0]);

/* SIPL 2011: Changed from static to extern to remove warnings.
static void free_electorates(struct electorate *elec[]);
*/
extern void free_electorates(struct electorate *elec[]);
/* SIPL 2011: Changed from static to extern to remove warnings.
static void write_groups(PGconn *conn, const char *filename);
*/
extern void write_groups(PGconn *conn, const char *filename);

/* SIPL 2011: Changed from static to extern to remove warnings.
static void write_candidates(PGconn *conn, const char *filename, unsigned int num_in_group[0]);
*/
extern void write_candidates(PGconn *conn, const char *filename, unsigned int num_in_group[0]);

/* SIPL 2011: Changed from static to extern to remove warnings.
static struct preference_set *unpack_preferences(const char *preference_list);
*/
extern struct preference_set *unpack_preferences(const char *preference_list);

/* Create a mapping for the rotation, collapsed to this number of
   candidates */
/* SIPL 2011: Only define this prototype if required by the including file.
static void produce_collapsed_map(const struct rotation *rot,
				  unsigned int map[],
				  unsigned int num_candidates);
*/
#ifdef DEFINE_PRODUCE_COLLAPSED_MAP
static void produce_collapsed_map(const struct rotation *rot,
				  unsigned int map[],
				  unsigned int num_candidates);
#endif

/* SIPL 2011: Changed from static to extern to remove warnings.
static unsigned int translate_dbci_to_sci(unsigned int num_candidates,
				   unsigned int db_candidate_index,
				   const struct rotation *rot);
*/
extern unsigned int translate_dbci_to_sci(unsigned int num_candidates,
				   unsigned int db_candidate_index,
				   const struct rotation *rot);


#endif /* EXPORT_BALLOTS_H */


