try:
    import psycopg2 as DB
    DatabaseError = DB.DatabaseError
except ImportError:
    DatabaseError = Exception
    pass

import pdb
class NullDB(object):
    def __init__(self, *_):
        pass
    def close(self):
        pass
    def insert(self, _):
        pass

create_ballots_table = """
create table ballots (
                ballot_id serial PRIMARY KEY,
                processed_at timestamp,
                code_string varchar(80),
                layout_code bigint,
                file1 varchar(80),
                file2 varchar(80),
		precinct varchar(80)
               );
"""
create_voteops_table = """
create table voteops (
       voteop_id serial PRIMARY KEY,
       ballot_id int REFERENCES ballots (ballot_id),
       contest_text varchar(80),
       choice_text varchar(80),
       original_x smallint,
       original_y smallint,
       adjusted_x smallint,
       adjusted_y smallint,
       red_mean_intensity smallint,
       red_darkest_pixels smallint,
       red_darkish_pixels smallint,
       red_lightish_pixels smallint,
       red_lightest_pixels smallint,
       green_mean_intensity smallint,
       green_darkest_pixels smallint,
       green_darkish_pixels smallint,
       green_lightish_pixels smallint,
       green_lightest_pixels smallint,
       blue_mean_intensity smallint,
       blue_darkest_pixels smallint,
       blue_darkish_pixels smallint,
       blue_lightish_pixels smallint,
       blue_lightest_pixels smallint,
       was_voted boolean,
       image bytea,
       h_span smallint,
       v_span smallint,
       suspicious boolean default False,
       overvoted boolean default False,
       filename varchar(80),
       contest_text_id smallint default -1,
       contest_text_standardized_id smallint default -1,
       choice_text_id smallint default -1,
       choice_text_standardized_id smallint default -1

);
"""
create_voteops_filename_index = """create index voteops_filename_index on voteops (filename);"""


class PostgresDB(object):
    def __init__(self, database, user):
        try:
            self.conn = DB.connect(database=database, user=user)
        except Exception, e:
            # try to connect to user's default database
            try:
                self.conn = DB.connect(database=user, user=user)
            except Exception, e:
                print "Could not connect to database %s specified in tevs.cfg,\nor connect to default database %s for user %s \nin order to create and initialize new database %s" % (database,user,user,database) 
                print "Do you have permission to create new databases?"
                print e
            # try to create new database, close, and reconnect to new database
            try:
                # create database requires autocommit (cannot be in transaction)
                # if this fails, use shell cmd to psql to create db and tables
                # !!! WARNING, autocommit requires version 2.4.2 of psycopg2, 
                # not in Ubuntu 10.4.
                # must build and set symbolic link from pyshared 
                # to build/lib2.6/psycopg2
                # as Ubuntu may do something weird with python installations
                self.conn.autocommit = True
                # try to create new database
                self.query_no_returned_values(
                    "create database %s" % (database,) )
                self.conn.close()
                # exit on failure, reconnect to new on success
                self.conn = DB.connect(database=database, user=user)
            except Exception, e:
                print "Could not create or connect to database %s." % (database,)
                print "Does your version of python psycopg2 include autocommit?"
                print e
            try:
                self.query_no_returned_values(create_ballots_table)
                self.query_no_returned_values(create_voteops_table)
                self.query_no_returned_values(create_voteops_filename_index)
                # create tables in new database
            except Exception, e:
                print "Could not initialize database %s \nwith ballots and voteops tables, and voteops filename index." % (database,)
                print e

    def close(self):
        try:
            self.conn.close()
        except DatabaseError: 
            pass


    def query_no_returned_values(self, q, *a):
        "returns a list of all results of q parameterized with a"
        cur = self.conn.cursor()
        try:
            cur.execute(q, *a)
            self.conn.commit()
        except DatabaseError, e:
            print e
            pdb.set_trace()
        return 

    def query(self, q, *a):
        "returns a list of all results of q parameterized with a"
        cur = self.conn.cursor()
        cur.execute(q, *a)
        r = list(cur)
        cur.close()
        return r

    def query1(self, q, *a):
        "return one result from q parameterized with a"
        cur = self.conn.cursor()
        cur.execute(q, *a)
        r = cur.fetchone()
        cur.close()
        return r

    def insert(self, ballot):
        #NB all db queries are decalred as strings after the method body for
        #clarity

        #XXX we should not have to chop it off to an arbitary and small length
        if type(ballot.pages[0]) != tuple:
            try:
                search_key = ballot.pages[0].template.barcode
            except TypeError, IndexError:
                search_key = "$".join(p.template.barcode for p in ballot.pages)
                
            name1 = ballot.pages[0].filename
            name2 = "<No such file>"
            if len(ballot.pages) > 1:
                name2 = ballot.pages[1].filename
        else:
            try:
                search_key = ballot.pages[0].template.barcode
            except TypeError, IndexError:
                search_key = "$".join(p[0].template.barcode for p in ballot.pages)
            b = ballot.pages[0]
            name1, name2 = b[0].filename, b[1].filename

        cur = self.conn.cursor()

        # create a record for this ballot

        cur.execute(_pg_mk, (search_key, name1, name2))
        sql_ret = cur.fetchall()

        try:
            ballot_id = int(sql_ret[0][0])
        except ValueError as e:
            self.conn.rollback()
            raise DatabaseError("Corrupt ballot_id")

        # write each result into our record

        for vd in ballot.results:
            try:
                cur.execute(_pg_ins, (
                        ballot_id,
                        vd.contest[:80],
                        vd.choice[:80],

                        vd.coords[0],
                        vd.coords[1],
                        vd.stats.adjusted.x,
                        vd.stats.adjusted.y, 

                        vd.stats.red.intensity,
                        vd.stats.red.darkest_fourth,
                        vd.stats.red.second_fourth,
                        vd.stats.red.third_fourth,
                        vd.stats.red.lightest_fourth,

                        vd.stats.green.intensity,
                        vd.stats.green.darkest_fourth,
                        vd.stats.green.second_fourth,
                        vd.stats.green.third_fourth,
                        vd.stats.green.lightest_fourth,

                        vd.stats.blue.intensity,
                        vd.stats.blue.darkest_fourth,
                        vd.stats.blue.second_fourth,
                        vd.stats.blue.third_fourth,
                        vd.stats.blue.lightest_fourth,

                        vd.was_voted, 
                        vd.ambiguous,
                        vd.filename
                    )
                )
            except:
                self.conn.rollback()
                raise


        self.conn.commit()

_pg_mk = """INSERT INTO ballots (
            processed_at, 
            code_string, 
            file1,
            file2
        ) VALUES (now(), %s, %s, %s) RETURNING ballot_id ;"""

_pg_ins = """INSERT INTO voteops (
            ballot_id,
            contest_text,
            choice_text,

            original_x,
            original_y,
            adjusted_x,
            adjusted_y,

            red_mean_intensity,
            red_darkest_pixels,
            red_darkish_pixels,
            red_lightish_pixels,
            red_lightest_pixels,

            green_mean_intensity,
            green_darkest_pixels,
            green_darkish_pixels,
            green_lightish_pixels,
            green_lightest_pixels,

            blue_mean_intensity,
            blue_darkest_pixels,
            blue_darkish_pixels,
            blue_lightish_pixels,
            blue_lightest_pixels,

            was_voted, 
            suspicious,
            filename
        ) VALUES (
            %s, %s, %s,  
            %s, %s, %s, %s,
            %s, %s, %s, %s, %s, 
            %s, %s, %s, %s, %s, 
            %s, %s, %s, %s, %s, 
            %s, 
            %s, 
            %s
        )"""
