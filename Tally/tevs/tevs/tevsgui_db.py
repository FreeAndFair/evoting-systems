import pickle
import sys
try:
    import psycopg2 as DB
    DatabaseError = DB.DatabaseError
except ImportError:
    DatabaseError = Exception
    pass

class PostgresQuery(object):
    def __init__(self, database, user, query, retfile):
        #print "Database",database,"query",query
        self.conn = DB.connect(database=database, user=user)
        cur = self.conn.cursor()
        cur.execute(query)
        self.conn.commit()
        try:
            r = list(cur)
            f = open(retfile,"w")
            pickle.dump(r,f)
            f.close()
            print retfile
        except:
            print "No results."
        self.conn.commit()
        self.conn.close()
        

if __name__ == "__main__":
    if len(sys.argv) == 5:
        try:
            pq = PostgresQuery(sys.argv[1],sys.argv[2],sys.argv[3],sys.argv[4])
        except DB.ProgrammingError, e:
            print e
    sys.exit(0)
