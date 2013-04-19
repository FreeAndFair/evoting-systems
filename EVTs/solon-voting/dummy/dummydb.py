"""solon/dummy/dummydb.py: Store stuff into a PostgreSQL backend"""
"""
    Copyright 2012, Henrik Ingo

    This file is part of Solon Voting.

    Solon is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Solon is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Solon.  If not, see <http://www.gnu.org/licenses/>.
"""

import psycopg2
import psycopg2.extras
import pickle
import pprint
# TODO: This should happen automatically when importing just connectorapi
from connectors.lqfb.lqfbdb import *

class DummyDB:
  """Store stuff into a PostgreSQL backend."""
  conn = None
  
  def __init__(self, host='localhost', port=5432, dbname='solon_dummy', user='www-data', password='password') :
    self.conn = psycopg2.connect("host=%s port=%s dbname=%s user=%s password=%s" % (host, port, dbname, user, password) )

  def _cursor(self) :
    return self.conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)

  def insertIssuesForVoting(self, issues) :
    cur = self._cursor()
    sql = "INSERT INTO issues (id, data, state) VALUES (%s, %s, %s)"
    # insert each issue as a separate db record
    for issue in issues.getIssues() :        
      cur.execute(sql, [issue['issue']['id'], pickle.dumps(issue), 'voting'])
    # Also save the highest event id (from where we will continue with the next poll
    # This is my Pg version of REPLACE INTO
    sql = "DELETE FROM last_event_id WHERE state=%s"
    cur.execute(sql, ['voting'])
    sql = "INSERT INTO last_event_id (id, state) VALUES (%s, %s)"
    cur.execute(sql, [issues.getLastEventId(), 'voting'])
    self.conn.commit()
    cur.close()    

  def insertPublicVotes(self, votes, last_event_id) :
    cur = self._cursor()
    sql = "INSERT INTO public_votes (issue_id, initiative_id, member_id, grade) VALUES (%s, %s, %s, %s)"
    # iterate over issues over members over initiatives to insert the grade
    for issue in votes :
      issue_id = issue['issue_id']
      for (member_id, vote) in issue['votes'].items() :
        for (initiative_id, grade) in vote.items() :
          cur.execute( sql, [ issue_id, initiative_id, member_id, grade ] )
    # Also save the highest event id (from where we will continue with the next poll)
    sql = "DELETE FROM last_event_id WHERE state=%s"
    cur.execute(sql, ['public_voting_closed'])
    sql = "INSERT INTO last_event_id (id, state) VALUES (%s, %s)"
    cur.execute(sql, [last_event_id, 'public_voting_closed'])
    self.conn.commit()
    cur.close()    

  def setPrivateVotingClosed(self, issue_id_list, last_event_id) :
    cur = self._cursor()
    sql = "UPDATE issues SET state='private_voting_closed' WHERE id=%s"
    for i in issue_id_list :        
      cur.execute( sql, [ i ] )
    # Also save the highest event id (from where we will continue with the next poll)
    sql = "DELETE FROM last_event_id WHERE state=%s"
    cur.execute(sql, ['private_voting_closed'])
    sql = "INSERT INTO last_event_id (id, state) VALUES (%s, %s)"
    cur.execute(sql, [last_event_id, 'private_voting_closed'])
    self.conn.commit()
    cur.close()    

  def getPrivateVotingResults(self) :
    cur = self._cursor()
    sql = """SELECT issue_id, winning_initiative_id, losing_initiative_id, count
             FROM battle_view
             JOIN issues
             ON battle_view.issue_id = issues.id
             WHERE issues.state='private_voting_closed'
          """
    cur.execute(sql)
    battle_list = cur.fetchall()
    sql = """SELECT issue_id, count(DISTINCT member_id) "count"
             FROM all_private_votes_outcome
             JOIN issues
             ON all_private_votes_outcome.issue_id = issues.id
             WHERE issues.state='private_voting_closed'
             GROUP BY issue_id;
          """
    cur.execute(sql)
    voter_count_map = {}
    res = cur.fetchall()
    for row in res :
      voter_count_map[ row['issue_id'] ] = row['count']
    self.conn.commit()
    cur.close()
    return (battle_list, voter_count_map)
  
  def setClosed(self, battle_list) :
    """Set issue state to closed for issues that appear in battle_list. 
       Note: for convenience we allow to push battle_list as returned by 
       getPrivateVotingResults(). The id's are found as 
       battle_list[n]['issue_id']. Also note that same id is repeated many times,
       this is harmless and we ignore it."""
    cur = self._cursor()
    sql = "UPDATE issues SET state='closed' WHERE id=%s"
    for row in battle_list :
      cur.execute(sql, [ row['issue_id'] ] )
    self.conn.commit()
    cur.close()
  
  def getLastEventId(self, state=None) :
    """Get the last event id as stored for given state.
    
       This is used to know the starting point of where to poll for new events
       from LQFB. Retrieving already processed events a 2nd time will result in errors.
       
       return -- the event id stored in database, or 0 if none was found.
    """
    cur = self._cursor()
    if state :
      sql = "SELECT id FROM last_event_id WHERE state=%s"
      cur.execute(sql, [state])
    else :
      sql = "SELECT MAX(id) AS id FROM last_event_id"
      cur.execute(sql)
    row = cur.fetchone()
    self.conn.commit()
    cur.close()
    if row :
      return row['id']
    else :
      return 0
    

  def listIssues(self, state=None, limit=1000, offset=0) :
    """Get all issues in the given state (e.g. 'voting', 'closed'), but without initiatives.
    
       return -- Issues object with the list of Issue objects
    """
    issues = []
    cur = self._cursor()
    if state :
      sql = "SELECT data, state FROM issues WHERE state=%s ORDER BY id LIMIT %s OFFSET %s"
      cur.execute(sql, [state, limit, offset])
    else :
      sql = "SELECT data, state FROM issues ORDER BY id LIMIT %s OFFSET %s"
      cur.execute(sql, [limit, offset])
    for row in cur :
      issues.append( pickle.loads(row['data']) )
      issues[len(issues)-1]['state'] = row['state']
    self.conn.commit()
    cur.close()
    return Issues(issues)
    
  def getIssue(self, id) :
    """Get issue given by id, including its initiatives"""
    cur = self._cursor()
    sql = "SELECT * FROM issues WHERE id=%s"
    cur.execute(sql, id)
    row = cur.fetchone()
    self.conn.commit()
    cur.close()
    if row :
      issue = pickle.loads(row['data']) 
      issue['state'] = row['state']
      return Issue( issue )
    else :
      return None

  def saveVote(self, user_id, issue_id, ballot, vote_type='direct') :
    cur = self._cursor()
    # If user already voted, this vote replaces the old one
    sql = "DELETE FROM direct_private_votes WHERE issue_id=%s AND member_id=%s"
    cur.execute(sql, [issue_id, user_id] )
    sql = "DELETE FROM delegated_private_votes WHERE issue_id=%s AND member_id=%s"
    cur.execute(sql, [issue_id, user_id] )
    if vote_type == 'direct' :
      # ballot contains a dictionary of scores
      for (k, v) in ballot.items() :
        sql = "INSERT INTO direct_private_votes (issue_id, initiative_id, member_id, grade) VALUES (%s, %s, %s, %s)"
        cur.execute(sql, [issue_id, k, user_id, v] )
    if vote_type == 'delegated' :
      # ballot contains the trustee_member_id
      sql = "INSERT INTO delegated_private_votes (issue_id, member_id, trustee_member_id) VALUES (%s, %s, %s)"
      cur.execute(sql, [issue_id, user_id, ballot] )
    self.conn.commit()
    cur.close()