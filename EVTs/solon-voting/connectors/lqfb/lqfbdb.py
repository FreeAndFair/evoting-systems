"""solon/connectors/lqfb/lgfbdb.py: Interact with a Liquid Feedback PostgreSQL database

This class extracts from LQFB:
 - Issues and their initiatives to be voted on
 - Information on eligible voters
and inserts back
 - Results of each vote
 
We poll for new issues periodically from the events table. Note that logically
the call sequence is such that LQFB triggers the start of voting that happens
in Solon, but in practice it has been implemented such that Solon polls LQFB,
pulls issues and pushes back voting results.

Similarly, Solon is a slave to LQFB in the sense that event id, issue id and other
id are specified by LQFB and we use the same ids in Solon.

The big idea is to move around data as python data structures (lists of 
dictionaries). This includes storing to the database: we serialize to a BLOB.
However, to get a best of both worlds approach, we do use the wrapper classes
Issues() and Issue() to operate on these data structures. Still, the primary
format for keeping the data is the dictionary-list, without the wrapper classes.
"""
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
import pprint
import datetime
import crypt
import json


class LqfbDB:
  """Connect to and operate on a LQFB PostgreSQL database."""
  conn = None
  
  def connect(self, host='localhost', port=5432, dbname='liquid_feedback', user='www-data', password='password') :
    self.conn = psycopg2.connect("host=%s port=%s dbname=%s user=%s password=%s" % (host, port, dbname, user, password) )

  def _cursor(self):
    return self.conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)

  def getIssuesForVoting(self, last_event_id) :
    conn = self.conn
    issues = []
    #cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
    cur = self._cursor()
    sql = """SELECT event.id as event_id, issue.id, issue.*
             FROM event 
             JOIN issue ON event.issue_id = issue.id 
             WHERE event.id > %s AND event.state='voting' 
             ORDER BY event.id"""
    cur.execute(sql, [last_event_id])
    res = cur.fetchall()
    # if there are new issues in the result set, we need to also fetch the related initiatives
    # A loop is not 100% optimal but readability of code is nice too (but we could have fetched all in one sql statement)
    for issue in res :
      sql = """SELECT current_draft.id AS draft_id, current_draft.*, initiative.*, initiative.id AS id, member.name as author_name
              FROM initiative 
              JOIN current_draft ON initiative.id = current_draft.initiative_id 
              JOIN member ON member.id = current_draft.author_id
              WHERE initiative.issue_id=%s and initiative.admitted=true
              ORDER BY initiative.id
            """
      cur.execute( sql, [ issue['id'] ] )
      initiatives = cur.fetchall()
      sql = "SELECT * FROM area WHERE id = %s"
      cur.execute( sql, [ issue['area_id'] ] )
      area = cur.fetchone()
      sql = "SELECT * FROM unit WHERE id = %s"
      cur.execute( sql, [ area['unit_id'] ] )
      unit = cur.fetchone()
      sql = "SELECT * FROM policy WHERE id = %s"
      cur.execute( sql, [ issue['policy_id'] ] )
      policy = cur.fetchone()
      issues.append( {'issue' : issue, 'initiatives' : initiatives, 'area' : area, 'unit' : unit, 'policy' : policy } )
    conn.commit()
    cur.close()
    # Something in the result set dictionary can't be pickled:
    #       TypeError: a class that defines __slots__ without defining __getstate__ cannot be pickled
    # We cleanse it by copying item for item to a new list/dictionary.
    issues = _copyIssues(issues)
    return Issues( issues )

  def getPublicVotes(self, last_event_id) :
    conn = self.conn
    public_votes = []
    cur = self._cursor()
    sql = """SELECT event.id as event_id, issue.id, issue.*
             FROM event 
             JOIN issue ON event.issue_id = issue.id 
             WHERE event.id > %s AND event.state='public_voting_closed' 
             ORDER BY event.id"""
    cur.execute(sql, [last_event_id])
    res = cur.fetchall()
    # For each issue in public_voting_closed, fetch the public delegations. 
    # Delegations form a graph, btw. 
    for issue in res :
      # We need to keep track of the highest event_id seen and return it back to caller
      last_event_id = issue['event_id']
      # Get all direct_voter for issue, plus the grades for the initiatives he voted for
      sql = """SELECT direct_voter.member_id, direct_voter.issue_id, vote.initiative_id, vote.grade 
               FROM direct_voter 
               JOIN vote ON direct_voter.issue_id = vote.issue_id AND direct_voter.member_id = vote.member_id
               WHERE direct_voter.issue_id = %s
               ORDER BY direct_voter.member_id, vote.initiative_id
            """
      cur.execute( sql, [issue['id']] )
      res = cur.fetchall()
      # Build a dictionary to lookup (issue_id -> ) member_id -> initiative_id
      votes = {}
      for row in res :
        # If this is the first vote for member_id, 
        # we need to create the empty dictionary for the next step, to avoid error.
        try :
          votes[ row['member_id'] ]
        except :
          votes[ row['member_id'] ] = {}
        votes[ row['member_id'] ][ row['initiative_id'] ] = row['grade']
        
      # Get all delegating_voter for issue
      sql = """SELECT member_id, issue_id, delegate_member_ids
               FROM delegating_voter
               WHERE issue_id = %s
               ORDER BY member_id
            """
      cur.execute( sql, [issue['id']] )
      res = cur.fetchall()
      # Merge delegating_voter into the votes dictionary, and copy the votes
      # from the direct_voter that is at the end of delegation chain.
      # We don't need to know the delegation chains, we just need to lookup
      # actual voting result for each member_id that did a public vote at all
      for row in res :
        votes[ row['member_id'] ] = votes[ row['delegate_member_ids'][-1] ]
      public_votes.append( {'issue_id' : issue['id'], 'votes' : votes } )
    conn.commit()
    cur.close()
    return (public_votes, last_event_id)

  def getIssuesToCalculate(self, last_event_id) :
    conn = self.conn
    issue_id_list = []
    cur = self._cursor()
    sql = """SELECT id as event_id, issue_id
             FROM event 
             WHERE id > %s AND event.state='private_voting_closed' 
             ORDER BY id"""
    cur.execute(sql, [last_event_id])
    res = cur.fetchall()
    # We simply need to return the list of issue_id's, plus the new last_event_id
    for issue in res :
      last_event_id = issue['event_id']
      issue_id_list.append( issue['issue_id'] )
    conn.commit()
    cur.close()
    return (issue_id_list, last_event_id)
    
  def returnResults(self, battle_list, voter_count_map) :
    """Return results to LQFB battle table and also call ext_results_available()"""
    cur = self._cursor()
    unique_ids_only = {}
    # Start with deleting possible old results with same issue_id
    sql = "DELETE FROM battle WHERE issue_id = %s"
    for row in battle_list :
      cur.execute(sql, [ row['issue_id'] ] )
    # Then insert results to lqfb
    sql = """INSERT INTO battle (
             issue_id, winning_initiative_id, 
             losing_initiative_id, count )
             VALUES
             (%s, %s, %s, %s)
          """
    for row in battle_list :
      cur.execute(sql, [ row['issue_id'], row['winning_initiative_id'], row['losing_initiative_id'], row['count'] ] )
      unique_ids_only[ row['issue_id'] ] = True
    # Also must set voter_count for each issue
    sql = """UPDATE issue SET voter_count=%s WHERE id=%s"""
    for id in unique_ids_only.keys() :
      cur.execute(sql, [ voter_count_map[id], id ] )
    # Call procedure that tells LQFB that results are available and Schulze ranking can start
    for id in unique_ids_only.keys() :
      cur.callproc("ext_results_available", [id] )
    self.conn.commit()
    cur.close()
    return True
    
  def userAuthentication(self, username, password='') :
    """If successful, returns LQFB user id, otherwise False."""
    conn = self.conn
    #cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
    cur = self._cursor()
    sql = "SELECT password, id FROM member WHERE login=%s LIMIT 1"
    cur.execute(sql, [username])
    row = cur.fetchone()
    cur.close()
    if row == None :
      return False 
    cryptedpass = row['password']
    if crypt.crypt(password, cryptedpass) == cryptedpass :
      return row['id']
    else :
      return False

  def userAuthorization(self, user_id, unit_id) :
    """Returns True if user_id has privilege.voting_right for unit_id, otherwise False"""
    conn = self.conn
    #cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
    cur = self._cursor()
    sql = "SELECT voting_right FROM privilege WHERE member_id=%s AND unit_id=%s"
    cur.execute(sql, [user_id, unit_id])
    row = cur.fetchone()
    conn.commit()
    cur.close()
    if row == None :
      return False 
    return row['voting_right']
  
  def getUserId(self, key, key_type):
    """Get user id by searching the "key_type" column for "key"."""
    conn = self.conn
    #cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
    cur = self._cursor()
    sql = "SELECT id FROM member WHERE " + key_type + "=%s LIMIT 1"
    cur.execute(sql, [key])
    row = cur.fetchone()
    conn.commit()
    cur.close()
    if row == None :
      return False 
    else :
      return row['id']
    
      
    
      
#TODO: use deepcopy      
def _copyIssues(issues) :
  """Deep copy of the issues array. Unlike dict.copy(), this function traverses all levels of issues and makes a copy."""
  # TODO: This can probably be done more generic by using deepcopy module. (Sorry, I don't know python...)
  newlist = []
  for issue in issues :
    newissue = { 'issue' : {}, 'area' : {}, 'unit' : {}, 'policy' : {} }
    for (k, v) in issue['issue'].items() :
      newissue['issue'][k] = v
    for (k, v) in issue['area'].items() :
      newissue['area'][k] = v
    for (k, v) in issue['unit'].items() :
      newissue['unit'][k] = v
    for (k, v) in issue['policy'].items() :
      newissue['policy'][k] = v
    # Sometimes there are no initiatives. Stop here to avoid KeyError.
    if not 'initiatives' in issue : 
      newlist.append(newissue)
      continue
    else :
      newissue['initiatives'] = []
    for initiative in issue['initiatives'] :
      newinit = {}
      for (k, v) in initiative.items() :
        newinit[k] = v
      newissue['initiatives'].append(newinit)
    newlist.append(newissue)
  return newlist

    

class Issues :
  """Wrapper around a dictionary with issues, initiatives and drafts.

  We mostly just push around LQFB issues as a python dictionary, but it's 
  encapsulated into this simple wrapper class so we can provide a few convenience
  accessors.

  Note that issue data is read-only towards LQFB, we never write back any changes.
  """
  issues = None
  
  def __init__(self, issues=None) :
    self.issues = issues

  def getIssues(self) :
    return self.issues

  def getIssue(self, i) :
    """Returns the dictionary {'issue' : issue, 'initiatives' : initiatives }."""
    return Issue(self.issues[i])

  def getIssueObject(self, i) :
    """Returns the dictionary {'issue' : issue, 'initiatives' : initiatives } wrapped in an Issue() object."""
    return Issue(self.issues[i])

  def getLastEventId(self) :
    """Get last event id of the list stored in this object.
    
       It is an error to call this function when the list is empty. See
       Issues.isEmpty()
    """
    return self.issues[len(self.issues)-1]['issue']['event_id']

  def isEmpty(self) :
    if self.issues :
      return False
    else :
      return True
  
  def copy(self) :
    newlist = []
    for issue in self.issues :
      i = Issue(issue).copy().issue
      newlist.append(i)
    return Issues(newlist)


  def json(self) :
    """Dump the list of issues as json, discarding the wrapper object
    
       This method will make a copy of the issues list, transform datetime
       and timedelta types into strings, and then return all this as JSON.
    """
    issues = self.copy().issues
    for issue in issues :
      i = Issue(issue)
      i._jsonPrepare()
    return json.dumps(issues, sort_keys=True, indent=4)
    
    
    
    
class Issue :
  """Wrapper around a single issue + initiatives."""
  issue = None
  def __init__(self, issue) :
    self.issue = issue

  def getIssue(self) :
    return self.issue
    
  def getIssueRecord(self) :
    return self.issue['issue']

  def getInitiatives(self) :
    return self.issue['initiatives']
    
  def getId(self) :
    return self.issue['issue'][1]
  
  def getEventId(self) :
    return self.issue['issue'][0]
        
  def getState(self) :
    return self.issue['issue'][4]
  
  def getInitiativeReverseLookupMap(self) :
    """Return the a map you can use for reverse lookups to get the array index that holds a given issue['initiatives'][index]['id']."""
    m = {}
    i = 0
    for ini in self.issue['initiatives'] :
      m[ ini['id'] ] = i
      i = i + 1
    return m
  
  def deleteInitiatives(self) :
    del( self.issue['initiatives'] )

  def copy(self) :
    # We have this handy function to copy a list of issues, so we can use it 
    # for a single issue too.
    return Issue( _copyIssues( [self.issue] )[0] )
  
  def json(self) :
    """Dump the wrapped array as json, without the wrapper object."""
    i = self.copy()
    i._jsonPrepare()
    return json.dumps(i.issue, sort_keys=True, indent=4)
    
  def _jsonPrepare(self) :
    """Convert datetime and timedelta types to strings, so they can be serialized into json."""
    issue = self.issue
    for h in ['issue', 'area', 'unit', 'policy'] :
      for (k, v) in issue[h].items() :
        # print str( type(v) ) + "\n"
        if type(v) == datetime.datetime :
          issue[h][k] = v.isoformat() # TODO: I wonder if I should use v.ctime() instead? What does JavaScript support better?
        if type(v) == datetime.timedelta :
          issue[h][k] = str(v)
    # Sometimes there are no initiatives. Stop here to avoid KeyError.
    if not 'initiatives' in issue : 
      return issue
    j = 0
    for initiative in issue['initiatives'] :
      for (k, v) in initiative.items() :
        if type(v) == datetime.datetime :
          issue['initiatives'][j][k] =  v.isoformat() # TODO: I wonder if I should use v.ctime() instead? What does JavaScript support better?
        if type(v) == datetime.timedelta :
          issue['initiatives'][j][k] = str(v)
      j = j + 1
    return issue