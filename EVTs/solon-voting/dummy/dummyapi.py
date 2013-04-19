"""This API provides all the Solon operations, but it's a dummy, it doesn't do any encryption.

   DummyDB is used as a backend. This is a simple PostgreSQL database, and most
   of the time Python structures are pickled and dumped as is (it's called NoSQL).
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

import tornado.ioloop
import tornado.web
import httplib
import traceback
import sys
from dummy.dummydb import DummyDB
from connectors.connectorapi import ImsConnectorFactory
from connectors.lqfb.lqfbdb import LqfbDB
import pprint

from config import conf

def dummyFactory() :
  # TODO: Now only host and password are supported, should support user, port, dbname in conf object too.
  return DummyDB(host=conf['dummydb.host'], password=conf["dummydb.password"])
    
class MyBaseRequestHandler(tornado.web.RequestHandler):
  """Base class currently provides a common error writer"""
  def write_error(self, status_code, **kwargs):
    self.write( "<p>%d: %s</p>" % (status_code, httplib.responses[status_code] )  )
    try:
      (t, e, trace) = kwargs["exc_info"]
      if type( e ) == tornado.web.HTTPError :
        self.write( "<p>" + e.log_message + "</p>" )
      l = traceback.format_exception(t, e, trace)
      self.write( "<pre>" + "".join(l) + "</pre>")
    except:
      traceback.print_exc()

class MainHandler(MyBaseRequestHandler):
  def get(self):
    p = """<h1>Solon Voting 0.01-dev (dummy)</h1>
           <p>Execute periodic tasks (cron): <a href="/cron">html</a></p>
           <p>List issues open for voting: <a href="list.html?state=voting">html</a> <a href="list.json?state=voting">json</a></p>
           <p>Show specific issue: <a href="issue.html?id=1">html</a> <a href="issue.json?id=1">json</a></p>
           <p>Vote on an issue: <a href="vote.html?id=1">html</a></p>
           <p>List issues waiting for calculation: <a href="list.html?state=private_voting_closed">html</a> <a href="list.json?state=private_voting_closed">json</a></p>
           <p>List closed issues: <a href="list.html?state=closed">html</a> <a href="list.json?state=closed">json</a></p>
        """
    self.write("<html><head><title>Solon Voting. 0.01-dev (dummy).</title></head><body>%s</body></html>" % p)
      
      
class ListIssuesJson(MyBaseRequestHandler):
  def get(self):
    dummy = dummyFactory()
    issues = dummy.listIssues(self.get_argument('state'))
    self.write( issues.json() )

class ListIssuesHtml(MyBaseRequestHandler):
  def get(self):
    dummy = dummyFactory()
    state = self.get_argument('state')
    limit = int( self.get_argument('limit', 100) )
    offset = int( self.get_argument('offset', 0) )
    issues = dummy.listIssues(state, limit, offset)
    p = ''
    n = ''
    for i in issues.getIssues() :
      initiatives = ''
      for ini in i['initiatives'] :
        link = "issue.html?id=" + str(i['issue']['id']) + "&initiative=" + str(ini['id'])
        initiatives = initiatives + \
                    """i%s: <a href="%s">%s</a><br />
                    """ % (ini['id'], link, ini['name'] )
                    
      if i['state'] == 'voting' :
        votelink = '&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<a href="vote.html?id=%s">Vote now</a>' % i['issue']['id']
      else :
        votelink = ''

      p = p + """<hr />
                 <p>%s &gt; %s %s<br />
                 <strong>%s: <a href="issue.html?id=%s">%s</a></strong><br />
                 %s
                 </p>
              """ % (i['unit']['name'], i['area']['name'], votelink, i['policy']['name'], i['issue']['id'], i['issue']['id'], initiatives)
      if len( issues.getIssues() ) > limit :
        # There's more
        n = """<small>(%s - %s) <a href="list.html?offset=%s">more &gt;&gt;</a></small><br />""" % ( offset+1, offset+limit, offset+limit )
    s = """<h1>Issues in state '%s'</h1>
           %s
           %s
           %s
        """ % (state, n, p, n)
    self.write( s )

    
class GetIssueJson(MyBaseRequestHandler):
  def get(self):
    dummy = dummyFactory()
    issue = dummy.getIssue(self.get_argument('id'))
    self.write( str( issue.json() ) )

class GetIssueHtml(MyBaseRequestHandler):
  def get(self):
    dummy = dummyFactory()
    issue = dummy.getIssue(self.get_argument('id'))
    m = issue.getInitiativeReverseLookupMap()
    # remove wrapper object
    issue = issue.getIssue()
    p = ''
    initiatives = ''
    for ini in issue['initiatives'] :
      link = "issue.html?id=" + str(issue['issue']['id']) + "&initiative=" + str(ini['id'])
      if int(ini['id']) == int(self.get_argument('initiative', -1)) :
        initiatives = initiatives + \
                    """<strong>i%s: %s</strong><br />
                    """ % (ini['id'], ini['name'] )
      else :
        initiatives = initiatives + \
                    """i%s: <a href="%s">%s</a><br />
                    """ % (ini['id'], link, ini['name'] )

    if issue['state'] == 'voting' :
      votelink = '&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<a href="vote.html?id=%s">Vote now</a>' % issue['issue']['id']
    else :
      votelink = ''
    p = """<p>%s &gt; %s %s<br />
              <strong>%s: %s</strong><br />
              %s
              </p>
              <hr />
        """ % (issue['unit']['name'], issue['area']['name'], votelink, issue['policy']['name'], issue['issue']['id'], initiatives)
    ini = int(self.get_argument('initiative', -1))
    if ini != -1 :
      # Use reverse lookup ini == issue['initiatives'][i]['id']
      i = m[ini]
              # TODO: showing raw RocketWiki code, we should html-escape this
              # ...or we should get the HTML rendered code from Lqfb instead?
      p = p + """<p>
              Author: %s<br />
              Latest draft created at: %s <br />
              <textarea cols="80" rows="20">%s</textarea>
              </p>
              """ % (issue['initiatives'][i]['author_name'], issue['initiatives'][i]['created'], issue['initiatives'][i]['content'] )
    self.write( p )

class VoteHtml(MyBaseRequestHandler):
  def get(self):
    dummy = dummyFactory()
    issue = dummy.getIssue(self.get_argument('id'))
    # remove wrapper object
    issue = issue.getIssue()
    # Check that issue is in voting state
    if not issue['state'] == 'voting' :
      raise tornado.web.HTTPError(400, 'Issue %s is not in "voting" state.' % issue['issue']['id'] )
    p = ''
    initiatives = ''

    # We need to create a drop down list where you can vote +n...+2, +1, 0, -1, -2...-n
    # Where n is the number of initiatives
    nr_ini = len( issue['initiatives'] )
    select_opts = ''
    selected = ''
    i = nr_ini
    while i >= -nr_ini :
      if i == 0 :
        selected = ' selected="selected"'
      else :
        selected = ''
      select_opts = select_opts + '<option value="%s"%s>%s</option>\n' % (i, selected, i)
      i = i - 1

    # Now create one table row for each initiative, appended with the drop down list
    for ini in issue['initiatives'] :
      link = "issue.html?id=" + str(issue['issue']['id']) + "&amp;initiative=" + str(ini['id'])
      initiatives = initiatives + \
                    """<tr><td>i%s: %s (<a target="_blank" href="%s">read initiative</a>)</td>
                           <td><select id="i%s" name="i%s">%s</select></td>
                       </tr>
                    """ % (ini['id'], ini['name'], link, ini['id'], ini['id'], select_opts )
        
    initiatives = initiatives + \
        """<tr><td><em>Status Quo</em></td><td>0</td></tr>
        """

    # TODO: Need separate page to pre-delegate your vote for area and unit
    js = """<script>
            function show(tab) {
               var tab = document.getElementById(tab);
               tab.style.display = "block";
            }
            function hide(tab) {
               var tab = document.getElementById(tab);
               tab.style.display = "none";
            }
            </script>
         """
    p = """<h1>Vote</h1>
           <p>%s &gt; %s</p>
           <p><strong>%s: %s</strong></p>
           <form name="vote" id="vote" method="post" action="vote.html?id=%s">
           <p>Cast direct vote: 
              <input type="radio" id="vote_type_direct" name="vote_type" value="direct" 
              onclick="show('direct_vote'); hide('delegate_vote');" checked="checked" /><br />
              Delegate your vote:
              <input type="radio" id="vote_type_delegated" name="vote_type" value="delegated" 
              onclick="show('delegate_vote'); hide('direct_vote');" /></p>
           <hr />
           <div id="direct_vote" style="display: block">
           <table cellpadding="10px">
           %s
           </table>
           </div>
           <div id="delegate_vote" style="display: none">
           <p>I'm delegating my vote for this issue to the following user:<br />
           Identification: <input type="text" id="trustee_identification" name="trustee_identification" value="" /></p>
           <p><em>Note: In Liquid Feedback, go to the profile page of the user you want to delegate your vote to,
           and copy the text from the "Identification" field. Match the capital letters, this field is case-sensitive!</em></p>
           </div>
           <br />
           <br />
           <hr />
           Username: <input type="text"     id="username" name="username" value="" /><br /><br />
           Password: <input type="password" id="password" name="password" value="" /><br /><br />
                     <input type="hidden"   id="issue_id" name="issue_id" value="%s" /><br /><br />
                     <input type="submit"   id="submit"   name="submit"   value="Save vote" />
           </form>
           <hr />
           <p>Please note: You can give the same score to more than one alternative.
              But the scores cannot contain gaps. For example... <br />
              This is allowed: (+1, 0, -1) <br />
              This is also allowed: (+1, +1, 0) <br />
              but this is not allowed: (+2, 0, -1) <br />
              ...since in the latter there is no score +1.<br />
              Note that 0 exists always due to 
              Status Quo, so all your scores have to be around 0: ...+2, +1, 0, -1, -2...</p>
        """ % (issue['unit']['name'], issue['area']['name'], issue['policy']['name'], \
               issue['issue']['id'], issue['issue']['id'], initiatives, issue['issue']['id'])
    self.write( "<html><head><title>Vote</title>" + js + "</head><body>" + p + "</body></html>")
    
  def post(self):
    """Process the submitted votes and save them in our DummyDB"""
    # First we need to check user credentials. This is done against the source
    # database (e.g. Liquid Feedback).
    username=self.get_argument('username')
    password=self.get_argument('password')
    ims = ImsConnectorFactory(LqfbDB)
    ims.connect(host=conf['lqfb.host'], password=conf['lqfb.password'])
    user_id = ims.userAuthentication(username, password)
    if not user_id :
      raise tornado.web.HTTPError(401, "To vote, please provide your Liquid Feedback username and password.")

    # Fetch issue that is voted on, we need it already
    dummy = dummyFactory()
    issue = dummy.getIssue(self.get_argument('issue_id'))
    # remove wrapper object
    issue = issue.getIssue()
    
    # Check that issue is in voting state
    if not issue['state'] == 'voting' :
      raise tornado.web.HTTPError(400, 'Issue %s is not in "voting" state.' % issue['issue']['id'] )

    # Check authorization
    if not ims.userAuthorization(user_id, issue['unit']['id']) :
      raise tornado.web.HTTPError(403, "User '%s' is not authorized to vote in unit <em>%s</em>" % (username, issue['unit']['name']) )
    
    if self.get_argument('vote_type') == 'direct' :
      # Get user score for each initiative in issue
      scores = {}
      for ini in issue['initiatives'] :
        arg = "i" + str( ini['id'] )
        value = int( self.get_argument(arg) )
        scores[ int( ini['id'] ) ] = value

      # Check that values are within allowed range.
      # Rules:
      """You can give the same score to more than one alternative.
        But the scores cannot contain gaps. For example... <br />
        This is allowed: (+1, 0, -1) <br />
        This is also allowed: (+1, +1, 0) <br />
        but this is not allowed: (+2, 0, -1) <br />
        ...since in the latter there is no score +1.<br />
        Note that 0 exists always due to 
        Status Quo, so all your scores have to be around 0: ...+2, +1, 0, -1, -2...
        """
      #Speaking of which, need to add the Status Quo
      scores[None] = 0
      # Now we can check for a consecutive range
      v_list = [v for (k,v) in scores.items()]
      v_list.sort()
      previous = v_list[0]
      for v in v_list :
        if v != previous and v != previous + 1 :
          raise tornado.web.HTTPError(400, 'Illegal scores in your vote (there is a gap in the values): ' + ", ".join(str(x) for x in v_list) )
        previous = v
      # With my logic, the above is also a sufficient check that values are between
      # -nr_ini ... nr_ini

      # We don't actually save the Status Quo vote to database:
      del( scores[None] )
      # Now save the vote
      dummy.saveVote(user_id, self.get_argument('issue_id'), scores, 'direct' )
      self.write("Your vote was saved successfully. Thank you for voting!")
    elif self.get_argument('vote_type') == 'delegated' :
      trustee_id = ims.getUserId(self.get_argument('trustee_identification'), 'identification')
      if trustee_id :
        dummy.saveVote(user_id, self.get_argument('issue_id'), trustee_id, 'delegated' )
        self.write("Your vote was saved successfully. Thank you for voting!")
      else :
        raise tornado.web.HTTPError(400, 'Cannot delegate vote. No such member in this voting system: %s' % self.get_argument('trustee_identification') )
    else :
      raise tornado.web.HTTPError(400, 'Invalid vote_type: %s' % self.get_argument('vote_type') )
      
      
      
class Cron(MyBaseRequestHandler):
  """Execute periodic tasks, such as poll LQFB event table."""
  dummy = None
  ims = None

  def get(self):
    self.dummy = dummyFactory()
    self.ims = ImsConnectorFactory(LqfbDB)
    self.ims.connect(host=conf['lqfb.host'], password=conf['lqfb.password'])
    self.getIssuesForVoting()
    self.getPublicVotes()
    self.getIssuesToCalculate()
    self.calculateResults()
    self.returnResults()
    self.write("Execution of periodic tasks completed.")

  def getIssuesForVoting(self) :
    dummy = self.dummy
    ims = self.ims
    leid = dummy.getLastEventId('voting')
    issues = ims.getIssuesForVoting(leid)
    if issues.isEmpty() :
      return
    else :
      dummy.insertIssuesForVoting(issues)

  def getPublicVotes(self) :
    dummy = self.dummy
    ims = self.ims
    leid = dummy.getLastEventId('public_voting_closed')
    (public_votes, leid) = ims.getPublicVotes(leid)
    if len( public_votes ) > 0 :
      dummy.insertPublicVotes(public_votes, leid)
      
  def getIssuesToCalculate(self) :
    dummy = self.dummy
    ims = self.ims
    leid = dummy.getLastEventId('private_voting_closed')
    (issue_id_list, leid) = ims.getIssuesToCalculate(leid)
    if len( issue_id_list ) > 0 :
      dummy.setPrivateVotingClosed(issue_id_list, leid)

  def calculateResults(self) :
    """In DummyDB calculation is actually provided by a series of views, so there is nothing to do for now."""
    return True

      
  def returnResults(self) :
    """Return results from battle_view to liquid_feedback battle table."""
    dummy = self.dummy
    ims = self.ims
    (battle_list, voter_count_map) = dummy.getPrivateVotingResults()
    if len( battle_list ) > 0 :
      if ims.returnResults(battle_list, voter_count_map) == True :
        # If results were successfully returned, set state on these issues to closed
        dummy.setClosed(battle_list)
    
