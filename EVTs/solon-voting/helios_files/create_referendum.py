#!/usr/bin/python

# Usage
# ./create_referendum.py referendum_short_name
# Note that referendum_short_name must be unique, e.g. use "autoreferendum1", "autoreferendum2", ... for tests.

# This is an example python script how to:
# - login to Helios, using dummy authentication for now
# - create a referendum
# - create questions in the referendum
# - upload a csv file with eligible voters
# - freeze the election, after which voters can vote
# TODO:
# - Put the debug printouts behind an "if DEBUG == True :"
# - We need requests module to post multipart/form-data, we might as well get 
#   rid of httplib and use requests module throughout, it is much nicer.
# - Get rid of lxml parser and just use regexps to catch the csrf_token
# - There seems to be a way to set the ending time for an election, find out how to do that.


import sys
import httplib, urllib
from urlparse import urlparse

import pprint

if len(sys.argv) < 2 :
  print "Usage: %s referendum_short_name\nNote that referendum_short_name must be unique, use a new one for each try." % sys.argv[0]
  sys.exit()

# Set these configuration variables to match your Helios setup
host = "localhost"
port = "8000"
username = "solonclient"

referendum_short_name=sys.argv[1]
referendum_name="Automatically generated referendum"
referendum_description="Describe the content of the referendum here..."

####################################################################
conn = httplib.HTTPConnection(host, port)

################################################################################
# Login to Helios
# You must use the 'dummy' authentication backend in Helios settings.py:
# AUTH_ENABLED_AUTH_SYSTEMS = ['dummy']
# AUTH_DEFAULT_AUTH_SYSTEM = 'dummy'
################################################################################

path = "/auth/?return_url=/"
conn.request("GET", path)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
cookie   = r.msg.get("Set-Cookie")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print
print

if not redirect :
  print "ERROR: I was expecting to be redirected here to http://localhost:8000/auth/start/dummy?return_url=/"
  sys.exit()
url = urlparse(redirect)
path = url.path + "?" + url.query
headers = {'Cookie': cookie}

conn.request("GET", path, None, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
cookie   = r.msg.get("Set-Cookie")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print
print
  
  
if not redirect :
  print "ERROR: I was expecting to be redirected to http://localhost:8000/auth/dummy/login"
  sys.exit()
url = urlparse(redirect)
path = url.path + "?" + url.query
headers = {'Cookie': cookie}
  
conn.request("GET", path, None, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
cookie   = r.msg.get("Set-Cookie")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print
print


# No more redirects, the above was the login form. 
# We need the hidden field csrf_token from the html form
from lxml import etree
from StringIO import StringIO
parser = etree.HTMLParser()
tree   = etree.parse(StringIO(data), parser)
root   = tree.getroot()
form   = root.find(".//form[@id='login_form']")
i      = form.find(".//input[@type='hidden']")
csrf_token = i.attrib['value']
    
if not csrf_token :
  print "ERROR: Failed to find csrf_token from the form sent by the Helios server."
  sys.exit()

print "Found csfr_token: " + csrf_token

path = path # Same path, just use POST instead
headers = {"Cookie": cookie, 
           "Content-type": "application/x-www-form-urlencoded",
           "Accept": "text/plain"} 
data = "csrf_token=%s&username=%s&admin_p=on" % (csrf_token, username)

conn.request("POST", path, data, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
cookie   = r.msg.get("Set-Cookie")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print r.msg.get("Location")
print
print
  
  
if not redirect :
  print "ERROR: I was expecting to be redirected to http://localhost:8000/auth/after/"
  sys.exit()
url = urlparse(redirect)
path = url.path + "?" + url.query
headers = {'Cookie': cookie}
  
conn.request("GET", path, None, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
cookie   = r.msg.get("Set-Cookie")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print
print
  
  
if not redirect :
  print "ERROR: I was expecting to be redirected to http://localhost:8000/auth/after_intervention"
  sys.exit()
url = urlparse(redirect)
path = url.path + "?" + url.query
headers = {'Cookie': cookie}
  
conn.request("GET", path, None, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
# Note: Something tricky here, Helios does not return the cookie in these headers
# But we should keep the old cookie that we have
# cookie   = r.msg.get("Set-Cookie")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print
print


if not redirect :
  print "ERROR: I was expecting to be redirected to http://localhost:8000/"
  sys.exit()
url = urlparse(redirect)
path = url.path + "?" + url.query
headers = {'Cookie': cookie}
  
conn.request("GET", path, None, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
cookie   = r.msg.get("Set-Cookie")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print
print



################################################################################
# End of login sequence
# The cookie is passed as output into the next sequence, it is what identifies 
# us as logged in.
################################################################################



################################################################################
# Create new referendum
################################################################################
path = "/helios/elections/new"
raw_data = {"short_name" : referendum_short_name,
            "name" : referendum_name,
            "description" : referendum_description,
            "election_type" : "referendum"
           }
data = urllib.urlencode(raw_data)
headers = {"Cookie": cookie,
           "Content-type": "application/x-www-form-urlencoded",
           "Accept": "text/plain"}

           
conn.request("POST", path, data, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
# No Set-Cookie from here on, we just need to keep using the old cookie
# cookie   = r.msg.get("Set-Cookie")

# Redirect url contains a UUID for the newly created referendum, like this:
# Location: http://localhost:8000/helios/elections/84f999ac-7b7c-11e2-94a9-08002710ab51/view
if not redirect :
  print "ERROR: I was expecting to be redirected to http://localhost:8000/helios/elections/<UUID>/view"
  sys.exit()
url = urlparse(redirect)
import re
pattern = re.compile(r'/helios/elections/(.*)/view')
match = pattern.match(url.path)
referendum_uuid = match.group(1)

# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print referendum_uuid
print
print

# Use the referendum_uuid to GET the page with questions
# We need to save the csrf_token to be used with the POST data
path = "/helios/elections/" + referendum_uuid + "/questions"
headers = {'Cookie': cookie}
conn.request("GET", path, None, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
# Find this line in data (it's part of a javascript function)
# CSRF_TOKEN = '214eed7f-63cb-4443-a18b-507d9611ff28';
pattern = re.compile("CSRF_TOKEN = '(.*)';")
match = pattern.search(data)
csrf_token = match.group(1)

# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print csrf_token
print
print



# To create a question to vote for, we need to send this:
# questions_json=%5B%7B%22question%22%3A+%22Build+death+star+replica%22%2C+%22min%22%3A+0%2C+%22max%22%3A+1%2C+%22short_name%22%3A+%22Build+death+star+replica%22%2C+%22answers%22%3A+%5B%22Yes%22%2C+%22Maybe%22%2C+%22No%22%5D%2C+%22answer_urls%22%3A+%5Bnull%2C+null%2C+null%5D%2C+%22choice_type%22%3A+%22approval%22%2C+%22tally_type%22%3A+%22homomorphic%22%2C+%22result_type%22%3A+%22absolute%22%7D%5D&csrf_token=214eed7f-63cb-4443-a18b-507d9611ff28
# Which is urlencoded form of this:
# questions_json=[{"question":+"Build+death+star+replica",+"min":+0,+"max":+1,+"short_name":+"Build+death+star+replica",+"answers":+["Yes",+"Maybe",+"No"],+"answer_urls":+[null,+null,+null],+"choice_type":+"approval",+"tally_type":+"homomorphic",+"result_type":+"absolute"}]&csrf_token=214eed7f-63cb-4443-a18b-507d9611ff28

path = "/helios/elections/" + referendum_uuid + "/save_questions"
questions = []
questions.append({})
questions[0]['question'] = "Question 1"
questions[0]['min'] = 0
questions[0]['max'] = 1
questions[0]['short_name'] = "question1"
questions[0]['answers'] = ["Alternative 1", "Alternative 2", "Alternative 3"]
questions[0]['answer_urls'] = ["http://liquid_feedback/alternative1", "http://liquid_feedback/alternative2", "http://liquid_feedback/alternative3"]
questions[0]['choice_type'] = "approval"
questions[0]['tally_type'] = "homomorphic"
questions[0]['result_type'] = "absolute"
# You could add more than one question per referendum, just do
# questions.append({}) and start all over

import json
questions_json = json.dumps(questions)
raw_data = {"questions_json" : questions_json,
            "csrf_token" : csrf_token
           }
data = urllib.urlencode(raw_data)
headers = {"Cookie": cookie,
           "Content-type": "application/x-www-form-urlencoded",
           "Accept": "text/plain"}           
conn.request("POST", path, data, headers)
r = conn.getresponse()
# Should contain just one word: SUCCESS
data = r.read()
redirect = r.msg.get("Location")

# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect
print
print


################################################################################
# End of creating referendum questions
################################################################################


################################################################################
# Upload list of eligible voters
################################################################################

path = "/helios/elections/" + referendum_uuid + "/voters/upload"
headers = {'Cookie': cookie}
  
conn.request("GET", path, None, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect

# We need the hidden field csrf_token from the html form
from lxml import etree
from StringIO import StringIO
parser = etree.HTMLParser()
tree   = etree.parse(StringIO(data), parser)
root   = tree.getroot()
form   = root.find(".//form[@id='upload_form']")
i      = form.find(".//input[@type='hidden']")
csrf_token = i.attrib['value']
    
if not csrf_token :
  print "ERROR: Failed to find csrf_token from the form sent by the Helios server."
  sys.exit()

print "Found csfr_token: " + csrf_token
print
print

# Apparently python httplib doesn't support POSTing multipart/form-data
# Should have maybe used this library from the beginning then, it looks simpler...
import requests

path = "/helios/elections/" + referendum_uuid + "/voters/upload"
url = "http://%s:%s%s" % (host, port, path)
raw_data = {"csrf_token" : csrf_token}
files = {'voters_file': """alice,alice@localhost,Alice
bob,bob@localhost,Bob
carol,carol@localhost,Carol
dave,dave@localhost,Dave
"""}
#Alternatively
files = {'voters_file': open('test_voters.csv', 'rb')}

# We need to split the cookie into key and value
# This is only because I didn't use requests library from the start...
pattern = re.compile(r'sessionid=([0123456789abcdef]*)')
match = pattern.match(cookie)
sessionid = match.group(1)
cookies = {'sessionid' : sessionid}

r = requests.post(url, files=files, data=raw_data, cookies=cookies)

data = r.content
redirect = r.headers.get("Location")

# Debug prints...
print path
print r.status_code
print data
pprint.pprint(r.headers)
print redirect
print
print



path = "/helios/elections/" + referendum_uuid + "/voters/upload"
headers = {"Cookie": cookie, 
           "Content-type": "application/x-www-form-urlencoded",
           "Accept": "text/plain"} 
data = "confirm_p=1"

conn.request("POST", path, data, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print r.msg.get("Location")
print
print



################################################################################
# End of upload list of eligible voters
################################################################################

################################################################################
# Freeze the referendum so that people can start voting
################################################################################

path = "/helios/elections/" + referendum_uuid + "/freeze"
headers = {'Cookie': cookie}
  
conn.request("GET", path, None, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print redirect

# We need the hidden field csrf_token from the html form
from lxml import etree
from StringIO import StringIO
parser = etree.HTMLParser()
tree   = etree.parse(StringIO(data), parser)
root   = tree.getroot()
# This form has no id="" attribute. Bad, bad web developer! No cookie for you.
form   = root.find(".//form")
i      = form.find(".//input[@type='hidden']")
csrf_token = i.attrib['value']
    
if not csrf_token :
  print "ERROR: Failed to find csrf_token from the form sent by the Helios server."
  sys.exit()

print "Found csfr_token: " + csrf_token
print
print


path = path # Same path, just use POST instead
headers = {"Cookie": cookie, 
           "Content-type": "application/x-www-form-urlencoded",
           "Accept": "text/plain"} 
# For this one there's just the token to post, no other data
data = "csrf_token=%s" % csrf_token

conn.request("POST", path, data, headers)
r = conn.getresponse()
data = r.read()
redirect = r.msg.get("Location")
# Debug prints...
print path
print r.status, r.reason
print data
pprint.pprint(r.msg.headers)
print r.msg.get("Location")
print
print

################################################################################
# End of freeze. Referendum is now open for voting.
################################################################################

conn.close()