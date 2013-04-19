#!/usr/bin/python
"""HTTP Server provides a HTML user interface and some JSON APIs for Solon Voting."""
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
import sys

from config import conf
from dummy.dummyapi import *
import pickle
import pprint
import json


# The callback classes are defined in dummy/dummyapi.py      
application = tornado.web.Application([
    (r"/", MainHandler),
    (r"/cron", Cron),
    (r"/list.json", ListIssuesJson),
    (r"/issue.json", GetIssueJson),
    (r"/list.html", ListIssuesHtml),
    (r"/issue.html", GetIssueHtml),
    (r"/vote.html", VoteHtml),
])

if __name__ == "__main__":
    application.listen(conf['tornado.port'])
    tornado.ioloop.IOLoop.instance().start()
