"""Solon Voting configuration file"""

conf = {}

# These parameters are used to connect to the PostgreSQL db used by the "dummy" backend
conf['dummydb.host']        = '127.0.0.1'
conf['dummydb.password']    = 'password'
# These are currently ignored by the code so changing them here won't help. 
conf['dummydb.user']        = 'www-data'
conf['dummydb.dbname']      = 'solon_dummy'
conf['dummydb.port']        = 5432

# These parameters are used by the LQFB connector to connect to your Liquid Feedback Core PostgreSQL db.
conf['lqfb.host']           = '127.0.0.1'
conf['lqfb.port']           = 5432
conf['lqfb.user']           = 'www-data'
conf['lqfb.password']       = 'password'
conf['lqfb.dbname']         = 'liquid_feedback'

# Tornado is the web server
conf['tornado.port'] = 8888