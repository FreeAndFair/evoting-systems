from distutils.core import setup, Extension

module1 = Extension('pilballot',
                    sources = ['temp.c'])

setup (name = 'PILBallot',
       version = '1.0',
       description = 'This is a package in aid of ballot analysis',
       ext_modules = [module1])
