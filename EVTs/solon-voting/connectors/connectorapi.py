"""Interface and factory for classes that interact with an external issue management system.

   Solon core modules use the ImsConnectorFactory() to get an instance
   of a connector of the given type.

   Currently there is only the Liquid Feedback connector. As long as we are
   developing only one implementation of the interface, there is no interface
   or superclass, the implementation is the interface. Hence this file only
   provides the factory.
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

from connectors.lqfb.lqfbdb import *

def ImsConnectorFactory(type) :
  # We ignore the type...
  return LqfbDB()