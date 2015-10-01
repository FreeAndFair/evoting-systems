/*
Prime III

URL: http://www.PrimeVotingSystem.org

Copyright (c) 2015 University of Florida

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>. 

*/

function setCookie(name, value, seconds) 
{
	var expires = "";
	if (typeof(seconds) != 'undefined') 
	{
		var date = new Date();
		date.setTime(date.getTime() + (seconds*1000));
		expires = "; expires=" + date.toGMTString();
	}

	document.cookie = name+"="+value+expires+"; path=/";
}
 
function getCookie(name) 
{ 
	name = name + "=";
	var carray = document.cookie.split(';');

	for(var x=0;x < carray.length;x++) 
	{
		var c = carray[x];
		while (c.charAt(0)==' ') c = c.substring(1,c.length);
		if (c.indexOf(name) == 0) return c.substring(name.length,c.length);
	}

		return null;
}
 
function deleteCookie(name) 
{
	setCookie(name, "", -1);
}
	
function deleteAllCookies() 
{
  	var theCookies = document.cookie.split(';');
  	var votes = 0;
  	
  	for (var x = 0; x < theCookies.length; x++) 
  	{
  		var thisCookie = window.top.explode("=", theCookies[x]);
  		deleteCookie(thisCookie[0]);
  	}
}
	
