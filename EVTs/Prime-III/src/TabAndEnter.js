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


function addTabEvent(obj)
{
	var myInput = document.getElementById(obj);

	if (myInput.addEventListener ) 
	    myInput.addEventListener('keydown',this.keyHandler,false);
	else if (myInput.attachEvent ) 
	    myInput.attachEvent('onkeydown',this.keyHandler); 
}

function keyHandler(e) 
{
    if ((e.keyCode == window.top.TABKEY) || (e.keyCode == 39) || (e.keyCode == 40) || (e.keyCode == 32))
    {
        e.preventDefault(); //prevent the tab from moving to the next item and from propogating through DOM
		window.top.processTab();
    }
    else if (e.keyCode == window.top.ENTERKEY)
    {
        e.preventDefault(); //prevent the tab from moving to the next item and from propogating through DOM
		window.top.processEnter();
    }
    else if ((e.keyCode == 38) || (e.keyCode == 37))
    {
        e.preventDefault(); //prevent the tab from moving to the next item and from propogating through DOM
		window.top.processBack();
/*
Right = 39
Left = 37
Down = 40
Up =    38
Space = 32 
*/
    }
}

function addEventHandlers()
{
	if (window.top.UseAudio) 
	{	
		var elem = document.getElementById('myForm').elements;
		for (i=0;i<elem.length;i++)
		{
			addTabEvent(elem[i].id);
		}
	}
}

setTimeout("addEventHandlers()", 400);