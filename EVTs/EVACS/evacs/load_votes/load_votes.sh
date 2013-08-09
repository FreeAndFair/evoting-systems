#! /bin/sh 
# This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd 
#
# This program is free software; you can redistribute it and/or modify
#   it under the terms of the GNU General Public License as published by
#   the Free Software Foundation; either version 2 of the License, or
#   (at your option) any later version.
#
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#   GNU General Public License for more details.
#
#   You should have received a copy of the GNU General Public License
#   along with this program; if not, write to the Free Software
#   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */
#
# This file contains the top-level executable for Load Votes for Counting
#
################################################################
# BIG NOTE: 
#             THIS SCRIPT MUST BE RUN AS ROOT
################################################################
#
# DDSv2A-3.1 Load Votes for Counting

# where all the scripts and executables are
SCRIPTROOT=/opt/eVACS/bin

# console.sh exports: 
#          text_mode(MODE FGCOLOUR BGCOLOUR)
#          bailout(msg)
#          warn(msg)
#          announce(msg)
#          instruct(msg)
#          delete_instruction()
source "$SCRIPTROOT/console.sh"

# cdrom.sh exports:
#           $CDROM_DEVICE
#           $CDROM_DIRECTORY
#           $SCSI_DEVICE
#           $RECORD_OPTIONS
#           load_blank_cdrom()
#           load_evacs_cdrom()
source "$SCRIPTROOT/cdrom.sh"

DBPREFIX="evacs"

PG_DIRECTORY=/usr/lib/postgres/data


ask_to_continue()
{
LOAD=0;
while [ $LOAD == 0 ]; do
    instruct "Do you wish to load the votes into the database(y/n)?"
    read INPUT
    delete_instruction
    case $INPUT in
	y|Y|yes) LOAD=1;;
	n|N|no) eject_media
	        bailout "The votes from the master and slave disks were NOT loaded onto the database.";;	
	 *) warn "ERROR: UNKNOWN OPTION SELECTED.                             ";;
    esac
done
}



# DDSv2A-3.2: Issue Prompt for Media
# DDSv2A-3.2: Wait for Key
display_prompt()
{
    instruct "Please insert CD-R for $TYPE and press return:"
    read -s DISCARD
  
    # replace highlighted instruction with default colours
    delete_instruction
    echo  -n "                                                                                 "
    delete_instruction
}

# display the ballot signature
display_signature() {
    # translate signature to caps and split with spaces
    SIG=`echo $1 | sed "y/abcdef/ABCDEF/" | sed "s/\(.\)/\1 /g"`
    count=1
    COLOUR=$CYAN
    acc=''
    join=''
    # draw top of box 
    text_mode $BRIGHT $RED $BLACK
    echo    "          +-----------------------------------------+"
    echo -n "          | "

    for char in $SIG; do
        acc=${acc}$char
	if [ $count == 4 ]; then
	    count=0
	    text_mode $BRIGHT $RED $BLACK
	    echo -n $join
	    text_mode $BRIGHT $COLOUR $BLACK
	    echo -n $acc

	    if [ "$COLOUR" == "$CYAN" ]; then
               COLOUR=$GREEN
	    else
	       COLOUR=$CYAN
            fi
	    acc=''
	    join='-'
	fi
	let count=$count+1
    done
    
    text_mode $BRIGHT $RED $BLACK
    # print bottom of box
    echo " |"
    echo "          +-----------------------------------------+"
    text_mode $RESET $WHITE $BLACK
}

eject_media()
{
# turn off kernel error messages to suppress spurious error message
        dmesg -n 1
    	umount $CDROM_DEVICE 2>&1 >/dev/null
	eject $CDROM_DEVICE 2>&1 > /dev/null
	dmesg -n 4
}


# DDSv2A-3.1: Get Votes
setup_vote_database()
{
	mkdir -p -m 700 $DIRECTORY 2> /dev/null
	chown postgres $DIRECTORY

	su - postgres -c "initdb -D $DIRECTORY 2>&1 >/dev/null" 2>&1 >/dev/null 

	su - postgres -c "/usr/bin/pg_ctl start -w -D $DIRECTORY 2>&1 >/dev/null" 2>&1 >/dev/null
    	if [ $? != 0 ]; then
		eject_media
	        bailout "Failed to start postmaster for $TYPE Backup!  target dir $DIRECTORY"
    	fi
}

recreate_checking_database()
{
	DBNAME=$DBPREFIX$PASS
	su - postgres -c "psql template1 2>&1 > /dev/null <<%
	DROP DATABASE $DBNAME;
	CREATE DATABASE $DBNAME;
%" 2>&1 >/dev/null
    	if [ $? != 0 ]; then
	      eject_media
	      bailout "Failed to drop/create database $DBNAME"
    	fi
}

get_votes_for_checking()
{
# DDSv2A-3.2 Get Votes
#  use black on black to hide spurious error message
        text_mode $RESET $BLACK $BLACK
   	load_evacs_cdrom
	text_mode $RESET $WHITE $BLACK

	su - postgres -c "psql  $DBPREFIX$PASS < $CDROM_DIRECTORY/$TYPE.dmp 2>&1>/dev/null" 2>&1 >/dev/null
    	if [ $? != 0 ]; then
  	         eject_media
		 bailout "Failed to load $TYPE Backup!"
    	fi
	
# Loose referrential integrity on <elec>_confirmed_vote 
	NUM_ELECS=`su - postgres -c"psql evacs <<EOF
                   SELECT COUNT(*) from electorate;
EOF"| sed 's/^ *//g' | tail -3 | head -1`
	
	ELECS=`su - postgres -c"psql evacs <<EOF
                  SELECT name from electorate;
EOF"| sed 's/^ *//g' | tail -"$(($NUM_ELECS+2))" | head -"$NUM_ELECS"`
	
	for ELECTORATE in $ELECS; do
	    su - postgres -c "psql $DBPREFIX$PASS 2>&1 >/dev/null<<EOF
                CREATE TABLE ${ELECTORATE}_cv AS SELECT * FROM ${ELECTORATE}_confirmed_vote;
                DROP TABLE ${ELECTORATE}_confirmed_vote;
                CREATE TABLE ${ELECTORATE}_confirmed_vote AS SELECT * FROM ${ELECTORATE}_cv; 
                DROP TABLE ${ELECTORATE}_cv;
EOF" 2>&1 > /dev/null
	done
}
# initialise the checking_databases(evacs1,2)
#  and the confirmed vote database(evacs)
# (You don't REALLY want to nuke the evacs database whenever a polling
# place loads it's results)
# setup_vote_database

# create confirmed_votes database
#
# Votes will be transferred after checking
    


    PASS=1
    # DDSv2A-3.1: Get Votes
    while [ $PASS -le 2 ] ; do
    
        if [ $PASS = 1 ]; then
		    TYPE="master"
	    else
		    TYPE="slave"
	    fi
	    
	    display_prompt
	    
	    recreate_checking_database    	    
	    get_votes_for_checking        

	    PP_CODE=`su - postgres -c"psql evacs$PASS <<EOF
SELECT polling_place_code
FROM server_parameter
WHERE id = (SELECT MIN(id)
FROM server_parameter);
EOF"`
	    PP_CODE=`echo $PP_CODE|awk '{print $3}'`
	    PP_NAME=`su - postgres -c"psql evacs <<EOF
SELECT DISTINCT name 
FROM polling_place 
WHERE code = $PP_CODE; 
EOF"| tail -3 | head -1 | sed "s/ //"`
	    
	    # Display the sum of the output file.
	    announce "The $TYPE Ballot Box signature for $PP_NAME is:"
	    display_signature `cat $CDROM_DIRECTORY/$TYPE.dmp $CDROM_DIRECTORY/$TYPE.rnd | md5sum`

	    su - postgres -c "$PWD/check_for_repeats_bin"
	    if [ $? != 0 ]; then
		    eject_media
                   bailout "Data for this polling place ($PP_NAME) has already been loaded"
	    fi
	    let PASS=$PASS+1
	    
	    eject_media 
    done

    ask_to_continue

    announce "Checking master and slave ballot boxes for consistency."
		    
    su - postgres -c "$PWD/check_votes_bin"
    if [ $? != 0 ] ; then
	eject_media
	bailout "Votes from each disk do not match!!  Check the disks and start again..."
    fi

    announce "Loading the votes into the counting database."

    text_mode $BRIGHT $YELLOW $BLACK
    su - postgres -c "$PWD/handle_few_votes_bin"
    if [ $? != 0 ] ; then
        eject_media
	bailout "Loading of votes failed!"
    fi

eject_media
announce "Votes successfully loaded for Polling Place:`text_mode $BRIGHT $YELLOW $BLACK`$PP_NAME."

exit 0











