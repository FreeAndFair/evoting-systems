#! /bin/sh 
# This file is (C) copyright 2001-2008 Software Improvements, Pty Ltd 
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
# This file contains the top-level executable for Load Scanned Votes
#
################################################################
# BIG NOTE: 
#             THIS SCRIPT MUST BE RUN AS ROOT
################################################################
#
# Load Scanned Votes for Counting

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
#           load_evacs_cdrom()
source "$SCRIPTROOT/cdrom.sh"

# menu_start.sh calls this script and passes these environment variables:
#           $EVACS_SCRATCH

# A note about processing input data:
# Be careful to strip out carriage returns _before_
# using 'grep -v "^$"'.
# In general you should find every occurrence of 'grep -v "^$"'
# preceded at some point by "sed 's/\r//g'"


DBPREFIX="evacs"


ask_to_continue()
{
    LOAD=0;
    while [ $LOAD == 0 ]; do
        instruct "Do you wish to load the papers into the database (y/n)?"
        read INPUT
        delete_instruction
        case $INPUT in
            y|Y|yes) LOAD=1;;
            n|N|no) eject_media
	        bailout "The papers from the disk were NOT loaded into the database.";;	
            *) warn "ERROR: UNKNOWN OPTION SELECTED.                             ";;
        esac
    done
}


# Issue Prompt for Media
# Wait for Key
display_prompt()
{
    instruct "Please insert CD-R for scanned papers and press return:"
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
    umount $CDROM_DEVICE >/dev/null 2>&1
    eject $CDROM_DEVICE >/dev/null 2>&1
    dmesg -n 4
}


remove_checking_database()
{
    DBNAME=$DBPREFIX$PASS
    su - postgres -c "psql -v ON_ERROR_STOP=1 template1 >/dev/null 2>&1 <<%
	DROP DATABASE $DBNAME;
%" >/dev/null 2>&1
    if [ $? != 0 ]; then
        eject_media
        bailout "Failed to drop database $DBNAME"
    fi
}

create_checking_database()
{
    DBNAME=$DBPREFIX$PASS
    su - postgres -c "psql template1 >/dev/null 2>&1 <<%
	DROP DATABASE $DBNAME;
%" >/dev/null 2>&1
    su - postgres -c "psql -v ON_ERROR_STOP=1 template1 >/dev/null 2>&1 <<%
	CREATE DATABASE $DBNAME;
%" >/dev/null 2>&1
    if [ $? != 0 ]; then
        eject_media
        bailout "Failed to create database $DBNAME"
    fi

    # Create batch and scanned_vote tables to hold all scanned votes.
    # We have to create the batch table here rather than
    # dump its schema with pg_dump because the source table
    # has triggers we don't want (they refer to other tables).
    su - postgres -c "psql -v ON_ERROR_STOP=1 $DBNAME >/dev/null 2>&1 <<EOF
CREATE TABLE batch (
    number integer NOT NULL PRIMARY KEY,
    polling_place_code integer NOT NULL,
    electorate_code integer NOT NULL,
    size integer,
    "committed" boolean DEFAULT false NOT NULL
);
CREATE INDEX batch_num_idx ON batch USING btree (number);

CREATE TABLE scanned_vote (
    id integer NOT NULL,
    batch_number integer NOT NULL,
    paper_version integer DEFAULT -1 NOT NULL,
    time_stamp timestamp,
    preference_list text
);

CREATE INDEX scanned_vt_btch_idx ON scanned_vote USING btree (batch_number);

EOF" >/dev/null 2>&1
    if [ $? != 0 ]; then
        eject_media
        bailout "Failed to create temporary database tables"
    fi
    # Copy batch table data into temporary database
    su - postgres -c \
        "(pg_dump -a -t batch $DBPREFIX | psql -v ON_ERROR_STOP=1 $DBNAME) >/dev/null 2>&1 "
    if [ $? != 0 ]; then
        eject_media
        announce "Removing temporary database because there was an error."
        remove_checking_database
        bailout "Failed to copy batch data to temporary database"
    fi

    # Remove electronic batches, which have NULL size
    su - postgres -c "psql -v ON_ERROR_STOP=1 $DBNAME >/dev/null 2>&1 <<EOF
DELETE FROM batch WHERE size IS NULL;
EOF" >/dev/null 2>&1
    if [ $? != 0 ]; then
        eject_media
        bailout "Failed to clean up batch data in temporary database"
    fi


}

get_votes_for_checking()
{
# DDSv2A-3.2 Get Votes

    DBNAME=$DBPREFIX$PASS

    # Create file to be loaded
    announce "Copying scanned papers to hard disk."
    echo "COPY scanned_vote FROM stdin;" > $EVACS_SCRATCH
    cat $CDROM_DIRECTORY/$TYPE.dmp | sed 's/\r//g' | grep -v "^$" | \
        sed 's/\t//g' | \
        awk -F\, ' { if (NF != 4) {print "Bad line of input data:\n"$0> "/dev/stderr";  exit(1);} print NR"\t"$1"\t"$2"\t"$3"\t"$4  }' \
        >> $EVACS_SCRATCH
    if [ $? != 0 ]; then
        eject_media
        bailout "Failed to load papers; $TYPE.dmp was not in the right format!"
    fi


    announce "Loading scanned papers into temporary database."
    su - postgres -c "psql -v ON_ERROR_STOP=1 $DBNAME -f $EVACS_SCRATCH 2>&1 >/dev/null | cut -d: -f 4-  ; exit \${PIPESTATUS[0]}"

    if [ $? != 0 ]; then
        eject_media
        bailout "Failed to load papers; $TYPE.dmp was not in the right format!"
    fi

    rm -f $EVACS_SCRATCH
}

# initialise the checking_databases(evacs1)
# (You don't REALLY want to nuke the evacs database whenever
# scanned votes are loaded)

# create confirmed_votes database
#
# Votes will be transferred after checking
    
PASS=1
TYPE=scanned

display_prompt

# Use black on black to hide spurious error message
text_mode $RESET $BLACK $BLACK
load_evacs_cdrom
text_mode $RESET $WHITE $BLACK

# Check all the required files are present on the disk.
if [ ! -r $CDROM_DIRECTORY/$TYPE.txt ] || \
  [ ! -r $CDROM_DIRECTORY/$TYPE.dmp ] || \
  [ ! -r $CDROM_DIRECTORY/$TYPE.rnd ] ; then
    eject_media
    bailout "One or more files are missing from the disk."
fi

# Display the text message on the CD
SHELL=/bin/true EDITOR=/bin/true VISUAL=/bin/true \
    su nobody -m -f -s /bin/sh -c "more -d -15 $CDROM_DIRECTORY/$TYPE.txt"

# Display the sum of the output file.
announce "The checksum of the disk is:"
display_signature `cat $CDROM_DIRECTORY/$TYPE.dmp $CDROM_DIRECTORY/$TYPE.rnd | md5sum`

ask_to_continue

announce "Preparing temporary database."
create_checking_database    	    

get_votes_for_checking        
	    
announce "Checking the format of the data."
		    
su - postgres -c "$PWD/check_scanned_votes_bin"
if [ $? != 0 ] ; then
    eject_media
    announce "Removing temporary database because there was an error."
    remove_checking_database
    bailout "The data is not OK.  It will not be loaded."
fi

announce "Loading the papers into the counting database."

text_mode $BRIGHT $YELLOW $BLACK
su - postgres -c "$PWD/handle_scanned_votes_bin"
if [ $? != 0 ] ; then
    eject_media
    # Remove any /tmp/evacsX* files created during import
    rm -f /tmp/evacsX*
    announce "Removing temporary database because there was an error."
    remove_checking_database
    bailout "Loading of scanned papers failed!"
fi

eject_media
announce "Scanned papers successfully loaded."

announce "Removing temporary database."
remove_checking_database

exit 0
