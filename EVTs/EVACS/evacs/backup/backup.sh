#! /bin/sh 

# This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

# DDSv1D-3.2: End of Day Backup
# Script to set up backup polling place electronic votes.

SCRIPTROOT=/opt/eVACS/bin
# console.sh exports: 
#          text_mode(MODE FGCOLOUR BGCOLOUR)
#          bailout(msg)
#          warn(msg)
#          announce(msg)
#          instruct(msg)
#          delete_instruction()
source "$SCRIPTROOT/console.sh" && CONSOLE='loaded'

# cdrom.sh exports:
#           $CDROM_DEVICE
#           $CDROM_DIRECTORY
#           $CDROM_SCSI_DEVICE
#           $CDROM_RECORD_OPTIONS
#           load_blank_cdrom()
#
source "$SCRIPTROOT/cdrom.sh" && CDROM='loaded'

# database settings
DB_NAME="evacs"
MASTER_PORT=5432
SLAVE_PORT=5433

 # directories we will be using
WEB_IMAGES_DIRECTORY=/var/www/html/images
TEMP_DIRECTORY=/tmp
ISO_DIRECTORY="$TEMP_DIRECTORY/evacs"
# make ISO_DIRECTORY if it does not already exist
if [ ! -d "$ISO_DIRECTORY" ]; then
    mkdir -p $ISO_DIRECTORY
fi;

# options to mount blank
MOUNT_OPTIONS=""

# turn off kernel generated messages
dmesg -n1

# Make a list of the electorate names
NUM_ELECS=`su - postgres -c"psql evacs <<EOF
SELECT COUNT(*) from electorate;
EOF"| sed 's/^ *//g' | tail -3 | head -1`

ELECS=`su - postgres -c"psql evacs <<EOF
SELECT name from electorate;
EOF"| sed 's/^ *//g' | tail -"$(($NUM_ELECS+2))" | head -"$NUM_ELECS"`

PP_CODE=`su - postgres -c"psql evacs <<EOF
SELECT  polling_place_code FROM server_parameter;
EOF"| sed 's/^ *//g' | tail -3 | head -1` 

PP_NAME=`su - postgres -c"psql evacs <<EOF
SELECT name FROM polling_place 
WHERE code=$PP_CODE;
EOF"| sed 's/^ *//g' | tail -3 | head -1`

ISO_IMAGE=$PP_NAME.iso

get_vote_count()
{ 
    join=''
    for ELECTORATE in $ELECS; do
	echo -n "$join"
	echo -n "$ELECTORATE: "
	echo "SELECT COUNT(*) FROM "${ELECTORATE}"_confirmed_vote;" |
	su - postgres -c "psql -p $PORT evacs" > $1 2>&1
	if grep -q 'psql' $1; then
	    echo -1
	else
	    tail -3 $1 | head -1 | sed "s/ //g"
	fi
	join=", "
    done

}

# DDSv1D-3.2: Display Backup Prompt
display_prompt_and_load_blank_cdrom()
{
    TMPFILE=`mktemp $TEMP_DIRECTORY/backup.XXXXXX`
    VOTES=`get_vote_count $TMPFILE`
    rm -f $TMPFILE
    text_mode $BRIGHT $BLUE $BLACK
    echo  "Votes in the $TYPE database: "
    text_mode $BRIGHT $CYAN $BLACK
    echo $VOTES
    text_mode $RESET $WHITE $BLACK
    
    load_blank_cdrom "Please insert CD-R for $TYPE and press ENTER:"
}

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


################################################################################
PASS=1
# DDSv1D-3.2: Get Required Number
while [ $PASS -le 2 ] ; do

        if [ $PASS = 1 ]; then
		PORT=$MASTER_PORT
		TYPE="master"
    	else
		PORT=$SLAVE_PORT
		TYPE="slave"
    	fi

    	# Export confirmed_vote tables into a temporary directory
    	# DDSv1D-3.2: Backup Confirmed Votes
    	# DDSv1D-3.2: Get Confirmed Vote
    	# DDSv1D-3.2: Write Confirmed Vote
	# generate a compound command to dump required tables:
	#     confirmed_vote table for each electorate
	#     server_parameter defining Polling Place location
	DUMP_CMD=''
	CONJUNCTION=""
	for ELECTORATE in $ELECS; do
	    DUMP_CMD=${DUMP_CMD}${CONJUNCTION}" pg_dump $DB_NAME -p $PORT -c -t ${ELECTORATE}_confirmed_vote"
            CONJUNCTION=" &&"
        done
 
	# add the command to dump the server_parameter table
	DUMP_CMD=${DUMP_CMD}${CONJUNCTION}" pg_dump $DB_NAME -p $PORT -c -t server_parameter"

        # announce the current dump action
	text_mode $BRIGHT $BLUE $BLACK
	echo -n Dumping `text_mode $BRIGHT $YELLOW $BLACK`$TYPE`text_mode $BRIGHT $BLUE $BLACK` ballot box for Polling Place:
	text_mode $BRIGHT $YELLOW $BLACK
	echo -n " $PP_NAME"
	text_mode $RESET $WHITE $BLACK
	echo

	# dump current database
	su - postgres -c " $DUMP_CMD " > $ISO_DIRECTORY/$TYPE.dmp
    	if [ $? != 0 ]; then
		# DDSv1D-3.2: Format Backup Error Message
		bailout "Backup of $TYPE database failed during $TYPE dump."
    	fi

	announce "Generating random number for $TYPE"

	# Generate the sum of the output file, plus random garbage so votes
	# not derivable from it.
	od -x -N128 < /dev/urandom > $ISO_DIRECTORY/$TYPE.rnd

	# Create disk image from dumped tables
	announce "Making disk image: $ISO_DIRECTORY/$ISO_IMAGE"
	mkisofs --quiet -r -J -V "$PP_NAME $TYPE"  -o "$ISO_IMAGE" $ISO_DIRECTORY  2>&1 > /dev/null
    	if [ $? != 0 ]; then
		# DDSv1D-3.2: Format Backup Error Message
		bailout "Backup of $TYPE database failed during generation of disk image."
    	fi

	# announce the number of votes;
	# prompt user to load a blank CD if not already loaded
    	display_prompt_and_load_blank_cdrom

	# Actually write to the disk
	announce "Writing $ISO_IMAGE to CDROM ($CDROM_DEVICE)"
	# SIPL 2011-08-09 Fedora 14 uses wodim, not cdrecord.
	# cdrecord dev=$CDROM_SCSI_DEVICE $CDROM_RECORD_OPTIONS -data "$ISO_IMAGE" 2>&1 > /dev/null
	wodim dev=$CDROM_DEVICE $CDROM_RECORD_OPTIONS -data "$ISO_IMAGE" 2>&1 > /dev/null
	if [ $? != 0 ]; then
		# DDSv1D-3.2: Format Backup Error Message
		bailout "Backup of $TYPE database failed during CD record phase."
    	fi

    	#Increment pass count
    	# DDSv1D-3.2: Check & Update Count
    	# DDSv1D-3.2: Update Count of Backups
    	let PASS=$PASS+1

	# Display the sum of the output files from the CD we just wrote.
	announce "The ballot box signature for ${TYPE}:"
	display_signature `cat $ISO_DIRECTORY/$TYPE.dmp $ISO_DIRECTORY/$TYPE.rnd | md5sum`

	eject $CDROM_DEVICE

	# Check $PASS = 2, as PASS was incremented just above.
        if [ $PASS = 2 ]; then
	    instruct "Please remove the CD-R, insert the CD-R for the slave backup, and press ENTER:"
	    read -s
	    delete_instruction
    	fi

	# remove this pass' artifacts
	rm -f $ISO_DIRECTORY/$TYPE.dmp || echo "Can't remove  $ISO_DIRECTORY/$TYPE.dmp" 
	rm -f $ISO_DIRECTORY/$TYPE.rnd || echo "Can't remove  $ISO_DIRECTORY/$TYPE.rnd" 

done

# finished
echo
announce "Thankyou.  End of Day Backup complete."

# turn kernel generated messages back on
dmesg -n4

exit 0
