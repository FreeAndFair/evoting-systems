# This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd

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
# Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA

# This file contains definitions and utilities for loading
# CDROMs

# cdrom.sh exports:
#           $CDROM_DEVICE
#           $CDROM_DIRECTORY
#           $CDROM_SCSI_DEVICE
#           $CDROM_RECORD_OPTIONS
#           load_blank_cdrom()
#           load_evacs_cdrom()

# source the console library unless it has already been loaded
if [ -z $CONSOLE ]; then
   # set SCRIPTROOT if not already set
    if [ -z $SCRIPTROOT ]; then
	SCRIPTROOT=/opt/eVACS/bin
    fi
    source "$SCRIPTROOT/console.sh" && CONSOLE='loaded'
fi

# 2011-05-20 /dev/cdrom may now be a symbolic link.  Follow it, so
# that the subsequent grep for $CDROM_DEVICE in the output of mount
# can succeed.
CDROM_DEVICE=`readlink -e /dev/cdrom`

# SIPL 2011-07-28 Fedora 14 uses wodim, not cdrecord.
#   wodim prefers the device name directly (/dev/sr0)
#   instead of the SCSI name.
# Command to find out the CD's SCSI device was:
#CDROM_SCSI_DEVICE=`cdrecord -scanbus 2>&1 | egrep "[0-9\,]{5}\s*[0-9)]*" | fgrep -v '*' | cut -b2-6`
# But this didn't deal with 1001,1,0 (wrong argument to cut)
# New improved version follows; deals with both 0,0,0 and 1001,1,0
# Note the following line contains strategically-placed
# space and tab characters
#CDROM_SCSI_DEVICE=`cdrecord -scanbus 2>&1 | egrep "	[0-9\,]+[ 	]+[0-9)]+ [^*]"|awk -F\  '{print $1}'`
CDROM_DIRECTORY=/mnt/cdrom
# SIPL 2011-07-28 -tao is assumed, if not specified.
#   -tao does seem to work, but try -dao anyway.
CDROM_RECORD_OPTIONS=" -dao -eject gracetime=0 "
MOUNT_OPTIONS=""

# make mount point if necessary
[ -d $CDROM_DIRECTORY ] || mkdir $CDROM_DIRECTORY || \
    bailout "Can't create directory $CDROM_DIRECTORY" 

# SIPL 2011-07-22 New function to "ping" the CD drive
# so that a following mount command
# will not fail prematurely.  Seven seconds seems to be just
# long enough for the HP drive in the new hardware.
# Even so, the HP drive can require repeated "pings";
# the code below represents the "worst case" actually observed
# during testing of this hardware.
ping_cdrom()
{
    eject -t $CDROM_DEVICE
    sleep 8 
    # This first call may fail immediately . . .
    /sbin/blkid -p $CDROM_DEVICE > /dev/null 2>&1
    # . . . but after sleeping . . .
    sleep 7
    # . . . the second try may work . . .
    /sbin/blkid -p $CDROM_DEVICE > /dev/null 2>&1
    # . . . but sometimes a third try is required.
    sleep 2
    /sbin/blkid -p $CDROM_DEVICE > /dev/null 2>&1
}

# return when there is a blank CDROM in the drive
load_blank_cdrom()
{
msg="$@"
# SIPL 2011-07-22 "Ping" the CD drive.
ping_cdrom

# SIPL 2011-07-28 Things have changed.  In RedHat 9:
#  If user has already loaded the blank disk, mount will fail with the message:
#  "mount: you must specify the filesystem type"
# But in Fedora 14, the error message is:
#  "mount: /dev/sr0: can't read superblock".
# CAVEAT - entering a non data disk will also generate this error
# so an audio disk will pass this test but fail at cdrecord
mounted=`mount $MOUNT_OPTIONS $CDROM_DEVICE $CDROM_DIRECTORY 2>&1 | grep "can't read superblock"`
# if mount command succeeded, disk is not blank
success=`mount | grep $CDROM_DEVICE`
if [ -n "$success" ]; then
    warn "Currently loaded disk is not blank"
    umount $CDROM_DEVICE 2>&1 > /dev/null
fi
while [ -z "$mounted"  ]; do
    eject $CDROM_DEVICE
    instruct "$msg"
    read -s
    # replace highlighted instruction with default colours
    delete_instruction
    announce "CD loading                                                   "

    # SIPL 2011-07-22 "Ping" the CD drive.
    ping_cdrom

    mounted=`mount $MOUNT_OPTIONS $CDROM_DEVICE $CDROM_DIRECTORY 2>&1 | grep "can't read superblock"`    
    # if mount command succeeded, disk is not blank
    success=`mount | grep $CDROM_DEVICE`
    if [ -n "$success" ]; then
	warn "Currently loaded disk is not blank"
	umount $CDROM_DEVICE 2>&1 > /dev/null
    fi
done

}

# return when a CD is loaded that satisfies current $MOUNT_OPTIONS 
load_evacs_cdrom()
{
    msg="$@"

    # SIPL 2011-07-22 "Ping" the CD drive.
    ping_cdrom

    mounted=`mount $MOUNT_OPTIONS $CDROM_DEVICE $CDROM_DIRECTORY 2>&1`
    success=`mount | grep $CDROM_DEVICE`
    # give the user some feedback if mount failed
#    echo $mounted | grep "wrong fs type" && warn "Loaded CD does not appear to be an evacs disk."
#    echo $mounted | grep "No medium found" && warn "CD not detected. "
	error=`echo $mounted | grep "wrong fs type"` && warn "Loaded CD does not appear to be an evacs disk."
	error=`echo $mounted | grep "No medium found"` && warn "CD not detected. "
    
    while  [ -z "$success" ]; do
	eject $CDROM_DEVICE
	instruct "$msg"
	read -s
	# replace highlighted instruction with default colours
	delete_instruction
	announce "CD loading                                                      "

        # SIPL 2011-07-22 "Ping" the CD drive.
        ping_cdrom

        # attempt to mount cd
	mounted=`mount $MOUNT_OPTIONS $CDROM_DEVICE $CDROM_DIRECTORY 2>&1`
	success=`mount | grep $CDROM_DEVICE`

	# give the user some feedback if mount failed
	error=`echo $mounted | grep "wrong fs type"` && warn "Loaded CD does not appear to be an evacs disk."
#	echo $mounted | grep "wrong fs type" >  && warn "Loaded CD does not appear to be an evacs disk."
	error=`echo $mounted | grep "No medium found"` && warn "CD not detected. "
    done
}
