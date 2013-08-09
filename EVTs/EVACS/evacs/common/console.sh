# This file contains console  definitions used to provide text mode 
# escape sequences for a vt100 

# console.sh exports: 
#          text_mode(MODE FGCOLOUR BGCOLOUR)
#          bailout(msg)
#          warn(msg)
#          announce(msg)
#          instruct(msg)
#          delete_instruction()
#          modes and colours directly below:
RESET=0
BRIGHT=1
DIM=2
UNDERLINE=4
BLINK=5
REVERSE=7
HIDDEN=8

BLACK=0
RED=1
GREEN=2
YELLOW=3
BLUE=4
MAGENTA=5
CYAN=6
WHITE=7

# SIPL 2011-08-12 DELETE_STRING was:
#DELETE_STRING="\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
# But now just use a carriage return to move to the beginning of the line,
# and the (ANSI) escape sequence to clear to the end of the line.
# This works better under screen
# (i.e., on the voting server), as a backspace under screen wraps backwards
# to the previous line!
DELETE_STRING="\r$(tput el)"

# set text colours
text_mode() {
    MODE=$1
    FG=$(($2+30 ))
    BG=$(($3+40 ))
#    echo "$MODE $FG $BG"
    echo -en "\033[$MODE;$FG;${BG}m"
}

bailout()
{
    warn "FATAL ERROR: $@" >&2
    # turn on kernel messages
    dmesg -n4
    # fix cursor colour
    echo -n
    # die
    exit 1
}

#print a red warning message
warn()
{
    text_mode $BRIGHT $RED $BLACK
    echo "$@" >&2
    text_mode $RESET $WHITE $BLACK
    echo -n
}

# Print a message in blue
announce()
{
    text_mode $BRIGHT $BLUE $BLACK
    echo "$@" >&2
    text_mode $RESET $WHITE $BLACK
    # fix cursor colour
    echo -n
}

# print a message in reverse yellow with no new line
instruct()
{
    text_mode $REVERSE $YELLOW $BLACK
    text_mode $BRIGHT $YELLOW $BLACK
    echo -n  "$@" >&2
    text_mode $RESET $WHITE $BLACK
    # fix cursor colour
    echo -n
}

# replace highlighted instruction with default colours
delete_instruction()
{
    echo -ne $DELETE_STRING
}

# initialise text mode  
text_mode $RESET $WHITE $BLACK
