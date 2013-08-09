/* This file is (C) copyright 2001 Software Improvements, Pty Ltd */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <common/barcode.h>
#include <common/authenticate.h>
#include <common/http.h>
#include "message.h"
#include "voting_client.h"
#include "initiate_session.h"
#include "verify_barcode.h"
#include <common/voter_electorate.h>

static struct barcode *once_swiped;
static unsigned int misread_count = 0;

/* DDS3.2.4: Verify Checksum */
static bool verify_checksum(struct barcode *barcode)
{
	unsigned char checksum;
	
	/* get checksum and data from ascii encoding */ 
	if (!bar_decode_ascii(barcode)) return false;

	checksum = gen_csum(barcode);
	if (checksum == barcode->checksum) {
		return true;
	}
	else {
		return false;
	}	
}


/* DDS3.2.4: Store Barcode */
static void store_barcode(struct barcode *barcode)
{
	once_swiped = malloc(sizeof(struct barcode));
	/* SIPL 2011: Added casts to conform to strcpy() parameter types. */
	/* strcpy(once_swiped->data, barcode->data); */
        strcpy((char *)once_swiped->data, (char *)barcode->data);
	once_swiped->checksum = barcode->checksum;
	strcpy(once_swiped->ascii, barcode->ascii);
}


/* DDS3.2.4: Verify Initial Barcode */
bool verify_init_barcode(struct barcode *barcode)
{
	bool ChecksumOK;
	enum error err;
	struct electorate *electorate;

	ChecksumOK = verify_checksum(barcode);
	if (ChecksumOK == false) {
		return false;
	} else {
		err = authenticate(barcode, &electorate);
		if (err != ERR_OK)
			display_error(err);
		store_electorate(electorate);
		store_barcode(barcode);
		return true;
	}		
}

/* DDS3.2.22: Increment Misread Count */
static void inc_misread_count(void)
{
	misread_count++;
	if (misread_count >= 2)
		display_error(ERR_BARCODE_MISREAD);
}

/* DDS3.2.22: Verify Barcode */
bool verify_barcode(struct barcode *bc)
{
	assert(once_swiped);
	if (verify_checksum(bc)) {
		/* This must be the barcode they used to start */
		if (strcmp(bc->ascii, once_swiped->ascii) != 0)
			display_error(ERR_BARCODE_MISMATCH);
		return true;
	}

	/* Barcode misread */
	inc_misread_count();
	return false;
}
	
                                                                        
