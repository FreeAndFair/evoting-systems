/*  */
/* This material is subject to the VoteHere Source Code Evaluation */
/* License Agreement ("Agreement").  Possession and/or use of this */
/* material indicates your acceptance of this Agreement in its entirety. */
/* Copies of the Agreement may be found at www.votehere.net. */
/*  */
/* Copyright 2004 VoteHere, Inc.  All Rights Reserved */
/*  */
/* You may not download this Software if you are located in any country */
/* (or are a national of a country) subject to a general U.S. or */
/* U.N. embargo or are deemed to be a terrorist country (i.e., Cuba, */
/* Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States */
/* (each a "Prohibited Country") or are otherwise denied export */
/* privileges from the United States or Canada ("Denied Person"). */
/* Further, you may not transfer or re-export the Software to any such */
/* country or Denied Person without a license or authorization from the */
/* U.S. government.  By downloading the Software, you represent and */
/* warrant that you are not a Denied Person, are not located in or a */
/* national of a Prohibited Country, and will not export or re-export to */
/* any Prohibited Country or Denied Party. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <vhti/support.h>
#include "test-misc.h"

char *snarf (const char *fn_first_part,
             const char *fn_second_part)
{
   char *fullname = VHTI_alloc (strlen (fn_first_part) + strlen (fn_second_part) + 1);
   char *contents = NULL;
   char *return_value = NULL;
   FILE *fh = NULL;
   struct stat stat_buf;

   strcpy (fullname, fn_first_part);
   strcat (fullname, fn_second_part);

   if (0 != stat (fullname, &stat_buf))
   {
      perror (fullname);
      goto cleanup;
   }

   contents = VHTI_alloc (stat_buf.st_size + 1);

   fh = fopen (fullname, "rb");
   if (NULL == fh)
   {
      perror (fullname);
      goto cleanup;
   }

   if (stat_buf.st_size != (off_t)(fread (contents, sizeof (char), stat_buf.st_size, fh)))
   {
      perror ("Read too few characters");
      goto cleanup;
   }
   contents[stat_buf.st_size] = '\0';

   return_value = contents;
   contents = NULL;

 cleanup:
   if (NULL == return_value)
      fprintf (stderr, "You probably need to run the Perl examples; I get all my test data from their outputs.\n");

   free (fullname);
   free (contents);
   if (fh)
   {
      if (0 != fclose (fh))
      {
         perror ("closing filehandle");
      }
   };

   if (!return_value)
      exit (1);

   return return_value;
}
