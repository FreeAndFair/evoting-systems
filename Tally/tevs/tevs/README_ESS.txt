The ESS ballot design has a couple of particularities.

First, some text is presented as black over halftoned gray.
This would cause problems for OCR, so the halftoned areas are
thresholded prior to being OCR'd.  The PIL Image.eval function
is used.

Second, there are two different ways in which contests are established.

Contests may be titled in black on halftone, in which case the 
following white area contains votes.  The votes may be located by
looking for ovals in the oval column.

However, YES or NO contests are presented with flush left text
in the white area, followed by YES and NO ovals and words.  These
are located by a different mechanism.

If your ballot has a different design, you may need to modify this code.
