import os
import sys
import subprocess
import uuid
import re
import logging

import const
import util

class OCRException(Exception):
    "Raised if OCR fails"
    pass

log = logging.getLogger('')

#XXX choice of OCR routine should be in config
_devnull = open("/dev/null", "w")
def tesseract(zone):
    "run the tesseract ocr engine on Image zone"
    #So we can run this function simultaneously from
    #multiple processes without fear of collisions
    badge = uuid.uuid4().hex
    ft = "/tmp/region-" + badge
    try:
        zone.save(ft + ".tif")
        p = subprocess.Popen(
            [
                "/usr/local/bin/tesseract", #XXX location should be in cfg 
                ft + ".tif", 
                ft
            ],
            stdin  = _devnull,
            stdout = _devnull,
            stderr = subprocess.PIPE
        )
        err = p.stderr.read()
        sts = os.waitpid(p.pid, 0)[1]
        if sts != 0 or len(err) > 100:
            log.error(err)
            raise OCRException("OCR failed")
        text = util.readfrom(ft + ".txt")
    finally:
        for p in (".tif", ".txt"):
            util.rmf(ft + p)
    return "".join(c for c in text if ord(c)<128)

#XXX choice of OCR text cleaner should be config
_scrub = re.compile(r'[^a-zA-Z0-9_ /]+')
def clean_ocr_text(text):
    "remove common ocr artifacts"
    text = text.strip(
              ).replace("\n",   "/"
              ).replace(",",    "comma"
              ).replace("'",    'squot' #XXX remove these two: make serializers do their own escaping
              ).replace('"',    'dquot'
              ).replace('\/',   '(M)'
              ).replace("IVI",  "(M)IVI"
              ).replace("|(M)", "(M)"
              ).replace("I(M)", "(M)"
              ).replace("(M)|", "M"
              ).replace("(M)I", "M"
              ).replace("|",    "I"
           )
    return _scrub.sub('', text)

