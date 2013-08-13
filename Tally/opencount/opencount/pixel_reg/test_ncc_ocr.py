import shared as sh
import part_match as pm
import os
import numpy as np
from matplotlib.pyplot import show, imshow, figure, title

ballotDir = '../../test-ballots/small_orange/339_100/'
digitDir = '../../test-ballots/small_orange/digit-source/'
# load all digit patches
digit_hash = {}
digit_hash["0"] = sh.standardImread(os.path.join(digitDir,'0.png'),flatten=True)
digit_hash["1"] = sh.standardImread(os.path.join(digitDir,'1.png'),flatten=True)
digit_hash["2"] = sh.standardImread(os.path.join(digitDir,'2.png'),flatten=True)
digit_hash["3"] = sh.standardImread(os.path.join(digitDir,'3.png'),flatten=True)
digit_hash["4"] = sh.standardImread(os.path.join(digitDir,'4.png'),flatten=True)
digit_hash["5"] = sh.standardImread(os.path.join(digitDir,'5.png'),flatten=True)
digit_hash["6"] = sh.standardImread(os.path.join(digitDir,'6.png'),flatten=True)
digit_hash["7"] = sh.standardImread(os.path.join(digitDir,'7.png'),flatten=True)
digit_hash["8"] = sh.standardImread(os.path.join(digitDir,'8.png'),flatten=True)
digit_hash["9"] = sh.standardImread(os.path.join(digitDir,'9.png'),flatten=True)

bbSearch = [260,340,1080,1260]
I = sh.standardImread(os.path.join(ballotDir,'339_1004_4_165_1.png'))
#imshow(I[bbSearch[0]:bbSearch[1],bbSearch[2]:bbSearch[3]]);show()

# generate image list
imList = []
for root, dirs, files in os.walk(ballotDir):
    for f in files:
        (f0,ext)=os.path.splitext(f)
        if ext != '.png':
            continue
        p1=os.path.join(root,f)
        imList.append(p1)
        
results = pm.digitParse(digit_hash,imList,bbSearch,7, hspace=20)
for r in results:
    print r[0], ",", r[1]
    # r[0]: filename
    # r[1]: ocr string
    # r[2]: list of numpy patches
    # r[3]: list of 4-tuple coordinates of patches
    # r[4]: list of scores for each digit


badresult = results[7]
extracted = badresult[2]
combined = np.ones((1,1))
for p in extracted:
    combined = sh.joinImages(combined,p)

figure(0);
# show incorrect result
imshow(combined);title(badresult[1] + '\n' + badresult[0] + '\n initially incorrect');

# now provide user input to reject a label at a location
#
I = sh.standardImread(badresult[0],flatten=True);
Ic=I[bbSearch[0]:bbSearch[1],bbSearch[2]:bbSearch[3]]
rejected_hash={}
# specify bounding box on the '6' as incorrect
rejected_hash['6']=badresult[3][3]
(ocr_str,extracted,bbs,scores)=pm.pm1(digit_hash,Ic,7,20,rejected_hash=rejected_hash)

combined = np.ones((1,1))
for p in extracted:
    combined = sh.joinImages(combined,p)

figure(1);
# show corrected result
imshow(combined);title(ocr_str + '\n' + '\n fixed');

show()
