import os
import array

def run(proj):
    #os.popen("mv "+proj+"classified  "+proj+"classified.old")
    #os.popen("mv "+proj+"classified.index  "+proj+"classified.index.old")
    #os.popen("mv "+proj+"extractedfile "+proj+"extractedfile.old")
    #os.popen("mv "+proj+"extractedfile.type "+proj+"extractedfile.type.old")
    #print classdat
    arr = array.array("L")
    sz = os.path.getsize(proj+"classified.old")
    print "SIZE", sz
    arr.fromfile(open(proj+"classified.index.old"), os.path.getsize(proj+"classified.index.old")/4)
    resarr = array.array("L")
    of = open(proj+"extractedfile", "w")
    oft = open(proj+"extractedfile.type", "w")
    it = open(proj+"classified", "w")
    imgf = open(proj+"extractedfile.old").read()
    imgft = open(proj+"extractedfile.type.old").read()
    classdat = open(proj+"classified.old").read()
    off = 0
    for repeat in range(20000):
        if repeat%100 == 0:
            print repeat
        of.write(imgf)
        oft.write(imgft)
        it.write(classdat)
        for item in arr:
            resarr.append(item+off)
        off += sz
    resarr.tofile(open(proj+"classified.index", "w"))
    


if __name__ == "__main__":
    run("../projects/a2/")
