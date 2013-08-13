import optparse
import doExtract
from os.path import join as pathjoin

def main():
    usage = 'python my_extract.py csvpath templatepath samplesdir outdir'
    parser = optparse.OptionParser(usage=usage)
    options, args = parser.parse_args()
    if not args:
        csvpath = pathjoin('erictest', '1_doctored_front_targetlocs.csv')
        templatepath = pathjoin('erictest', '1_doctored_front.png')
        samplesdir = pathjoin('erictest', 'samples')
        outdir = 'erictest_out'
    else:
        csvpath, templatepath, samplesdir, outdir = args
    doExtract.convertImages(csvpath, templatepath, samplesdir, outdir)

if __name__ == '__main__':
    main()
