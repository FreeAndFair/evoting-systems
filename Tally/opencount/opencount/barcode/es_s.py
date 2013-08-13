import os, time
import cv

def decode_patch(original_image, original_mark, expected_bits):
    """
    Given a ES&S-style ballot, returns the LHS barcode as a bitstring 
    if one is found, along with bounding box of each digit in the barcode.
    The algorithm works by finding finding the column of timing marks on 
    the left side of the ballot and looking at the intensity of pixels
    just to the right of each of them to detect "on" or "off" bits.
    Input:
        original_image : cv image of ballot
        original_mark  : cv image of mark
        expected_bits  : number of bits expected in barcode
    Output:
        bitstring : string representation of barcode (ex: "100110...")
        locations : {bit_value: [(x1,y1,x2,y2), ...]}
    """

    # pixels for resized mark, image will be scaled down by same ratio
    resized_mark_height = 15  # will not match if lower than ~10

    # left portion of page to template match (ex: 5 means 1/5 of page)
    portion = 5               # error if more than ~6 

    mark_w,mark_h = cv.GetSize(original_mark)
    scaling = float(resized_mark_height)/mark_h
    w = int(round(mark_w * scaling))
    h = int(round(mark_h * scaling))
    resized_mark = cv.CreateImage((w, h), 8, 1)
    cv.Resize(original_mark, resized_mark)

    image_W, image_H = cv.GetSize(original_image)
    cv.SetImageROI(original_image, (0, 0, int(round(image_W/portion)), image_H))
    W = int(round(image_W / portion * scaling))
    H = int(round(image_H * scaling))
    resized_image = cv.CreateImage((W, H), 8, 1)
    cv.Resize(original_image, resized_image)
    width = W - w + 1
    height = H - h + 1
    match_mat = cv.CreateImage((width, height), 32, 1)
    cv.MatchTemplate(resized_image, resized_mark, match_mat, cv.CV_TM_CCOEFF_NORMED)
    cv.ResetImageROI(original_image)

    # find all possible match locations
    best_column = 0
    most_matches = 0
    possible = []
    for x in range(width):
        column_matches = 0
        for y in range(height):
            if match_mat[y,x] > 0.6:
                possible.append((y,x))
                column_matches += 1
        if column_matches > most_matches:
            most_matches = column_matches
            best_column = x
    f1 = filter(lambda p: p[1] < best_column + w, possible)
    f1 = sorted(f1, key=lambda z: z[0])
    if not f1:
        return (None, None)

    # filter match locations
    last_location = f1[0]
    last_max = match_mat[f1[0][0], f1[0][1]]
    locations = []
    for p in f1[1:]:
        y, x = p
        r = match_mat[y,x]
        if y > last_location[0] + h:
            locations.append(last_location)
            last_max = r
            last_location = p
            continue
        if r > last_max:
            last_max = r
            last_location = p
    locations.append(last_location)
    locations = locations[1:-1]
    if len(locations) != expected_bits:
        return (None, None)

    # detect mark to the right of the timing marks
    y0, x0 = locations[0]
    thresh = 0
    black = 0
    white = 0
    for x in range(x0,x0+w):
        black += resized_image[y0+h/2, x]
        white += resized_image[y0-h/2, x]
    thresh = 0.7*white + 0.3*black
    bitstring = ''
    bit_locations = {}
    for (y, x) in locations:
        intensity = 0
        x_start = x + (2*w)
        x_end = x_start + w
        digit = ''
        for x_check in range(x_start, x_end):
            intensity += resized_image[y+(h/2), x_check]
        digit = '1' if (intensity < thresh) else '0'
        bitstring += digit
        resized_locations = [x_start, y, x_end, y+h]
        total_intensity = 0
        if digit == '0':
            # check for stray marks
            for x1 in range(x_start, x_end):
                for y1 in range(y, y+h):
                    total_intensity += resized_image[y1, x1]
            if total_intensity < 255 * 0.99 * w * h:
                return (None, None)
        mark_location = tuple([int(round(z/scaling)) for z in resized_locations])
        bit_locations.setdefault(digit, []).append(mark_location)
    return bitstring, bit_locations

def decode(imgpath, mark, bits):
    """
    Given a ES&S-style ballot, returns the LHS barcode as a bitstring. 
    Will try to detect and report flipped ballots.
    Input:
        imgpath : path to ballot image
        mark    : image of mark
        bits    : number of bits expected in barcode
    Output:
        bitstring     : string for detected barcode
        is_flipped    : boolean indicating whether ballot was flipped
        bit_locations : {str bit_value: [(x1,y1,x2,y2), ...]}
    """

    is_flipped = False
    img = cv.LoadImage(imgpath, cv.CV_LOAD_IMAGE_GRAYSCALE)
    bitstring, bit_locations = decode_patch(img, mark, bits)
    if not bitstring:
        is_flipped = True
        w, h = cv.GetSize(img)
        tmp = cv.CreateImage((w,h), img.depth, img.channels)
        cv.Flip(img, tmp, flipMode=-1)
        img = tmp
        bitstring, bit_locations = decode_patch(img, mark, bits)
    return bitstring, is_flipped, bit_locations

def build_bitstrings(img_bit_locations, expected_bits):
    """
    For each ballot, build bitstring from the locations of the barcode digits.
    Input:
        img_bit_locations : {imgpath: [(bit_value, y), ...]}
        expected_bits     : number of bits expected in the bitstring
    Output:
        img_decoded_map : {imgpath: bitstring}
    """

    img_decoded_map = {}
    for imgpath, tups in img_bit_locations.iteritems():
        tups_sorted = sorted(tups, key=lambda x: x[1])
        decoding = ''.join([str(tup[0]) for tup in tups_sorted])
        assert len(decoding) == expected_bits
        img_decoded_map[imgpath] = decoding
    return img_decoded_map

def get_info(bitstring):
    """
    Converts the barcode bitstring to dictionary with info about the ballot.
    Input:
        bitstring : string representation of barcode on ballot
    Output:
        info : {infotype: value}
    """

    info = {'page': 0}  # TODO: change once barcode meaning is understood
    return info

def isimgext(f):
    return os.path.splitext(os.path.split(f)[1])[1].lower() in ('.png', '.bmp', '.jpg')

def main():
    imgpath = "merced2.jpg" 
    mark_path = "ess_mark.png"
    bits = 36
    trials = 1

    start = time.time()
    mark = cv.LoadImage(mark_path, cv.CV_LOAD_IMAGE_GRAYSCALE)
    for i in range(trials):
        bitstring, is_flipped, bit_locations = decode(imgpath, mark, bits)
    print "%s\t%s\t%s" % (imgpath, is_flipped, bitstring)
    print "Time/ballot: %s" % str((time.time() - start)/trials)

    print "\nTesting build_bitstrings():"
    img_bc_temp = {}
    if not bit_locations:
        return None
    for bit_value, tups in bit_locations.iteritems():
        for (x1, y1, x2, y2) in tups:
            img_bc_temp.setdefault(imgpath, []).append((bit_value, y1))
    img_decoded_map = build_bitstrings(img_bc_temp, bits)
    print img_decoded_map


if __name__ == '__main__':
    main()

