from PIL import Image, ImageDraw
import os, sys, pdb, traceback
import time
import random
sys.path.append('..')
try:
    from collections import Counter
except ImportError as e:
    from util import Counter
import multiprocessing as mp
import cPickle as pickle
import itertools
import time
from grouping.partask import do_partask
from vendors import Vendor
import threading
import util
import wx
from wx.lib.pubsub import Publisher
import numpy as np
from scipy.optimize import fmin
import specify_voting_targets.select_targets

def pdb_on_crash(f):
    """
    Decorator to run PDB on crashing  
    """
    def res(*args, **kwargs):
        try:
            return f(*args, **kwargs)
        except:
            import pdb as err_pdb
            err_pdb.post_mortem()
    return res

black = 200

do_save = True
do_test = True
export = False

flipped = {}

#@pdb_on_crash
def num2pil(img):
    pilimg = Image.new("L", (len(img[0]), len(img)))
    pilimg.putdata([item for sublist in img for item in sublist])
    return pilimg

def load_pil(path):
    pilimg = Image.open(path)
    pilimg = pilimg.convert("L")
    #print 'loading', path
    #print 'isflipped', flipped
    if flipped != {} and flipped[path]:
        pilimg = pilimg.transpose(Image.ROTATE_180)
    return pilimg

def load_num(path="", pilimg=None):
    if pilimg == None:
        pilimg = load_pil(path)
    width, height = pilimg.size
    data = list(pilimg.getdata())
    data = [data[x:x+width] for x in range(0,width*height,width)]
    #print width, height
    return data

def load_threshold(image):

    def dorem(dat, block, boxes, replacewith=False):
        remove = []
        for x,y in boxes:
            if (x,y-block) in boxes and (x,y+block) in boxes:
                if (x-block,y) in boxes and (x+block,y) in boxes:
                    remove.append((x,y))
        for x,y in remove:
            for dy in range(block):
                for dx in range(block):
                    dat[y+dy][x+dx] = replacewith


    dat = load_num(image)
    block = 40
    boxes = {}
    for y in range(0, len(dat)-block, block):
        for x in range(0, len(dat[y])-block, block):
            if sum(dat[y+dy][x+dx] < 240 for dy in range(0,block,4) for dx in range(0,block,4)) > block/4*block/4*3/10:
                lst = [dat[y+dy][x+dx] < 240 for dy in range(0,block) for dx in range(0,block)]
                if sum(lst) > block*block*7/10:
                    boxes[x,y] = True
    dorem(dat, block, boxes, replacewith=255)

    dat = [[x < black for x in y] for y in dat]
    block = 10
    boxes = {}
    for y in range(0,len(dat)-block, block):
        for x in range(0,len(dat[y])-block, block):
            if sum(dat[y+dy][x+dx] for dy in range(0,block,2) for dx in range(0,block,2)) > block/2*block/2*5/10:
                filled = sum(dat[y+dy][x+dx] for dy in range(block) for dx in range(block)) > block*block*9/10
                if filled:
                    boxes[x,y] = True

    dorem(dat, block, boxes, replacewith=255)
    
    dat = [[0 if x else 255 for x in y] for y in dat]
    if do_save and False:
        # TODO: This assumes that the dir 'tmp/' exists.
        load_pil(image).save(tmp+"/%s-a.png"%image.split("/")[1])
        num2pil(dat).save(tmp+"/%s-b.png"%image.split("/")[1])
    return dat

def find_lines(data):
    """
    Find all the lines we can on the image.

    For each pixel, if it is black:
        (1) Extend up and down as far as possible. Call those
              pixels part of one line.
        (2) Extend left and right as far as possible. Call those
              pixels part of one line.
        (3) Mark the lined pixels as 'used'.
    
    When extending, first move to the middle of the line. Then,
    do a DFS search going in the direction of the line, but only
    in the given direction.

    In order to improve efficiency, only test the black pixels on a grid.
    """
    height, width = len(data), len(data[0])
    def extend_ud(point):
        y, x = point
        while 0 < y and data[y][x] < black: y -= 1
        upper_y = y
        y, x = point
        low = len(data)
        while y < low and data[y][x] < black: y += 1
        lower_y = y
        return upper_y, lower_y
    def extend_lr(point):
        y, x = point
        while 0 < x and data[y][x] < black: x -= 1
        left_x = x
        y, x = point
        right = len(data[y])
        while x < right and data[y][x] < black: x += 1
        right_x = x
        return left_x, right_x

    def full_extend_ud(point):
        y, x = point
        l,r = extend_lr((y,x))
        x = (l+r)/2 if l+r<20 else x
        u1,d1 = extend_ud((y,x))
        return u1,d1

    def full_extend_lr(point):
        y, x = point
        u,d = extend_ud((y,x))
        y = (u+d)/2 if u+d<20 else y
        l1,r1 = extend_lr((y,x))
        return l1,r1

    LST = []
    def full_extend_lr_2(point):
        u,d = extend_ud(point)
        if d-u < 20: y = (u+d)/2
        else: y = point[0]
        point = (y,point[1])

        lower = max(y-10,0)
        upper = min(y+10,height)

        seen = []

        q = [point[0]]
        x = point[1]-1
        while q and x > 0:
            q = list(set([dy+y for y in q for dy in [-1, 0, 1] if lower <= dy+y < upper and data[dy+y][x] < black]))
            seen.extend(q)
            #LST.extend([(x,y) for y in q])
            x -= 1
        l = x
        q = [point[0]]
        x = point[1]+1
        while q and x < width:
            q = list(set([dy+y for y in q for dy in [-1, 0, 1] if lower <= dy+y < upper and data[dy+y][x] < black]))
            seen.extend(q)
            #LST.extend([(x,y) for y in q])
            x += 1
        r = x
        yy = sum(seen)/len(seen) if len(seen) else point[0]
        return yy,(l,r)

    def full_extend_ud_2(point):
        l,r = extend_lr(point)
        if r-l < 20: x = (l+r)/2
        else: x = point[1]
        point = (point[0],x)

        lower = max(x-10,0)
        upper = min(x+10,width)

        seen = []

        q = [point[1]]
        y = point[0]-1
        while q and y > 0:
            q = list(set([dx+x for x in q for dx in [-1, 0, 1] if lower <= dx+x < upper and data[y][dx+x] < black]))
            seen.extend(q)
            #LST.extend([(x,y) for y in q])
            y -= 1
        u = y
        q = [point[1]]
        y = point[0]+1
        while q and y < height:
            q = list(set([dx+x for x in q for dx in [-1, 0, 1] if lower <= dx+x < upper and data[y][dx+x] < black]))
            seen.extend(q)
            #LST.extend([(x,y) for y in q])
            y += 1
        d = y
        yy = sum(seen)/len(seen) if len(seen) else point[1]
        return yy,(u,d)

    foundy = {}
    foundx = {}
    lines = []
    YSKIP = 15
    XSKIP = 40
    for y in range(0,height,1):
        for x in range(0,width,1) if y%YSKIP == 0 else range(0,width,XSKIP):
            if not data[y][x] < black: 
                #data[y][x] = black
                continue
            if y%YSKIP == 0 and (y/3,x/3) not in foundy:
                u,d = full_extend_ud((y,x))
                if d-u > 30:
                    xx,(u,d) = full_extend_ud_2((y,x))
                    if d-u > 30:
                        for dx in range(-10, 10, 3):
                            for q in range(u,d):
                                foundy[q/3,(xx+dx)/3] = True
                        lines.append(("V", (xx-3,u,xx+3,d)))

            if x%XSKIP == 0 and (y/3,x/3) not in foundx:
                #print 'h', newy, y, x
                yy,(l,r) = full_extend_lr_2((y,x))
                if r-l > 30:
                    for dy in range(-10, 10, 3):
                        for q in range(l,r):
                            foundx[(yy+dy)/3,q/3] = True
                    #print 'line starting from', x, y, data[y][x]
                    #LST.append((x-3,y-3,x+3,y+3))
                    #LST.append((l,y,r,y))
                    lines.append(("H", (l,yy-3,r,yy+3)))
    
    if do_save and False:
        num2pil(data).save(tmp+"/it.png")
        ct = Counter(LST)
        im = Image.new("RGB", (width, height), (255,255,255))
        d = ImageDraw.Draw(im)
        LST = list(set(LST))
        for each in LST:
            if len(each) == 4:
                d.rectangle(each, fill=(0,0,0))
            else:
                d.point(each, fill=(ct[each],0,0))                
        im.save(tmp+"/asdf.png")

        im = Image.new("L", (width, height), 255)
        d = ImageDraw.Draw(im)
        for i in range(len(data)):
            for j in range(len(data[i])):
                if data[i][j] < black:
                    d.point((j,i), fill=0)
        im.save(tmp+"/asdf2.png")
    

    #print len(lines)
    #print lines
    return lines


def intersect(line1, line2):
    """
    Compute the intersection of two bounding boxes.
    """
    top = max(line1[1], line2[1])
    bottom = min(line1[3], line2[3])
    left = max(line1[0], line2[0])
    right = min(line1[2], line2[2])
    if bottom > top and right > left:
        return left, top, right, bottom
    else:
        return None
def union(line1, line2):
    """
    Compute the union of two bounding boxes.
    """
    top = min(line1[1], line2[1])
    bottom = max(line1[3], line2[3])
    left = min(line1[0], line2[0])
    right = max(line1[2], line2[2])
    return left, top, right, bottom

def dfs(graph, start):
    """
    Run a DFS search on a graph starting at a given vertex.
    Return the list of seen graphs.
    """
    s = [start]
    seen = {}
    while s != []:
        top = s.pop()
        if top in seen: continue
        seen[top] = True
        s += graph[top]
    return seen.keys()

@pdb_on_crash
def extend_to_line(lines, width, height):
    table = [[False]*(width+200) for _ in range(height+200)]
    for d,each in lines:
        if d == 'V':
            (l,u,r,d) = each
            for x in range(l,r):
                for y in range(u,d):
                    table[y][x] = True

    print "RECTANGLE FIX", len(lines)

    new = []
    for direc,each in lines:
        if direc == 'H':
            l,u,r,d = each
            if any(table[u][x] for x in range((l+9*r)/10,r)):
                new.append((direc,each))
            else:
                pos = [x for x in range((l+9*r)/10,min(r+(r-l)/2,width)) if table[u][x]]
                if len(pos):
                    new.append((direc, (l,u,pos[0]+(pos[0]-l)/10,d)))
                else:
                    new.append((direc, (l,u,r,d)))
        else:
            new.append((direc,each))

    print len(new)

    return new


def to_graph(lines, width, height, minsize, giventargets):
    """
    Convert a set of lines to graph where lines are vertexes, and
    there is an edge between two lines when they intersect. This
    prepares for finding all rectangles.

    First, we need to find lines which were accidentally split in to
    pieces, and merge them together. That is, if there are two
    horizontal lines which intersect, or two vertical lines which
    intersect, then merge them in to one line of the union of the two.
    
    We do this by making another graph of all horizontal lines and 
    adding edges between the lines when they touch. Then we run a
    connnected components algorithm over it and take the union.
    This is done by creating an width*height array, storing where all
    of the lines are, and finding when they touch.

    Then it is easy to do an all-pairs algorithm to find the intersecting
    vertical and horizontal lines.
    """
    print width, height

    # Extend the lines.
    def extend(line):
        if line[0] == 'V':
            l, u, r, d = line[1]
            ext = int(round((d-u)*0.02))
            return ('V', (l, u-ext if u-ext >= 0 else 0, r, d+ext if d+ext < height else height-1))
        if line[0] == 'H':
            l, u, r, d = line[1]
            ext = int(round((r-l)*0.02))
            return ('H', (l-ext if l-ext >= 0 else 0, u, r+ext if r+ext < width else width-1, d))

    for _ in range(2):
        print "THERE ARE", len(lines)
        lines = map(extend, lines)
    
        for direction in ['H', 'V']:
            table = [[None]*(width+200) for _ in range(height+200)]
            equal = []
            for full in lines:
                if full[0] != direction: continue
                _,(l,u,r,d) = full
                for x in range(l,r):
                    for y in range(u,d):
                        if table[y][x] != None:
                            equal.append((table[y][x], full))
                        else:
                            table[y][x] = full
            equal = list(set(equal))
            #print equal
            graph = {}
            for v1,v2 in equal:
                if v1 not in graph: graph[v1] = []
                if v2 not in graph: graph[v2] = []
                graph[v1].append(v2)
                graph[v2].append(v1)
            #print graph
            seen = {}
            new = []
            for el in graph.keys():
                if el in seen: continue
                makeequal = dfs(graph, el)
                for each in makeequal:
                    seen[each] = True
                new.append((makeequal[0][0], reduce(union, [x[1] for x in makeequal])))
            for line in lines:
                if line not in seen:
                    new.append(line)
            lines = new
    print "THERE ARE END", len(lines)
    print list(sorted([area(x[1]) for x in lines]))
    print minsize
    lines = [x for x in lines if x[1][2]-x[1][0] > width/10 or x[1][3]-x[1][1] > height/30]
    print "THERE ARE END", len(lines)

    lines = extend_to_line(lines, width, height)


    new_lines = []
    for k,line in lines:
        if k == 'H':
            if any(line[0] <= (x[0]+x[2])/2 <= line[2] for x in giventargets):
                new_lines.append((k, line))
        if k == 'V':
            if any(line[1] <= (x[1]+x[3])/2 <= line[3] for x in giventargets):
                new_lines.append((k, line))
    lines = new_lines

    
    vertexes = dict((x, []) for _,x in lines)

    boxes = []
    for way1,line1 in lines:
        for way2,line2 in lines:
            if way1 != way2:
                if intersect(line1, line2):
                    boxes.append(intersect(line1, line2))
                    vertexes[line1].append(line2)
    print 'finished', len(str(vertexes)), len(boxes)
    return boxes,dict((k,v) for k,v in vertexes.items() if v != [])

def find_squares(graph, minarea):
    """
    Given a graph (vertexes are lines, edges when they intersect),
    return the squares that are in the graph.
    A square is when the DFS finds a back-edge where the difference in
    the preorders of the two nodes is 4.
    """
    def dfs_square(stack, debug=False):
        if debug:
            print ".  "*len(stack), stack[-1]
        if len(stack) == 4:
            if stack[0] in graph[stack[-1]]:
                tores = intersect(union(stack[0],stack[2]), union(stack[1],stack[3]))
                if area(tores) > minarea:
                    return [tores]
            return [None]
        res = []
        for vertex in graph[stack[-1]]:
            if vertex in stack: continue
            res += dfs_square(stack+[vertex], debug)
        return res

    #result = [dfs_square([start]) for start in graph]
    #result = [x for sublist in result for x in sublist]
    #return list(set([x for x in result if x]))
    result = {}
    for i,start in enumerate(graph):
        #print 'on', i, 'of', len(graph)
        for each in dfs_square([start]):
            if each:
                result[each] = True
    return result.keys()

def area(x): 
    if x == None: return 0
    return (x[2]-x[0])*(x[3]-x[1])

def do_extract(name, img, squares, giventargets):
    """
    Find all contests and extract them.
    
    Start with the smallest sized bounding box, and check if it
    contains any voting targets. 

    If it does, it's a contest. Remove it and the targets that
    are inside of it. Move on to next biggest.
    
    If not, then remove it and move on to the next biggest.

    For each contest, see if there are any previously-identified
    voting targets that were removed by a smaller bounding box,
    if there are, warn the operator. This means one contest
    encloses another.
    """

    targets = [x for x in giventargets]
    avg_targ_area = sum(map(area,targets))/len(targets)
    squares = [x for x in squares if area(x) > avg_targ_area*2]#xxx

    contests = []

    #print "T", targets
    for sq in sorted(squares, key=area):
        if sq in targets: continue
        inside = [t for t in targets if area(intersect(sq, t)) > area(t)/2] #xxx
        #print sq
        if inside != [] and sq[3]-sq[1] > 2*(t[3]-t[1]):
            #print "Adding a contest", sq, inside, [area(intersect(sq, t)) for t in inside]
            contests.append(sq)
            targets = [x for x in targets if x not in inside]

    if targets != []:
        print "Was left with", targets
    keepgoing = True
    while keepgoing:
        keepgoing = False
        for target in giventargets:
            #print 'this target', target
            tomerge = [x for x in contests if intersect(x, target) == target] #xxx
            if len(tomerge) > 1:
                # Find the smallest subset to merge which overlap all targets in all contests.
                maxcontest = None
                must_include_targets = sum([[x for x in giventargets if intersect(c, x)] for c in tomerge],[]) #xxx
                print 'must include', must_include_targets
                found = False
                for group_size in range(1,len(tomerge)+1):
                    if found: break
                    for comb in itertools.combinations(tomerge, group_size):
                        thiscontest = reduce(union, comb)
                        print 'this', thiscontest
                        print 'for each', [intersect(targ,thiscontest) for targ in must_include_targets]
                        if all(intersect(targ,thiscontest) for targ in must_include_targets):
                            print 'yes'
                            maxcontest = thiscontest
                            found = True
                            break
                print "MERGING", tomerge
                contests = [x for x in contests if x not in tomerge] + [maxcontest] #xxx
                keepgoing = True
                break
            elif len(tomerge) < 1:
                print "Target", target, "Not in any contest on ballot", name


    def samecolumn(a, b):
        if (abs(a[0]-b[0]) < 30 or abs(a[2]-b[2]) < 30):
            if abs((a[0]+a[2])/2-(b[0]+b[2])/2) < 100:
                return True
        return False
    def height(x): 
        if x == None: return 0
        return x[3]-x[1]
        
    if len(contests) > 2*len(giventargets)/3:
        equivs = list(contests)
        prev = 0
        h = giventargets[0][3]-giventargets[0][1]
        print "start", contests, h
        while prev != len(equivs):
            prev = len(equivs)
            new = []
            skip = {}
            for a in equivs:
                if a in skip: continue
                print "On ", a
                if a[3]-a[1] > len([x for x in giventargets if intersect(x,a)])*h*5: 
                    print 'abort 1', len([x for x in giventargets if intersect(x,a)]), a[3]-a[1]
                    new.append(a)
                    continue
                found = None
                for b in equivs:
                    if b[3]-b[1] > len([x for x in giventargets if intersect(x,b)])*h*5: 
                        print 'abort 2', len([x for x in giventargets if intersect(x,b)]), b[3]-b[1]
                        continue
                    if a == b: continue
                    if abs(b[3]-a[1]) < 30 and samecolumn(a, b):
                        print 'case 2', b
                        found = b
                        break
                if found != None:
                    print 'merge'
                    new.append(union(a, found))
                    skip[found] = True
                    skip[a] = True
                else:
                    new.append(a)
            equivs = new

            # Find which contests we've detected as equal,
            # and hopefully not ones which happen to overlap a bit,
            # and merge them together.
            equivs = []
            while new:
                s = [x for x in new if height(intersect(x,new[0])) >= h and samecolumn(x, new[0])]
                equivs.append(reduce(union,s))
                new = [x for x in new if x not in s]

                
            #print "RES", len(equivs), equivs

        contests = equivs
    
    #print "C", contests
    for cont in contests:
        if export:
            im = img.crop(cont)
            cname = tmp+"/"+str(sum(im.histogram()[:100]))+".png"
            im = img.crop(cont)
            im.save(cname)

    if do_save or do_test:
        new = Image.new("RGB", img.size, (255, 255, 255))
        imd = ImageDraw.Draw(new)
        for box in contests:
            c = (int(random.random()*200), int(random.random()*155+100), int(random.random()*155+100))
            imd.rectangle(box, fill=c)
        #print "GIVEN", giventargets
        for box in giventargets:
            #print box, area(box)
            imd.rectangle(box, fill=(255,0,0))
        new.save(tmp+"/"+name+"-fullboxed.png")

    return contests

    #print targets, contests
    #os.popen("open tmp/*")
    #exit(0)

#@pdb_on_crash
def remove_contest_overlap(boxes, targets):
    print "INPUT", boxes, targets

    boxes = np.array(boxes)

    def fn(delta):
        delta = np.reshape(delta, boxes.shape)
        #print "D",delta
        #print "B",boxes
        bxs = delta+boxes
        r = 0
        for i,box1 in enumerate(bxs):
            for j,box2 in enumerate(bxs):
                if all(box1 == box2): continue # yeah, yeah, a contest overlaps with itself
                r += area(intersect(box1,box2))*100
        r += (delta**2).sum()
        return r

    #def pr(x): print np.reshape(x,boxes.shape)

    zeros = np.zeros(boxes.shape)
    last = [None]
    #print 'aaa'
    def checkdiff(x):
        if last[0] != None:
            print np.abs(last[0]-x).sum(),
        last[0] = np.array(x)
        
    
    #print 'bbb'
    #print zeros+boxes
    v = fmin(fn, x0=zeros)
    #print "done", v
    
    return [map(int,x) for x in map(list,np.reshape(v,boxes.shape)+boxes)]

#remove_contest_overlap([(601, 425, 1094, 753), (118, 1479, 607, 1876), (1088, 425, 1575, 880), (1088, 874, 1575, 1450), (118, 1870, 607, 2479), (118, 425, 607, 1394), (601, 838, 1094, 2012)], [(620, 552, 690, 593), (1107, 1331, 1177, 1372), (621, 1750, 691, 1791), (620, 1199, 690, 1240), (621, 1614, 691, 1655), (621, 1098, 691, 1139), (1107, 819, 1177, 860), (621, 1399, 691, 1440), (621, 1887, 691, 1928), (136, 916, 206, 957), (137, 2030, 207, 2071), (138, 2348, 208, 2389), (137, 1751, 207, 1792), (135, 516, 205, 557), (136, 1085, 206, 1126), (136, 1269, 206, 1310), (136, 782, 206, 823), (620, 652, 690, 693), (620, 963, 690, 1004), (621, 1500, 691, 1541), (137, 1604, 207, 1645), (1107, 762, 1177, 803), (621, 1300, 691, 1341), (137, 2200, 207, 2241), (136, 649, 206, 690), (1108, 1389, 1178, 1430)])
#exit(0)
        
"""
def extract_contest(args):
    try:
        return extract_contest_2(args)
    except:
        print "Fail on", args[0]
        print "Fail on", args[0]
        print "Fail on", args[0]
        print "Fail on", args[0]
"""
def extract_contest(args):
    if len(args) == 3:
        image_path, giventargets, queue = args
        returnimage = True
    elif len(args) == 4:
        image_path, giventargets, returnimage, queue = args
    else:
        raise Error("Wrong number of args")

    now = time.time()

    print len(giventargets), giventargets

    print "processing", image_path
    data = load_threshold(image_path)
    #data = load_num(image_path)
    print 'loaded'
    lines = find_lines(data)
    lines += [('V', (len(data[0])-20, 0, len(data[0]), len(data)))]
    #print "calling with args", lines, len(data[0]), len(data), max(giventargets[0][2]-giventargets[0][0],giventargets[0][3]-giventargets[0][1])
    boxes, graph = to_graph(lines, len(data[0]), len(data), area(giventargets[0])**.5, giventargets)
    print 'tograph'
    squares = find_squares(graph, area(giventargets[0]))
    print 'findsquares'
    squares = sorted(squares, key=lambda x: -(x[2]-x[0])*(x[3]-x[1]))
    #print lines
    #print squares

    filename = ".".join(image_path.split("/")[-2:])[:-4]
    if do_save:
        show = num2pil(data)
        new = Image.new("RGB", show.size, (255, 255, 255))#load_pil(image_path).copy().convert("RGB")#
        imd = ImageDraw.Draw(new)
        for line in [x[1] for x in lines]:
            imd.rectangle(line, outline=(0,0,0))
        for line in boxes:
            imd.rectangle(line, fill=(0,0,255))
    
        print len(squares), "NUM"
    
        new.save(tmp+"/"+filename+"-line.png")
    
        new = Image.new("RGB", show.size, (255, 255, 255))
        imd = ImageDraw.Draw(new)
        for line in graph:
            imd.rectangle(line, outline=(0,0,0))
        for line in boxes:
            imd.rectangle(line, fill=(0,0,255))
    
        print len(squares), "NUM"
    
        new.save(tmp+"/"+filename+"-line-2.png")
    
        for l,u,r,d in squares:
            c = (int(random.random()*255), int(random.random()*255), int(random.random()*255))
            imd.rectangle((l,u,r,d), fill=c)
        new.save(tmp+"/"+filename+"-box.png")

    if do_save or export or do_test:
        loadedimage = load_pil(image_path)
    else:
        loadedimage = None

    #print "GET ARG", image_path, image_path.split("/")[-1]

    print len(giventargets), giventargets

    final = do_extract(filename,
                       loadedimage, squares, giventargets)

    #print "before"
    #print final
    #final = remove_contest_overlap(final, giventargets)
    #print "after"
    #print final

    #os.popen("open tmp/*")
    #exit(0)
    
    print "Took", time.time()-now
    queue.put(1)

    if returnimage:
        return data, final
    else:
        return final

def ballot_preprocess(i, f, image, contests, targets, lang, vendor):
    """
    Preprocess a ballot and turn it in to its corresponding data.
    For each contest, record the ballot ID, the contest bounding box,
    as well as the text associated with the contest.
    """
    sub = os.path.join(tmp+"", f.split("/")[-1].split(".")[0]+"-dir")
    #print "SUB IS", sub
    if not os.path.exists(sub):
        os.mkdir(sub)
    res = []
    print "CONTESTS", contests

    all_boxes = []
    for l,u,r,d in contests:
        all_boxes.append(specify_voting_targets.select_targets.ContestBox(l,u,r,d))

    for l,u,r,d in targets:
        all_boxes.append(specify_voting_targets.select_targets.TargetBox(l,u,r,d))

    assocs, _ = specify_voting_targets.select_targets.compute_box_ids(all_boxes)
    def grab(box): return (box.x1, box.y1, box.x2, box.y2)

    for c,targets in assocs.values():
        c = grab(c)
        targets = map(grab,targets)
        print "TOMAKE", c
        if not os.path.exists(os.path.join(sub, "-".join(map(str,c)))):
            os.mkdir(os.path.join(sub, "-".join(map(str,c))))
        t = compare_preprocess(lang, os.path.join(sub, "-".join(map(str,c))), 
                               image, c, targets, vendor)
        res.append((i, c, t))
    print "RESULTING", res
    return res

#@pdb_on_crash
def compare_preprocess(lang, path, image, contest, targets, vendor):
    """
    Identifies the text associated with the contest.

    Split the contest in to "stripes", one for each voting target,
    and one for the title. OCR the text and record it.
    """

    #targets = [x for x in targets if area(intersect(contest, x))] #xxx
    cont_area = None

    print path
    print 'targs', len(targets), targets

    if vendor:
        boxes = vendor.split_contest_to_targets(image, contest, targets)
    else:
        boxes = Vendor.Vendor(None).split_contest_to_targets(image, contest, targets)

    l,u,r,d = contest
    blocks = []
    print 'lenbox', len(boxes), boxes
    for count,(upper,lower) in boxes:
        istarget = (count != 0)
        print upper, lower
        if upper == lower:
            blocks.append((istarget, ""))
            continue
        name = os.path.join(path, str(count)+".tif")
        if os.path.exists(name+".txt"):
            txt = open(name+".txt").read().decode('utf8')
            if txt != '':
                print 'Found'
                blocks.append((istarget, txt))
                continue
            else:
                print 'Empty'
        #print "POS", upper, lower
        #print len(cont_area[upper:lower])
        if not os.path.exists(name):
            if cont_area == None: cont_area = load_num(pilimg=num2pil(image).crop((l+10,u+10,r-10,d-10)))
            img = num2pil(cont_area[upper:lower])
            img.save(name)
        
        txt = ""
        for iternum in range(3): # try 3 times
            if txt != "": continue
            os.popen("tesseract %s %s -l %s"%(name, name, lang))
            print 'Invoke tesseract'
            time.sleep(max((iternum-1)*.1,0))
            if os.path.exists(name+".txt"):
                print 'DONE'
                txt = open(name+".txt").read().decode('utf8')
                break

        if os.path.exists(name+".txt"):
            blocks.append((istarget, txt))
        else:
            print "-"*40
            print "OCR FAILED"
            print name
            print path
            print contest
            print lang
            print count, upper, lower
            print "-"*40
            blocks.append((istarget, ""))
            
    
    print 'retlen', len(blocks)
    return blocks

#import editdist
try:
    from Levenshtein import distance
except:
    print "Error: Edit Distance module not loaded"
    if __name__ != '__main__':
        print "Exiting"
        exit(1)

def row_dist(a, b):
    if type(a) == unicode or type(b) == unicode:
        return distance(unicode(a), unicode(b))
    else:
        return distance(a, b)
    #v = editdist.distance(a.encode("ascii", "ignore"), 
    #                      b.encode("ascii", "ignore"))
    #print 'r', v, a == b
    return v
    """
    Compute the edit distance between two strings.
    """
    if a == b: return 0
    prev = None
    curr = range(len(b)+1)
 
    for i in range(len(a)):
        #print curr
        prev = curr
        curr = [0]*(len(b)+1)
        curr[0] = i+1
        for j in range(len(b)):
            curr[j+1] = min(prev[j+1] + 1,
                            curr[j] + 1,
                            prev[j] + (a[i] != b[j]))
    return curr[-1]


count = 0
def compare(otexts1, otexts2, debug=False):
    """
    Compute the distance between two contests.
    
    This distance allows the order of the targets to shuffle,
    but does not allow the text within a target to reorder.
    
    We do this with an approximation of the weighted disjoint
    set cover problem. We sort the edges by weight, and take the
    minimum weight one, remove the corresponding nodes, and recurse.
    
    The distance is sum of the edges picked, as well as the sum
    of the unused vertexes.
    """

    if len(otexts1) != len(otexts2):
        print "Possible error: tried to compare distance of two contests with different number of targets."
        return 1<<30

    def fixup(s):
        words = s.split()
        found = 0
        for item,sep in [('Party Preference: Republican', 3), ('Party Preference: Democratic', 3),
                         ('MEMBER OF THE STATE ASSEMBLY', 5)]:
            for i in range(len(words)-(sep-1)):
                combined = " ".join(words[i:i+sep])
                if abs(len(combined)-len(item)) < len(item)/10:
                    if row_dist(combined, item) < len(item)/5:
                        words[i:i+sep] = item.split(" ")
                        found += len(item)
        return " ".join(words), found

    texts1, founds1 = zip(*[fixup(x) for t,x in otexts1 if t])
    texts2, founds2 = zip(*[fixup(x) for t,x in otexts2 if t])
    # Text associated with targets only
    ordering1 = range(len(texts1))
    ordering2 = range(len(texts2))
    size = sum(map(len,[x for _,x in otexts1]))+sum(map(len,[x for _,x in otexts2]))-sum(founds1)-sum(founds2)
    #print 'size', size
    if size == 0:
        print "Possible Error: A contest has no text associated with it"
        return [(1<<30,(len(texts1),0,0)) for _ in range(len(texts1))], (1<<30, 0)

    titles1 = [x for t,x in otexts1 if not t]
    titles2 = [x for t,x in otexts2 if not t]
    val = sum(row_dist(*x) for x in zip(titles1, titles2))
    #print 'dist of titles is', val

    all_vals = []
    for num_writeins in [0]:#range(len(texts2)):
        rottexts2 = [[texts2[i] for _,i in get_order(len(texts2),order,num_writeins)] for order in range(len(texts2))]
        values = [(sum(row_dist(a,b) for a,b in zip(texts1, t2)),i) for i,t2 in enumerate(rottexts2)]
        if debug:
            print "DEBUG", size, size-sum(map(len,titles1))-sum(map(len,titles2))
            print num_writeins
            print [([row_dist(a,b) for a,b in zip(texts1, t2)],i) for i,t2 in enumerate(rottexts2)]
            print map(len,texts1), map(len,texts2)
            print min(values)
        #print values
        minweight,order = min(values)

        #print 'min', order, minweight

        all_vals.append((minweight, order, num_writeins))
    #print "BEST:", best_val
    #print 'so should be equal'
    #print texts1
    #print texts2[best_val[1]:-best_val[2]]+texts2[:best_val[1]]+texts2[-best_val[2]:]
    all_vals = sorted(all_vals)
    res = {}
    best = 1<<30, None
    for weight,order,num_writeins in all_vals:
        if float(weight+val)/size < best[0]:
            best = float(weight+val)/size, num_writeins
        res[num_writeins] = (float(weight+val)/size,
                             (len(texts1), order, num_writeins))
    #print otexts1
    #print otexts2
    #print "res", [x[1] for x in sorted(res.items())], best
    return [x[1] for x in sorted(res.items())], best

def get_order(length, order, num_writeins):
    lst = range(length)
    if num_writeins == 0:
        new_order = lst[order:]+lst[:order]
    else:
        new_order = lst[order:-num_writeins]+lst[:order]+lst[-num_writeins:]
    return list(zip(lst, new_order))

def first_pass(contests, languages):
    """
    Split a set of contests in to a set of sets, where each
    set contains the same number of voting targets of the same language.
    """
    ht = {}
    i = 0
    for each in contests:
        key = (len(each[2]), None if each[0] not in languages else languages[each[0]])
        if key not in ht: ht[key] = []
        ht[key].append(each)
    return [x for x in sorted(ht.items())]

class Contest:
    def __init__(self, contests_text, cid, const=.2):
        self.contests_text = contests_text
        self.cid = cid
        self.const = const
        # CID -> [(distance, order, numwritein)]
        self.similarity = {}
        self.parent = self
        self.depth = 0
        self.children = []
        self.writein_num = 0

    def all_children(self):
        res = [self]
        for child in self.children:
            res += child.all_children()
        return res

    def get_root(self):
        while self.parent != self.parent.parent:
            self.parent = self.parent.parent
        return self.parent

    def dominating_set(self):
        root = self.get_root()
        children = root.all_children()
        conn = {}
        for c1 in children:
            lst = []
            for c2 in children:
                if c1.similarity[c2.cid][root.writein_num][0] < .1:
                    lst.append(c2.cid)
            conn[c1.cid] = lst
        conn = conn.items()
        rem = {}
        used = []
        while len(rem) != len(children):
            item = max(conn, key=lambda x: len(x[1]))
            used.append(item[0])
            for v in item[1]:
                rem[v] = True
            rem[item[0]] = True
            conn = [(k,[x for x in v if x not in rem]) for k,v in conn if k not in rem]
        print "SET", used

    def is_close(self, other, num_writein):
        group1 = self.all_children()
        group2 = other.all_children()
        best = 1<<31, None
        #print 'joining', len(group1), len(group2)
        for nwi in set([self.writein_num, other.writein_num, num_writein]):
            distance = 0
            for c1 in group1:
                for c2 in group2:
                    if c2.cid not in c1.similarity:
                        distance += 1
                    else:
                        distance += c1.similarity[c2.cid][nwi][0]
            distance /= len(group1)*len(group2)
            #print nwi, distance
            if distance < best[0]:
                best = distance, nwi
        #print 'pick', best
        return best[0] < self.const, best[1]
    
    def join(self, new_parent, num_writein):
        if self.get_root() == new_parent.get_root():
            return

        root1 = self.parent
        root2 = new_parent.parent

        close, winum = root1.is_close(root2, num_writein)
        if not close: return

        if root1.depth < root2.depth:
            root1.parent = root2
            root2.children.append(root1)
            root2.writein_num = winum
        elif root2.depth < root1.depth:
            root2.parent = root1
            root1.children.append(root1)
            root1.writein_num = winum
        else:
            root1.parent = root2
            root1.depth += 1
            root2.children.append(root1)
            root2.writein_num = winum
    
def do_group_pairing_map(args):
    global tmp

    args = args[0]
    #for k,v in list(zip(globals(), [type(v) for k,v in globals().items()])):
    #    print k,v

    items, contests_text = args
    #out = open(tmp+"/group_dump/"+str(items[0]), "w")
    x = 0
    for i in items:
        lst = []
        for j in range(len(contests_text)):
            if x%10000 == 0: print x
            x += 1
            #print ((i,j),compare(contests_text[i][2], contests_text[j][2]))
            lst.append(((i,j),compare(contests_text[i][2], contests_text[j][2])))
        #out.write("\n".join(map(str,lst))+"\n")
        pickle.dump(lst, open(tmp+"/group_dump/"+str(i), "w"))
    #out.close()
    return []

def group_by_pairing(contests_text, CONST):
    """
    Group contests together by pairing them one at a time.

    Currently this is very slow. It's going to run n^2 comparisons,
    and then do a linear scan through each of them to make the groups.
    """
    global tmp

    contests = [Contest(contests_text, i, CONST) for i in range(len(contests_text))]

    #args = [(i,cont1,j,cont2) for i,cont1 in enumerate(contests_text) for j,cont2 in enumerate(contests_text)]


    #"""
    if not os.path.exists(tmp+"/group_dump"):
        os.mkdir(tmp+"/group_dump")
    else:
        os.popen("rm "+tmp+"/group_dump/*")

    """
    print "Prepare"
    pool = mp.Pool(mp.cpu_count())
    print "Start"
    data = [[] for _ in range(mp.cpu_count())]
    for i in range(len(contests_text)):
        data[i%len(data)].append(i)
    print "GO UP TO", (len(contests_text)**2)/mp.cpu_count()
    data = [(x, contests_text) for x in data]
    pool.map(do_group_pairing_map, data)
    pool.close()
    pool.join()
    #"""
    if False:
        do_group_pairing_map([(range(len(contests_text)), contests_text)])
    else:
        num = mp.cpu_count()
        data = [[] for _ in range(num)]
        for i in range(len(contests_text)):
            data[i%len(data)].append(i)
        print "GO UP TO", (len(contests_text)**2)/num
        data = [(x, contests_text) for x in data]
        do_partask(do_group_pairing_map, data, N=num)
    

    diff = {}
    print len(contests_text)
    for i in range(len(contests_text)):
        if i%100 == 0:
            print 'load', i
        d = pickle.load(open(tmp+"/group_dump/"+str(i)))
        for k,v in d:
            diff[k] = v
        
    print "Done"
    diff = sorted(diff.items(), key=lambda x: x[1][1][0])
    print len(diff)
    #print diff[0]

    for (k1,k2),(dmap,best) in diff:
        if k1 == k2:
            print 'eq', k1, k2, dmap, best
        contests[k1].similarity[k2] = dmap
    print "Created"
    now = time.time()
    for (k1,k2),(dmap,best) in diff:
        if best[0] > CONST: continue
        if k1 == k2: continue
        contests[k1].join(contests[k2], best[1])
        #print 'join', contests_text[k1][0], contests_text[k2][0]
        #print 'data', contests[k1].writein_num, contests[k2].writein_num
        #print contests_text[k1][2][1]
        #print contests_text[k2][2][1]
    print "taken", time.time()-now
    print "Traverse"
    seen = {}
    res = []
    for contest in contests:
        #print 'try', contest.cid,
        contest = contest.get_root()
        if contest in seen: continue
        #print "SEE", contest
        #contest.dominating_set()
        seen[contest] = True
        v = [x.cid for x in contest.all_children()]
        #print "CHILDREN", v
        write = contest.writein_num
        #print "FOR THIS GROUP", write
        if contest.cid in contest.similarity:
            print 'case 1', get_order(*contest.similarity[contest.cid][write][1]), contest.similarity[contest.cid][write][1]
            this = [(contests_text[contest.cid][:2],get_order(*contest.similarity[contest.cid][write][1]))]
        else:
            #print 'case 2', range(len(contests_text[contest.cid][:2])-1)
            v = []
            l = range(len(contests_text[contest.cid][:2])-1)
            this = [(contests_text[contest.cid][:2],zip(l,l))]
        #print "Base"
        #print list(enumerate(contests_text[contest.cid][2][1:]))
        for x in v:
            if x == contest.cid: continue
            #print contest.similarity[x]
            #print contest.similarity[x][write][1], get_order(*contest.similarity[x][write][1])
            #print "This", list(enumerate(contests_text[x][2][1:]))
            this.append((contests_text[x][:2],get_order(*contest.similarity[x][write][1])))
        #print this
        print "ADD", len(res), this
        res.append(this)
    print "Workload reduction"
    print map(len,res)
    print len([x for x in map(len,res) if x > 3])+sum([x for x in map(len,res) if x <= 3]), sum(map(len,res))
    print "Factor", float(len([x for x in map(len,res) if x > 3])+sum([x for x in map(len,res) if x <= 3]))/sum(map(len,res))
    return res

def full_group(contests_text, key):
    print "Linear Scan"

    if key[1] == 'eng':
        CONST = .2
    elif key[1] == 'spa':
        CONST = .2
    elif key[1] == 'vie':
        CONST = .25
    elif key[1] == 'kor':
        CONST = .3
    elif key[1] == 'chi_sim':
        CONST = .3
    else:
        CONST = .2
    
    debug=[]

    contests_text = sorted(contests_text, key=lambda x: sum(len(v[1]) for v in x[2]))
    joins = dict((i,[]) for i in range(len(contests_text)))
    for offset in range(1,2):
        for i,(c1,c2) in enumerate(zip(contests_text, contests_text[offset:])):
            data, (score,winum) = compare(c1[2], c2[2])
            debug.append((score,(c1[2][0], c2[2][0])))
            if score < CONST/2:
                #print 'merged', c1[2], c2[2]
                joins[i].append(i+offset)
                joins[i+offset].append(i)
    def mylen(l):
        return sum(2 if ord(x)>512 else 1 for x in l)

    #for each in sorted(debug):
    #    print each[0]
    #    s1 = each[1][0][1].split("\n")
    #    s2 = each[1][1][1].split("\n")
    #    #print s1, s2
    #    s1 = [x+"."*(max(map(mylen,s1))-mylen(x)) for x in s1]
    #    print "\n".join([a+"  |  "+b for a,b in zip(s1,s2)])

    seen = {}
    exclude = {}
    for i in joins:
        if i in seen: continue
        items = dfs(joins, i)
        first = min(items)
        for each in items: seen[each] = True
        for each in items:
            if first != each:
                exclude[each] = first
    

    #print sorted(exclude.items())

    new_indexs = [x for x in range(len(contests_text)) if x not in exclude]
    new_contests = [contests_text[x] for x in new_indexs]

    print "Of sizes", len(contests_text), len(new_contests)
    #for x in new_contests[::100]:
    #    print x
    newgroups = []
    STEP = 1000
    print "Splitting to smaller subproblems:", round(.5+(float(len(new_contests))/STEP))
    for iternum in range(0,len(new_contests),STEP):
        print "SUBPROB", iternum/STEP
        newgroups += group_by_pairing(new_contests[iternum:min(iternum+STEP, len(new_contests))], CONST)

    mapping = {}
    for i,each in enumerate(newgroups):
        for item in each:
            mapping[item[0][0],tuple(item[0][1])] = i
    #print "mapping", mapping

    for dst,src in exclude.items():
        #print "Get", dst, "from", src
        bid,cids = contests_text[src][:2]
        index = mapping[bid,tuple(cids)]
        find = newgroups[index][0][0]
        text = [text for bid,cid,text in contests_text if (bid,cid) == find][0]
        data,(score,winum) = compare(text, contests_text[dst][2])
        newgroups[index].append((contests_text[dst][:2], get_order(*data[winum][1])))
    
    print "SO GET"
    #print sorted(map(hash,map(str,map(sorted,groups))))
    print sorted(map(sorted,newgroups))

    return newgroups
    

            
def equ_class(contests, languages):
    #print "EQU", contests
    #print map(len, contests)
    #print contests
    contests = [x for sublist in contests for x in sublist]
    #print contests
    groups = first_pass(contests, languages)
    # Each group is known to be different.
    result = []
    print "Go up to", len(groups)
    for i,(key,group) in enumerate(groups):
        print "-"*50
        print "ON GROUP", i, key, len(group)
        print "-"*50
        result += full_group(group, key)
        print "Finished one group"
        print "Total length", len(result)
    
    #print "RETURNING", result
    return result

def get_target_to_contest(contests, targets):
    if 1 == 1:
        all_boxes = []
        for l,u,r,d in contests:
            all_boxes.append(specify_voting_targets.select_targets.ContestBox(l,u,r,d))
            
        for l,u,r,d in targets:
            all_boxes.append(specify_voting_targets.select_targets.TargetBox(l,u,r,d))
                
        assocs, _ = specify_voting_targets.select_targets.compute_box_ids(all_boxes)
        def grab(box): return (box.x1, box.y1, box.x2, box.y2)

        target_to_contest = {}
        for contest,all_targets in assocs.values():
            for target in all_targets:
                target_to_contest[grab(target)]=contests.index(grab(contest))
        return target_to_contest


def merge_contests(ballot_data, fulltargets):
    """
    Given a set of bounding boxes, merge together those which
    are different boundingboxes but are, in reality, the same contest.
    """
    #pdb.set_trace()
    new_data = []
    for ballot, targets in zip(ballot_data, fulltargets):
        #print 'next'
        new_ballot = []
        seen_so_far = []

        target_to_contest = get_target_to_contest([x[1] for x in ballot], sum(targets,[]))

        for group in targets:
            #for c,targets in assocs.values():

            #print 'targs is', group
            # indexs in ballot of contests which are equal
            #equal = [i for t in group for i,(_,bounding,_) in enumerate(ballot) if intersect(t, bounding) == t]
            equal = [target_to_contest[x] for x in group]
            equal_uniq = list(set(equal))
            if any(x in seen_so_far for x in equal_uniq) or equal_uniq == []:
                raise Exception()
            seen_so_far.extend(equal_uniq)
            #print equal_uniq
            merged = sum([ballot[x][2] for x in equal_uniq],[])
            new_ballot.append((ballot[equal[0]][0], [ballot[x][1] for x in equal_uniq], merged))
        new_data.append(new_ballot)
    #print new_data
    return new_data

def do_extend(args):
    txt,c1,c2,t1,t2 = args
    data, (score, winum) = compare(txt, t1[2]+t2[2])
    if score < .2:
        #print "THEY ARE EQUAL"
        res = (c1, c2)
        #print 'txt', t1, t2
        newgroup = ((c1[0], [c1[1], c2[1]], t1[2]+t2[2]), get_order(*data[winum][1]))
        return res, newgroup
    return None
        

def extend_multibox(ballots, box1, box2, orders):
    ballot = ballots[box1[0]]
    txt1 = [x for x in ballot if x[:2] == box1][0]
    txt2 = [x for x in ballot if x[:2] == box2][0]
    txt = txt1[2]+txt2[2]
    res = []
    newgroup = []

    tocompare = []
    for bid,order in enumerate(orders):
        #print 'BID IS', bid
        for c1,c2 in order:
            t1 = [x for x in ballots[bid] if x[:2] == c1][0]
            t2 = [x for x in ballots[bid] if x[:2] == c2][0]
            if len(t1[2])+len(t2[2]) != len(txt1[2])+len(txt2[2]):
                continue
            tocompare.append((txt,c1,c2,t1,t2))
    pool = mp.Pool(mp.cpu_count())
    res = pool.map(do_extend, tocompare)
    pool.close()
    pool.join()
    print "RESULT", res
    res = [x for x in res if x != None]
    res, newgroup = zip(*res)
    print "RESULT", res
    print "NEWGROUP", newgroup

    return res, newgroup

@pdb_on_crash
def find_contests(t, paths, giventargets):
    """
    Input:
        str T:
        list PATHS:
        list GIVENTARGETS: G[i][j][k] := k-th target of j-th contest of i-th ballot.
    """
    global tmp
    #print "ARGS", (t, paths, giventargets)
    #exit(0)
    #paths = paths[80:400]
    #giventargets = giventargets[80:400]

    """
    giventargets += giventargets
    giventargets += giventargets
    npaths = list(paths)
    npaths += [x.replace("bal_0", "bal_1") if os.path.exists(x.replace("bal_0", "bal_1")) else x for x in paths]
    npaths += [x.replace("bal_0", "bal_2") if os.path.exists(x.replace("bal_0", "bal_2")) else x for x in paths]
    npaths += [x.replace("bal_0", "bal_3") if os.path.exists(x.replace("bal_0", "bal_3")) else x for x in paths]
    paths = npaths
    """
    if t[-1] != '/': t += '/'
    tmp = t
    if not os.path.exists(tmp):
        os.mkdir(tmp)
    os.popen("rm -r "+tmp.replace(" ", "\\ ")+"*")

    manager = mp.Manager()
    queue = manager.Queue()
    args = [(f, sum(giventargets[i],[]), False, queue) for i,f in enumerate(paths)]
    #args = [x for x in args if '0/bal_0_side_1' in x[0]]
    pool = mp.Pool(mp.cpu_count())
    res = [None]
    def done(x): res[0] = x
    pool.map_async(extract_contest, args, callback=done)
    got = 0
    while got < len(args):
        sys.stderr.write('.')
        val = queue.get(block=True)
        wx.CallAfter(Publisher().sendMessage, "signals.MyGauge.tick")
        got += 1

    pool.close()
    pool.join()
    return res[0]
    #print "RETURNING", ballots
    reverse = sorted(enumerate(paths), key=lambda x: x[1])
    for i in range(0,len(reverse),4):
        print reverse[i:i+4]
        full = [ballots[x] for x,_ in reverse[i:i+4]]
        if full == []: continue
        order = []
        for each in full:
            order.append(sorted(each, key=lambda x: (x[0]/200, x[1])))
        print 'i get', i, order
        for cs in zip(*order):
            err = 0
            for coords in zip(*cs):
                avg = sum(coords)/len(coords)
                err += sum(abs(x-avg) for x in coords)
            if err > 100:
                print 'err', err, paths[reverse[i][0]], reverse[i]
                print cs
    return ballots

def group_given_contests_map(arg):
    vendor,lang_map,giventargets,(i,(f,conts)) = arg
    print f
    im = load_num(f)
    lang = lang_map[f] if f in lang_map else 'eng'
    return ballot_preprocess(i, f, im, conts, sum(giventargets[i],[]), lang, vendor)
        
#@pdb_on_crash
def group_given_contests(t, paths, giventargets, contests, flip, vendor, lang_map = {}, NPROC=None):
    global tmp, flipped
    #print "ARGUMENTS", (t, paths, giventargets, lang_map)
    #print 'giventargets', giventargets
    #print lang_map
    if t[-1] != '/': t += '/'
    flipped = flip
    tmp = t
    if not os.path.exists(tmp):
        os.mkdir(tmp)
    #os.popen("rm -r "+tmp.replace(" ", "\\ ")+"*")
    if NPROC == None:
        NPROC = mp.cpu_count()
    if NPROC == 1:
        print "(Info) Using 1 process for group_given_contests"
        ballots = []
        args = [(vendor, lang_map, giventargets, x) for x in enumerate(zip(paths, contests))]
        for arg in args:
            ballots.append(group_given_contests_map(arg))
    else:
        print "(Info) Using {0} processors for group_given_contests".format(NPROC)
        pool = mp.Pool(NPROC)
        args = [(vendor,lang_map,giventargets,x) for x in enumerate(zip(paths,contests))]
        #print paths, giventargets, contests
        #print paths[11], giventargets[11], contests[11]
        #exit(0)
        ballots = pool.map(group_given_contests_map, args)
        pool.close()
        pool.join()
        #ballots = map(group_given_contests_map, args)
    print "WORKING ON", ballots
    return ballots, final_grouping(ballots, giventargets, paths, lang_map)

@pdb_on_crash
def final_grouping(ballots, giventargets, paths, langs, t=None):
    global tmp
    if t != None:
        tmp = t
    lookup = dict((x,i) for i,x in enumerate(paths))
    if langs:
        languages = dict((idx, langs[imP]) for imP, idx in lookup.iteritems())
    else:
        languages = {}
    #languages = dict((lookup[k],v) for k,v in langs.items())
    print "RUNNING FINAL GROUPING"
    #pickle.dump((ballots, giventargets), open("/tmp/aaa", "w"))
    ballots = merge_contests(ballots, giventargets)
    print "NOW EQU CLASSES"
    #print ballots
    #pickle.dump((ballots, languages), open("/tmp/aaa", "w"))
    return equ_class(ballots, languages)

def sort_nicely( l ): 
  """ Sort the given list in the way that humans expect. Does an inplace sort.
  From:
      http://www.codinghorror.com/blog/2007/12/sorting-for-humans-natural-sort-order.html
  """ 
  convert = lambda text: int(text) if text.isdigit() else text 
  alphanum_key = lambda key: [ convert(c) for c in re.split('([0-9]+)', key) ] 
  l.sort( key=alphanum_key ) 

import re
import csv

class ThreadDoInferContests:
    def __init__(self, queue, job_id, proj, *args, **kwargs):
        self.job_id = job_id
        self.queue = queue
        self.proj = proj

    def extract_data(self):
        """
        Stolen from labelcontest.py.

        This should be removed in favor of taking the data from
        this panel directly, instead of loading from the file.
        """
        res = []
        dirList = []
        for root,dirs,files in os.walk(self.proj.target_locs_dir):
            sort_nicely(files) # Fixes Marin ordering.
            for each in files:
                if each[-4:] != '.csv': continue
                gr = {}
                name = os.path.join(root, each)
                for i, row in enumerate(csv.reader(open(name))):
                    if i == 0:
                        # skip the header row, to avoid adding header
                        # information to our data structures
                        continue
                    # If this one is a target, not a contest
                    if row[7] == '0':
                        if row[8] not in gr:
                            gr[row[8]] = []
                        # 2,3,4,5 are left,up,width,height but need left,up,right,down
                        gr[row[8]].append((int(row[2]), int(row[3]), 
                                           int(row[2])+int(row[4]), 
                                           int(row[3])+int(row[5])))
                    r = row[0].replace("/media/data1/audits2012_straight/santacruz/blankballots/", "santacruz/")
                    if r not in dirList:
                        dirList.append(r)
                if gr.values() != []:
                    res.append(gr.values())
        #for a,b in zip(dirList, res):
        #    print a,b
        #print res
        #print dirList
        return res, dirList
        
    def run(self):
        # Do fancy contest-inferring computation
        data, files = self.extract_data()
        bboxes = dict(zip(files,find_contests(self.proj.ocr_tmp_dir, files, data)))
        # Computation done!
        self.queue.put(bboxes)
        self.proj.infer_bounding_boxes = True
        print "AND I SEND THE RESUTS", bboxes


"""
if __name__ == "__main__":
    _, paths, them = pickle.load(open("marin_contest_run"))
    paths = [x.replace("/media/data1/audits2012_straight/marin/blankballots", "marin") for x in paths]
    find_contests("tmp", paths, them)
    exit(0)
#"""

tmp = "tmp"

"""
if __name__ == "__main__":
    p = "./"
    class FakeProj:
        target_locs_dir = p+"sc_target_locations"
        ocr_tmp_dir = p+"tmp"
    class FakeQueue:
        def put(self, x):
            return
    thr = ThreadDoInferContests(FakeQueue(), 0, FakeProj())
    print thr
    thr.run()
    exit(0)
"""

if __name__ == "__main__":
    find_contests(u'../projects_new/napa/ocr_tmp_dir', [u'../projects_new/napa/groupsAlign_seltargs/partition_0/bal_0_side_0.png', u'../projects_new/napa/groupsAlign_seltargs/partition_0/bal_0_side_1.png', u'../projects_new/napa/groupsAlign_seltargs/partition_1/bal_0_side_0.png', u'../projects_new/napa/groupsAlign_seltargs/partition_1/bal_0_side_1.png', u'../projects_new/napa/groupsAlign_seltargs/partition_2/bal_0_side_0.png', u'../projects_new/napa/groupsAlign_seltargs/partition_2/bal_0_side_1.png', u'../projects_new/napa/groupsAlign_seltargs/partition_3/bal_0_side_0.png', u'../projects_new/napa/groupsAlign_seltargs/partition_4/bal_0_side_0.png', u'../projects_new/napa/groupsAlign_seltargs/partition_4/bal_0_side_1.png', u'../projects_new/napa/groupsAlign_seltargs/partition_5/bal_0_side_0.png', u'../projects_new/napa/groupsAlign_seltargs/partition_5/bal_0_side_1.png', u'../projects_new/napa/groupsAlign_seltargs/partition_6/bal_0_side_0.png', u'../projects_new/napa/groupsAlign_seltargs/partition_6/bal_0_side_1.png'], [[[(1212, 1423, 1342, 1456)], [(1211, 1677, 1341, 1710)], [(1209, 2185, 1339, 2218)], [(1208, 2435, 1338, 2468)], [(1206, 2932, 1336, 2965)], [(1210, 1846, 1340, 1879)], [(1210, 1931, 1340, 1964)], [(607, 1504, 737, 1537)], [(1212, 1508, 1342, 1541)], [(1209, 2269, 1339, 2302)], [(1207, 2600, 1337, 2633)], [(607, 1363, 737, 1396)], [(1206, 3015, 1336, 3048)], [(1209, 2100, 1339, 2133)], [(607, 1433, 737, 1466)], [(1207, 2767, 1337, 2800)], [(1211, 1593, 1341, 1626)], [(1207, 2684, 1337, 2717)], [(1210, 2016, 1340, 2049)], [(1209, 2352, 1339, 2385)], [(1813, 2601, 1943, 2634)], [(607, 1574, 737, 1607)], [(1211, 1761, 1341, 1794)], [(1207, 2519, 1337, 2552)], [(1815, 2193, 1945, 2226)], [(1813, 2519, 1943, 2552)], [(1812, 3026, 1942, 3059)], [(1815, 2108, 1945, 2141)], [(1812, 2944, 1942, 2977)], [(1816, 1764, 1946, 1797)], [(1207, 2850, 1337, 2883)], [(1815, 2024, 1945, 2057)], [(1815, 2277, 1945, 2310)], [(1817, 1596, 1947, 1629)], [(1813, 2861, 1943, 2894)], [(1817, 1511, 1947, 1544)], [(1817, 1425, 1947, 1458)], [(1817, 1679, 1947, 1712)]], [[(602, 1527, 732, 1560)], [(602, 1192, 732, 1225)], [(602, 1121, 732, 1154)], [(602, 1598, 732, 1631)], [(603, 675, 733, 708)], [(603, 603, 733, 636)], [(603, 745, 733, 778)], [(603, 532, 733, 565)]], [[(1211, 1755, 1341, 1788)], [(1210, 2594, 1340, 2627)], [(1211, 2009, 1341, 2042)], [(606, 1460, 736, 1493)], [(606, 1530, 736, 1563)], [(1211, 1840, 1341, 1873)], [(606, 1670, 736, 1703)], [(1211, 1417, 1341, 1450)], [(606, 1810, 736, 1843)], [(1210, 2677, 1340, 2710)], [(1211, 2094, 1341, 2127)], [(1211, 1587, 1341, 1620)], [(606, 1740, 736, 1773)], [(1211, 2263, 1341, 2296)], [(1211, 1502, 1341, 1535)], [(1210, 2512, 1340, 2545)], [(1210, 2760, 1340, 2793)], [(1211, 1924, 1341, 1957)], [(606, 1390, 736, 1423)], [(1211, 1671, 1341, 1704)], [(1210, 2926, 1340, 2959)], [(606, 1600, 736, 1633)], [(1211, 2179, 1341, 2212)], [(1211, 2345, 1341, 2378)], [(1210, 3009, 1340, 3042)], [(1210, 2429, 1340, 2462)], [(1210, 2843, 1340, 2876)], [(1817, 2185, 1947, 2218)], [(1817, 1756, 1947, 1789)], [(1817, 2593, 1947, 2626)], [(1816, 2511, 1946, 2544)], [(1817, 1503, 1947, 1536)], [(1817, 2016, 1947, 2049)], [(1817, 1418, 1947, 1451)], [(1817, 1588, 1947, 1621)], [(1816, 3018, 1946, 3051)], [(1817, 2100, 1947, 2133)], [(1816, 2935, 1946, 2968)], [(1817, 2269, 1947, 2302)], [(1817, 1672, 1947, 1705)], [(1817, 2853, 1947, 2886)]], [[(602, 605, 732, 638)], [(602, 1194, 732, 1227)], [(602, 1123, 732, 1156)], [(602, 677, 732, 710)], [(602, 1599, 732, 1632)], [(602, 534, 732, 567)], [(602, 1529, 732, 1562)], [(602, 748, 732, 781)]], [[(607, 1582, 737, 1615)], [(1212, 1516, 1342, 1549)], [(1206, 2940, 1336, 2973)], [(1209, 2193, 1339, 2226)], [(1210, 2024, 1340, 2057)], [(1208, 2609, 1338, 2642)], [(1206, 3023, 1336, 3056)], [(1209, 2277, 1339, 2310)], [(1212, 1601, 1342, 1634)], [(1211, 1685, 1341, 1718)], [(1211, 1939, 1341, 1972)], [(607, 1511, 737, 1544)], [(1211, 1770, 1341, 1803)], [(1210, 2109, 1340, 2142)], [(607, 1370, 737, 1403)], [(1208, 2527, 1338, 2560)], [(1211, 1854, 1341, 1887)], [(1209, 2360, 1339, 2393)], [(607, 1441, 737, 1474)], [(1208, 2692, 1338, 2725)], [(1207, 2775, 1337, 2808)], [(1212, 1430, 1342, 1463)], [(1208, 2443, 1338, 2476)], [(1207, 2858, 1337, 2891)], [(1812, 2610, 1942, 2643)], [(1811, 2952, 1941, 2985)], [(1812, 2528, 1942, 2561)], [(1814, 2202, 1944, 2235)], [(1814, 2117, 1944, 2150)], [(1814, 2033, 1944, 2066)], [(1811, 3035, 1941, 3068)], [(1816, 1519, 1946, 1552)], [(1815, 1773, 1945, 1806)], [(1811, 2869, 1941, 2902)], [(1816, 1604, 1946, 1637)], [(1816, 1688, 1946, 1721)], [(1814, 2286, 1944, 2319)], [(1816, 1434, 1946, 1467)]], [[(600, 1206, 730, 1239)], [(600, 1613, 730, 1646)], [(600, 686, 730, 719)], [(600, 542, 730, 575)], [(600, 614, 730, 647)], [(600, 757, 730, 790)], [(600, 1542, 730, 1575)], [(600, 1135, 730, 1168)]], [[(1210, 1509, 1340, 1542)], [(1215, 2191, 1345, 2224)], [(1211, 1677, 1341, 1710)], [(1214, 2022, 1344, 2055)], [(1212, 1762, 1342, 1795)], [(1221, 2941, 1351, 2974)], [(1221, 3024, 1351, 3057)], [(605, 1513, 735, 1546)], [(1214, 2106, 1344, 2139)], [(609, 2020, 739, 2053)], [(1218, 2598, 1348, 2631)], [(1211, 1594, 1341, 1627)], [(607, 1766, 737, 1799)], [(1209, 1424, 1339, 1457)], [(1217, 2517, 1347, 2550)], [(617, 3019, 747, 3052)], [(610, 2189, 740, 2222)], [(615, 2688, 745, 2721)], [(614, 2604, 744, 2637)], [(609, 1935, 739, 1968)], [(610, 2105, 740, 2138)], [(606, 1681, 736, 1714)], [(611, 2273, 741, 2306)], [(608, 1851, 738, 1884)], [(606, 1598, 736, 1631)], [(616, 2936, 746, 2969)], [(615, 2771, 745, 2804)], [(612, 2356, 742, 2389)], [(604, 1428, 734, 1461)], [(613, 2523, 743, 2556)], [(1216, 2275, 1346, 2308)], [(612, 2439, 742, 2472)], [(1220, 2858, 1350, 2891)], [(616, 2854, 746, 2887)], [(1814, 1321, 1944, 1354)], [(1815, 1392, 1945, 1425)], [(1816, 1533, 1946, 1566)], [(1816, 1462, 1946, 1495)], [(1819, 1904, 1949, 1937)], [(1820, 1974, 1950, 2007)], [(1822, 2303, 1952, 2336)], [(1822, 2373, 1952, 2406)]], [[(605, 1674, 735, 1707)], [(1210, 1845, 1340, 1878)], [(605, 1605, 735, 1638)], [(1209, 2099, 1339, 2132)], [(604, 2025, 734, 2058)], [(1209, 2268, 1339, 2301)], [(1209, 2184, 1339, 2217)], [(1208, 2682, 1338, 2715)], [(1210, 1930, 1340, 1963)], [(605, 1394, 735, 1427)], [(1208, 2599, 1338, 2632)], [(1206, 3013, 1336, 3046)], [(605, 1744, 735, 1777)], [(604, 1884, 734, 1917)], [(1210, 1676, 1340, 1709)], [(604, 1955, 734, 1988)], [(1208, 2434, 1338, 2467)], [(604, 1814, 734, 1847)], [(605, 1464, 735, 1497)], [(1210, 2015, 1340, 2048)], [(1211, 1422, 1341, 1455)], [(1207, 2930, 1337, 2963)], [(1211, 1507, 1341, 1540)], [(1208, 2517, 1338, 2550)], [(605, 1535, 735, 1568)], [(1207, 2765, 1337, 2798)], [(1210, 1760, 1340, 1793)], [(1211, 1593, 1341, 1626)], [(1209, 2350, 1339, 2383)], [(1207, 2848, 1337, 2881)], [(1814, 2942, 1944, 2975)], [(1814, 3025, 1944, 3058)], [(1817, 2023, 1947, 2056)], [(1815, 2859, 1945, 2892)], [(1817, 2192, 1947, 2225)], [(1815, 2518, 1945, 2551)], [(1817, 2107, 1947, 2140)], [(1816, 2600, 1946, 2633)], [(1818, 1763, 1948, 1796)], [(1818, 1679, 1948, 1712)], [(1818, 1510, 1948, 1543)], [(1818, 1595, 1948, 1628)], [(1816, 2276, 1946, 2309)], [(1818, 1425, 1948, 1458)]], [[(600, 749, 730, 782)], [(600, 1195, 730, 1228)], [(600, 678, 730, 711)], [(600, 607, 730, 640)], [(600, 1530, 730, 1563)], [(600, 1124, 730, 1157)], [(600, 535, 730, 568)], [(600, 1600, 730, 1633)]], [[(1210, 1674, 1340, 1707)], [(1209, 2432, 1339, 2465)], [(1210, 1928, 1340, 1961)], [(1209, 2182, 1339, 2215)], [(605, 1573, 735, 1606)], [(1210, 2013, 1340, 2046)], [(605, 1362, 735, 1395)], [(1209, 2266, 1339, 2299)], [(1208, 2929, 1338, 2962)], [(1209, 2681, 1339, 2714)], [(1208, 3012, 1338, 3045)], [(1210, 1843, 1340, 1876)], [(1209, 2097, 1339, 2130)], [(605, 1432, 735, 1465)], [(1209, 2516, 1339, 2549)], [(1209, 2764, 1339, 2797)], [(1209, 2349, 1339, 2382)], [(605, 1503, 735, 1536)], [(1210, 1505, 1340, 1538)], [(1210, 1590, 1340, 1623)], [(1210, 1759, 1340, 1792)], [(1209, 2598, 1339, 2631)], [(1210, 1421, 1340, 1454)], [(1816, 2189, 1946, 2222)], [(1817, 1507, 1947, 1540)], [(1815, 2940, 1945, 2973)], [(1815, 3023, 1945, 3056)], [(1209, 2847, 1339, 2880)], [(1817, 1592, 1947, 1625)], [(1817, 1422, 1947, 1455)], [(1816, 2597, 1946, 2630)], [(1817, 2020, 1947, 2053)], [(1817, 1760, 1947, 1793)], [(1815, 2515, 1945, 2548)], [(1816, 2104, 1946, 2137)], [(1815, 2857, 1945, 2890)], [(1817, 1676, 1947, 1709)], [(1816, 2273, 1946, 2306)]], [[(601, 1527, 731, 1560)], [(601, 1598, 731, 1631)], [(601, 532, 731, 565)], [(601, 1122, 731, 1155)], [(601, 746, 731, 779)], [(601, 675, 731, 708)], [(601, 1193, 731, 1226)], [(601, 603, 731, 636)]], [[(1209, 2186, 1339, 2219)], [(1208, 2602, 1338, 2635)], [(1209, 2101, 1339, 2134)], [(1210, 1932, 1340, 1965)], [(606, 1435, 736, 1468)], [(1210, 2017, 1340, 2050)], [(1207, 2934, 1337, 2967)], [(1208, 2520, 1338, 2553)], [(1210, 1762, 1340, 1795)], [(1209, 2353, 1339, 2386)], [(1209, 2271, 1339, 2304)], [(1814, 2602, 1944, 2635)], [(1816, 1764, 1946, 1797)], [(1208, 2685, 1338, 2718)], [(1210, 1678, 1340, 1711)], [(1813, 3027, 1943, 3060)], [(1210, 1594, 1340, 1627)], [(1210, 1848, 1340, 1881)], [(1207, 3016, 1337, 3049)], [(1211, 1424, 1341, 1457)], [(1208, 2436, 1338, 2469)], [(1211, 1509, 1341, 1542)], [(1816, 2024, 1946, 2057)], [(605, 1364, 735, 1397)], [(1817, 1510, 1947, 1543)], [(1814, 2520, 1944, 2553)], [(1815, 2278, 1945, 2311)], [(1208, 2768, 1338, 2801)], [(1815, 2194, 1945, 2227)], [(1816, 2109, 1946, 2142)], [(1817, 1425, 1947, 1458)], [(1814, 2944, 1944, 2977)], [(1816, 1679, 1946, 1712)], [(1817, 1596, 1947, 1629)], [(1814, 2862, 1944, 2895)], [(1207, 2852, 1337, 2885)]], [[(604, 606, 734, 639)], [(603, 1532, 733, 1565)], [(603, 1603, 733, 1636)], [(604, 678, 734, 711)], [(604, 1125, 734, 1158)], [(604, 534, 734, 567)], [(604, 1196, 734, 1229)], [(604, 748, 734, 781)]]])
    exit(0)
    equ_class(*pickle.load(open("/tmp/aaa")))
    exit(0)
    paths = eval(open("../orangedata_paths").read())
    lookup = dict((x,i) for i,x in enumerate(paths))
    languages = eval(open("../orangedata_lang").read())
    languages = dict((lookup[k],v) for k,v in languages.items())
    
    equ_class(merge_contests(*pickle.load(open("../orangedata"))), languages)

    from labelcontest import LabelContest
    p = "../projects/label_grouping/"
    # Regroup the targets so that equal contests are merged.
    class FakeProj:
        target_locs_dir = p+"target_locations"
    class FakeMe(LabelContest):
        proj = FakeProj()
    fakeme = FakeMe(None, None)
    LabelContest.gatherData(fakeme)
    groupedtargets = fakeme.groupedtargets
    targets = []
    for bid,ballot in enumerate(groupedtargets):
        ballotlist = []
        for gid,targlist in enumerate(ballot):
            ballotlist.append([x[2:] for x in targlist])
        targets.append(ballotlist)

    internal = pickle.load(open(p+"contest_internal.p"))[2]
    print type(internal)
    print final_grouping(internal, targets)
