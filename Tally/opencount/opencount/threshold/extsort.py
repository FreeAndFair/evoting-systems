from heapq import heapify, heappop, heappush
from itertools import islice, cycle
from tempfile import gettempdir
import os, traceback, pdb

""" An external merge-sort implementation. Useful when you need to sort
a file that is too large to fit in memory.

Modified from: 
    http://www.cs.sunysb.edu/~algorith/implement/psort/implement.shtml
"""

def merge(chunks,key=None):
    if key is None:
        key = lambda x : x

    values = []

    for index, chunk in enumerate(chunks):
        try:
            iterator = iter(chunk)
            value = iterator.next()
        except StopIteration:
            try:
                chunk.close()
                os.remove(chunk.name)
                chunks.remove(chunk)
            except:
                pass
        else:
            heappush(values,((key(value),index,value,iterator,chunk)))

    while values:
        k, index, value, iterator, chunk = heappop(values)
        yield value
        try:
            value = iterator.next()
        except StopIteration:
            try:
                chunk.close()
                os.remove(chunk.name)
                chunks.remove(chunk)
            except:
                pass
        else:
            heappush(values,(key(value),index,value,iterator,chunk))

def batch_sort(input,output,key=None,buffer_size=32000,tempdirs=[]):
    if not tempdirs:
        tempdirs.append(gettempdir())
    
    input_file = file(input,'rb',64*1024)
    try:
        input_iterator = iter(input_file)
        
        chunks = []
        try:
            for tempdir in cycle(tempdirs):
                current_chunk = list(islice(input_iterator,buffer_size))
                if current_chunk:
                    current_chunk.sort(key=key)
                    output_chunk = file(os.path.join(tempdir,'%06i'%len(chunks)),'w+b',64*1024)
                    output_chunk.writelines(current_chunk)
                    output_chunk.flush()
                    output_chunk.seek(0)
                    chunks.append(output_chunk)
                else:
                    break
        except:
            for chunk in chunks:
                try:
                    chunk.close()
                    os.remove(chunk.name)
                except:
                    pass
            if output_chunk not in chunks:
                try:
                    output_chunk.close()
                    os.remove(output_chunk.name)
                except:
                    pass
            return
    finally:
        input_file.close()
    
    output_file = file(output,'wb',64*1024)
    try:
        output_file.writelines(merge(chunks,key))
    finally:
        for chunk in chunks:
            try:
                chunk.close()
                os.remove(chunk.name)
            except:
                pass
        output_file.close()

def merge_mod(chunks,cidx2offset,imgSize,key=None,DELETE_CHUNKS=True):
    if key is None:
        key = lambda x : x

    values = []
    cidx2curtidx = {} # maps {int chunkindex: int targetidx}

    for index, chunk in enumerate(chunks):
        cidx2curtidx[index] = cidx2offset[index]
        try:
            iterator = iter_targets_file(chunk, imgSize)
            value = iterator.next()
        except StopIteration:
            try:
                chunk.close()
                if DELETE_CHUNKS:
                    os.remove(chunk.name)
                chunks.remove(chunk)
            except:
                pass
        else:
            heappush(values,((key(cidx2curtidx[index]),index,value,iterator,chunk)))
    while values:
        k, index, value, iterator, chunk = heappop(values)
        yield value
        try:
            value = iterator.next()
            cidx2curtidx[index] += 1
        except StopIteration:
            try:
                chunk.close()
                if DELETE_CHUNKS:
                    os.remove(chunk.name)
                chunks.remove(chunk)
            except:
                pass
        else:
            heappush(values,(key(cidx2curtidx[index], value),index,value,iterator,chunk))

def iter_targets(fname, targetsize):
    """ Reads a binary file FNAME and outputs bytes in a target-by-target
    fashion.
    """
    with open(fname, 'rb') as f:
        while True:
            chunk = f.read(targetsize)
            if chunk:
                yield chunk
            else:
                break
def iter_targets_file(f, targetsize):
    """ Reads a binary file F and outputs bytes in a target-by-target
    fashion.
    """
    while True:
        chunk = f.read(targetsize)
        if chunk:
            yield chunk
        else:
            break


def batch_sort_mod(input,output,imgSize,key=None,
                   buffer_size=32000,tempdirs=[],
                   fn_ignore=None,
                   DELETE_TEMPFILES=True):
    if not tempdirs:
        tempdirs.append(gettempdir())
    
    try:
        input_iterator = iter_targets(input, imgSize)
        offset_tidx = 0
        chunks = []
        cidx2offset = {} # maps {int chunkidx: int tidx_offset}
        cidx = 0 # chunk index
        total_targets_written = 0
        try:
            for tempdir in cycle(tempdirs):
                current_chunk = list(islice(input_iterator,buffer_size))
                if current_chunk:
                    '''
                    tidx_low, tidx_high, names = get_names(cur_tidx)
                    idxs_tosort = []
                    for tidx in xrange(len(chunk_data)):
                        tidx_low, tidx_high, idxfpath, names = get_names(cur_tidx)
                        idxs_tosort.append((tidx - tidx_low, idxfpath))
                    sort_order = sorted(idxs_tosort, key=lambda tidx, idxfpath: idxfpath2names[idxfpath][tidx])
                    sorted_chunk = [current_chunk[i] for i in sort_order]
                    '''
                    # SORT_ORDER: [int sortval/None, ...]. None if the target was quarantined
                    # and should be ignored
                    sort_order = [key(i + offset_tidx) for i in xrange(len(current_chunk))]
                    # First, filter out the quarantined targets
                    sorted_chunk = [(i, tdata) for (i, tdata) in enumerate(current_chunk) if sort_order[i] != None]
                    # Second, sort the targets by the sort criterion (avg intensity)
                    sorted_chunk = sorted(sorted_chunk, key=lambda (i, tdata): sort_order[i])
                    #sorted_chunk = sorted(enumerate(current_chunk), key=lambda (tidx, target): key(offset_tidx + tidx))
                    output_chunk = file(os.path.join(tempdir,'%06i'%len(chunks)),'w+b',64*1024)
                    for (i, target) in sorted_chunk:
                        output_chunk.write(target)
                    output_chunk.flush()
                    output_chunk.seek(0)
                    chunks.append(output_chunk)
                    cidx2offset[cidx] = offset_tidx
                    offset_tidx += len(current_chunk)
                    cidx += 1
                    total_targets_written += len(current_chunk)
                else:
                    break
        except Exception as e:
            traceback.print_exc()
            pdb.set_trace()
            for chunk in chunks:
                try:
                    chunk.close()
                    os.remove(chunk.name)
                except:
                    pass
            if output_chunk not in chunks:
                try:
                    output_chunk.close()
                    os.remove(output_chunk.name)
                except:
                    pass
            return
    finally:
        pass
    
    output_file = file(output,'wb',64*1024)
    try:
        for thing in merge_mod(chunks, cidx2offset, imgSize, key, DELETE_CHUNKS=DELETE_TEMPFILES):
            output_file.write(thing)
    finally:
        for chunk in chunks:
            try:
                chunk.close()
                if DELETE_TEMPFILES:
                    os.remove(chunk.name)
            except:
                pass
        output_file.close()

    return total_targets_written

if __name__ == '__main__':
    import optparse
    parser = optparse.OptionParser()
    parser.add_option(
        '-b','--buffer',
        dest='buffer_size',
        type='int',default=32000,
        help='''Size of the line buffer. The file to sort is
            divided into chunks of that many lines. Default : 32,000 lines.'''
    )
    parser.add_option(
        '-k','--key',
        dest='key',
        help='''Python expression used to compute the key for each
            line, "lambda line:" is prepended.\n
            Example : -k "line[5:10]". By default, the whole line is the key.'''
    )
    parser.add_option(
        '-t','--tempdir',
        dest='tempdirs',
        action='append',
        default=[],
        help='''Temporary directory to use. You might get performance
            improvements if the temporary directory is not on the same physical
            disk than the input and output directories. You can even try
            providing multiples directories on differents physical disks.
            Use multiple -t options to do that.'''
    )
    parser.add_option(
        '-p','--psyco',
        dest='psyco',
        action='store_true',
        default=False,
        help='''Use Psyco.'''
    )
    options,args = parser.parse_args()
    
    if options.key:
        options.key = eval('lambda line : (%s)'%options.key)
    
    if options.psyco:
        import psyco
        psyco.full()
    
    batch_sort(args[0],args[1],options.key,options.buffer_size,options.tempdirs) 
