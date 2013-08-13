import multiprocessing, random, math

"""
A utility script/tool that handles performing an embarassingly
parallelizable task.
I've done the same pattern enough times to tire of doing it again...
might as well abstract the pattern.
"""

def do_partask(fn, jobs, _args=None, blocking=True,
               combfn=None, init=None,
               pass_idx=False,
               singleproc=False,
               manager=None,
               pass_queue=None,
               N=None):
    """ The developer-facing main function. do_partask will split up
    'jobs' into N equally-sized chunks C_i, and apply 'fn' to each
    C_i in parallel, in addition to (optionally) providing additional
    arguments (from '_args', a list of things).
    Input:
        fn: A function that must be of the following signature:
              fn(list, arg_0, ..., arg_N)
            where each arg_i is optional, and provided by '_args'
        list jobs: A list of tasks, to be split up by do_partask.
            If JOBS is a dict, then it will be split up by keys.
        list _args: 
        bool blocking: 
        fn combfn: A combining function that must take two arguments
            combfn(T results, T* subresults) -> (T results*, int k)
        T init: Used with 'combfn', specifies the initial starting 
                value.
        bool pass_idx: If True, then the starting index w.r.t jobs will
                       be passed to 'fn' as the last argument.
        int N: Number of processors to use. If None, it will use the
            number of system cores.
    Output:
        The return value of calling 'fn' on all things in 'jobs', in a
        flat-list.
    TODO: non-blocking functionality is not implemented.
    """
    if singleproc or N == 1:
        moreargs = ()
        if pass_idx:
            moreargs += (0,)
        if pass_queue != None:
            moreargs += (pass_queue,)
        return fn(jobs, _args, *moreargs)

    if manager == None:
        print "...creating new Manager..."
        manager = multiprocessing.Manager()
    else:
        print "...Received Your Manager, roger..."
    queue = manager.Queue()

    p = multiprocessing.Process(target=spawn_jobs, args=(queue, fn, jobs, _args, pass_idx, pass_queue, N))
    p.start()

    num_jobs = len(jobs)
    if combfn == None:
        combfn = combfn_lst
        init = []
    elif combfn == 'dict':
        combfn = combfn_dict
        init = {}
    elif combfn == 'ignore':
        combfn = combfn_ignore
        init = True
        
    results = init
    while True:
        subresults = queue.get()
        if isinstance(subresults, POOL_CLOSED):
            return results
        results = combfn(results, subresults)
    return results

def combfn_ignore(res, subres):
    return True
def combfn_lst(res, subres):
    res.extend(subres)
    return res
def combfn_dict(res, subres):
    """ Assumes that res/subres maps keys to lists of values. """
    newres = dict(res)
    for k, v in subres.iteritems():
        newres.setdefault(k, []).extend(v)
    return newres

class POOL_CLOSED:
    """
    A dummy class to use to signal that the pool is finished
    processing.
    """
    def __init__(self):
        pass

_POOL_CLOSED = POOL_CLOSED()

def spawn_jobs(queue, fn, jobs, _args=None, pass_idx=False, pass_queue=None, N=None):
    def handle_result(result):
        queue.put(result)

    pool = multiprocessing.Pool()
    if N == None:
        n_procs = multiprocessing.cpu_count()
    else:
        n_procs = N
    cnt = 0
    for i, job in enumerate(divy_list(jobs, n_procs)):
        num_tasks = len(job)
        print "Process {0} got {1} tasks.".format(i, num_tasks)

        the_args = (job,)
        if _args != None:
            the_args += (_args,)
        if pass_idx == True:
            the_args += (cnt,)
        if pass_queue:
            the_args += (pass_queue,)
        pool.apply_async(fn, args=the_args, callback=handle_result)
        cnt += num_tasks
    pool.close()
    pool.join()
    queue.put(POOL_CLOSED())
    
def divy_list(lst, k):
    """ Divides input list into 'k' equally-sized chunks.
    Input:
        list lst: A list of stuff.
        int k: An integer.
    Output:
        K tuples.
    """
    dictflag = False
    if isinstance(lst, dict):
        dictflag = True
        lst = lst.items()

    if len(lst) <= k:
        if not dictflag:
            return [[thing] for thing in lst]
        else:
            return [dict([thing]) for thing in lst]
    chunksize = math.ceil(len(lst) / float(k))
    i = 0
    chunks = []
    curchunk = []
    while i < len(lst):
        if i != 0 and ((i % chunksize) == 0):
            chunks.append(curchunk)
            curchunk = []
        curchunk.append(lst[i])
        i += 1
    if curchunk:
        chunks.append(curchunk)
    if dictflag:
        chunks = [dict(c) for c in chunks]
    return chunks
    
"""
Test scripts. Refer to this usage to get an idea of how to use this
utility script.
"""

def square_nums(nums):
    return [x * x for x in nums]

def test0():
    nums = [random.random() for _ in range(1)]
    nums_squared = do_partask(square_nums, nums)
    print "Input nums:"
    print nums
    print "Output nums:"
    print nums_squared

def test0_a():
    nums = [random.random() for _ in range(2)]
    nums_squared = do_partask(square_nums, nums)
    print "Input nums:"
    print nums
    print "Output nums:"
    print nums_squared
    
def test1():
    nums = [random.random() for _ in range(10000)]
    # Fascinating -- 'square' must be defined as a function with 'def',
    # you can't just do:
    # square = lambda x: x * x
    nums_squared = do_partask(square_nums, nums)
    print "Input nums:"
    print nums[0:10]
    print "Output nums:"
    print nums_squared[0:10]

def eval_quadratic(nums, (a, b, c)):
    """ 
    Evalutes 'x' with the following quadratic:
        a*x**2 + b*x + c
    """
    return [a*(x**2) + b*x + c for x in nums]

def test2():
    nums = [random.random() for _ in range(10000)]
    result = do_partask(eval_quadratic, nums, _args=[4, 3, 2])
    print "Input nums:"
    print nums[0:4]
    print "Output nums:"
    print result[0:4]

def count_occurs(strs):
    res = {}
    for str in strs:
        if str in res:
            res[str] += 1
        else:
            res[str] = 1
    return res

def count_combfn(d, subd):
    """ Combines two dictionaries. """
    final_d = dict(d.items())
    for k, v in subd.iteritems():
        if k in final_d:
            final_d[k] += v
        else:
            final_d[k] = v
    return final_d

def test3():
    strs = ('a', 'a', 'a', 'a', 'a', 'a',
            'b', 'b', 'b', 'b',
            'c', 'c', 'c', 'c', 'c', 'c', 'c', 'c', 'c', 'c', 'c', 'c',
            'a', 'a',
            'z', 'z', 'z')
    counts = do_partask(count_occurs, strs, combfn=count_combfn, init={})
    print counts

def run_tests():
    print "==== Running tests..."
    print "== 1.) Square 1 number."
    test0()

    print "== 1.a.) Square 2 numbers."
    test0_a()

    print "== 2.) Square 10,000 numbers."
    test1()

    print "== 3.) Eval a quadratic-expression of 10,000 numbers."
    test2()

    print "== 4.) Counting occurrences of strings."
    test3()

    print "==== Completed tests."

if __name__ == '__main__':
    run_tests()
