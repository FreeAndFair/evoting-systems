import glib
import pdb
import subprocess

extraction_stdin = None
extraction_stdout = None
extraction_stderr = None
extraction_pid = None
extraction_object = None
extraction_process_output = ""


def set_up_extraction_process(status):
    """ 
    run process_ballot_on_input in separate Python, 
    asking it to extract one ballot per request and print back
    the number of the processed ballot.  
    """
    global extraction_stdin
    global extraction_stdout
    global extraction_stderr
    global extraction_object
    global extraction_pid
    try:
        extraction_object = subprocess.Popen(
            ["/usr/bin/python", "process_ballot_on_input.py"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            close_fds = True)
        extraction_pid = extraction_object.pid
        (extraction_stdin,
         extraction_stdout,
         extraction_stderr) = (extraction_object.stdin,
                               extraction_object.stdout,
                               extraction_object.stderr)
        glib.io_add_watch(extraction_object.stdout,
                          glib.IO_IN,
                          data_available_from_extraction_process, status)
        glib.io_add_watch(extraction_object.stdout,
                          glib.IO_HUP,
                          extraction_process_done, status)
        return extraction_pid

    except Exception,e:
        print e
        return -1
            
def take_down_extraction_process():
    """terminate extraction and reset related variables"""
    global extraction_stdin
    global extraction_stdout
    global extraction_stderr
    global extraction_object
    global extraction_pid
    status.update("Ending extraction process.")
    extraction_object.kill()
    extraction_pid = None
    extraction_stdin = None
    extraction_stdout = None
    extraction_stderr = None


def extraction_process_done(fd,condition,status):
    """extraction process ended; reset related variables"""
    global extraction_stdin
    global extraction_stdout
    global extraction_stderr
    global extraction_object
    global extraction_pid
    if condition == glib.IO_HUP:
        extraction_object = None
        extraction_pid = None
        extraction_stdin = None
        extraction_stdout = None
        extraction_stderr = None
        status.update("Extraction process has ended.")
    return False

def data_available_from_extraction_process(fd,condition,status):
    """ extraction will prompt for number of ballots to scan, ending with ?
        We accumulate output and send request for 1 more ballot at ?.
    """
    global extraction_process_output
    global extraction_stdin
    global extraction_stdout
    global extraction_stderr
    global extraction_pid
    if condition == glib.IO_IN:
        char = fd.read(1)
        extraction_process_output = "%s%s" % (
            extraction_process_output,char)
        # support process will send "!" to request shutdown, 
        # "?" or ":" to request next instruction
        if char == '?' or char == ':' :
            print extraction_process_output
            #basic_cid = status.get_context_id("Basic")
            #status.push(extraction_process_output) 
            status.update(extraction_process_output)
            extraction_process_output = ""
            print "Requesting next ballot"
            # extraction process accepts:
            # S for single (counts one more ballot)
            # + for increment next_ballot_count by const.num_pages, process one
            # =nnn for set next_ballot_count to nnn, process one 
            # 0 for no more requests, shut down extraction
            extraction_stdin.write("S\n")
            extraction_stdin.flush()
        elif char == '!':
            # request for process shutdown (or for a delayed retry)
            print "Requesting process shutdown"
            extraction_stdin.write("0\n")
            extraction_stdin.flush()
        else: 
            print char,
        return True
    else:
        print "Got wrong condition from glib"
        return False
