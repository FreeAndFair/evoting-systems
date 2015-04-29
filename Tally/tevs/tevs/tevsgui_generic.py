import gtk
import sys
import tevsgui_generic_svc
import pdb

class gui(object):

    def stdout_cb(self,char):
        print char
        return True

    def start_cb(self,button,data):
        print "Starting service"
        self.svc = tevsgui_generic_svc.Service(
            ["/usr/bin/python","tevsgui_generic_client.py"]
            )

    def send_cb(self,button,data):
        print "Sending [",data,"]"
        self.send(data)

    def __init__(self):
        self.window = gtk.Window()
        self.vbox = gtk.VBox()
        self.window.add(self.vbox)
        self.btn1 = gtk.Button("Start")
        self.btn1.connect("clicked",self.start_cb,"hello")
        self.btn2 = gtk.Button("Send hello")
        self.btn2.connect("clicked",self.send_cb,"data\n")
        self.vbox.pack_start(self.btn1)
        self.vbox.pack_start(self.btn2)
        self.window.show_all()
        self.svc = None
        #self.svc = Service(["ls",])
        #self.svc = Service(["/usr/bin/python","tevsgui_generic_client.py"])
        #self.svc = Service(["bash",])
        #print "Svc",self.svc
        #self.svc.send("+\n")

    def send(self,data):
        self.svc.send(data)
        print "Sent data to",self.svc
        return True

if __name__ == "__main__":
    gui1 = gui()
    gtk.main()
    
