import pygtk
pygtk.require('2.0')
import gobject
import gtk
import string

class BrowsingException(Exception):
    def __init__(self,value):
        self.value = value
    def __str__(self):
        return repr(self.value)


def do_modal_dialog(text,window):
    dialog = gtk.Dialog(text,
                window,
                gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT,
                (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT,
                 gtk.STOCK_OK, gtk.RESPONSE_ACCEPT))
    label = gtk.Label(text)
    dialog.vbox.pack_start(label, True, True, 0)
    label.show()
    retval = dialog.run()
    dialog.destroy()
    return retval

def showinfo(title,text,window):
    dialog = gtk.Dialog(title,
                window,
                gtk.DIALOG_DESTROY_WITH_PARENT,
                 (gtk.STOCK_OK, gtk.RESPONSE_ACCEPT))
    label = gtk.Label(text)
    dialog.vbox.pack_start(label, True, True, 0)
    label.show()
    retval = dialog.run()
    dialog.destroy()
    return retval

def askyesno(text1,text2,window):
    dialog = gtk.Dialog(text1,
                window,
                gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT,
                (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT,
                 gtk.STOCK_OK, gtk.RESPONSE_ACCEPT))
    label = gtk.Label(text2)
    dialog.vbox.pack_start(label, True, True, 0)
    label.show()
    retval = dialog.run()
    dialog.destroy()
    return retval

def askstring(title,summarytext,labeltext,window):
    dialog = gtk.Dialog(title,
                window,
                gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT,
                (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT,
                 gtk.STOCK_OK, gtk.RESPONSE_ACCEPT))
    hbox = gtk.HBox()
    label = gtk.Label(labeltext)
    entry = gtk.Entry()
    hbox.pack_start(label, False, False, 0)
    hbox.pack_start(entry, True, True, 0)
    dialog.vbox.pack_start(gtk.Label(summarytext),True,True,0)
    dialog.vbox.pack_start(hbox, True, True, 0)
    label.show()
    entry.show()
    hbox.show()
    dialog.vbox.show()
    retval = dialog.run()
    if retval == gtk.RESPONSE_ACCEPT:
        retstr = entry.get_text()
        dialog.destroy()
    else:
        retstr = ""
    return retstr

def askinteger(title,summarytext,labeltext,initial_value):
    dialog = gtk.Dialog(title,
                window,
                gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT,
                (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT,
                 gtk.STOCK_OK, gtk.RESPONSE_ACCEPT))
    hbox = gtk.HBox()
    label = gtk.Label(labeltext)
    entry = gtk.SpinButton()
    entry.set_range(0,30)
    entry.set_value(initial_value)

    hbox.pack_start(label, False, False, 0)
    hbox.pack_start(entry, True, True, 0)
    dialog.vbox.pack_start(gtk.Label(summarytext),True,True,0)
    dialog.vbox.pack_start(hbox, True, True, 0)
    label.show()
    entry.show()
    hbox.show()
    dialog.vbox.show()
    retval = dialog.run()
    if retval == gtk.RESPONSE_ACCEPT:
        retint = entry.get_value_as_int()
        dialog.destroy()
    else:
        retint = "-1"
    return retint

