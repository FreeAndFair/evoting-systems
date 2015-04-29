import tevsgui

class Status(object):
      def __init__(self,statusbar):
            self.statusbar = statusbar
            self.context = self.statusbar.get_context_id("Basic")

	  
      def update(self,text,context=None):
            if context is None:
                  self.statusbar.push(self.context,text)
            else:
                  self.context = self.statusbar.get_context_id(context)
                  try:
                        self.statusbar.pop(self.context)
                  except Exception, e:
                        print e
                  self.statusbar.push(self.context,text)
                  self.context = self.statusbar.get_context_id("Basic")
                  
if __name__ == "__main__":
   print "status = Status(statusbar widget)"
