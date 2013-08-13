import wx, pdb

"""
The interface for all OpenCount UI components.
"""

class OpenCountPanel(wx.Panel):
    def __init__(self, *args, **kwargs):
        wx.Panel.__init__(self, *args, **kwargs)
        
        # self.sanitychecks_callbacks: maps {int ID_FLAG: fn callback}
        #     This is used to (optionally) allow each widget to add
        #     special handling for certain failed sanity checks. For
        #     instance, the UI could direct the user to a particular
        #     page(s) which failed a check.
        #     Each callback F must accept a single argument DATA, which
        #     is specific to each sanity check. F should return a bool:
        #     True if the user is allowed to continue, or False o.w.
        #     This allows 'conditionally'-fatal errors, depending on
        #     the user's own judgement.
        self.sanitychecks_callbacks = {}

    def can_move_on(self, *args, **kwargs):
        """ Performs sanity checks to see if the user can move onto the
        next tab. Returns True if the user can move on, False o.w.
        This method is allowed to raise Dialogs to inform the user about
        various things.
        """
        status = self.run_sanity_checks()
        if status:
            print "...All Sanity Checks Passed, can proceed."
        else:
            print "...Sanity Checks NOT Passed, will not proceed."
        return status

    def run_sanity_checks(self, *args, **kwargs):
        """ Performs sanity checks to see if everything seems correct
        and normal. Returns True if all non-fatal tests pass, False o.w.
        """
        can_go_on = True
        lst_statuses = self.invoke_sanity_checks()
        
        for (isok, isfatal, msg, id_flag, data) in lst_statuses:
            if not isok:
                if isfatal:
                    can_go_on = False

                _title = "OpenCount Warning" if not isfatal else "OpenCount Fatal Warning"
                wx.MessageDialog(self, message=msg, caption=_title, style=wx.OK).ShowModal()

                callback_fn = self.sanitychecks_callbacks.get(id_flag, None)
                if callback_fn:
                    user_judgement = callback_fn(data)
                else:
                    user_judgement = True

                if user_judgement == False:
                    # User indicated that this was a fatal error
                    can_go_on = False
                    break # No sense in continuing to yell at the user

        return can_go_on

    def invoke_sanity_checks(self, *args, **kwargs):
        """ Code that actually calls each sanity-check with application
        specific arguments. Outputs a list of statuses, like:

            [(bool isOk, bool isFatal, str msg, int id_flag, obj data), ...]

        This should be overridden by each class.
        """
        return []

    def add_sanity_check_callback(self, id_flag, fn):
        """ Register a callback function to be called if a particular
        sanity check ID_FLAG fails. A useful use-case for this is for the
        application to gain control of the UI, and direct the user to
        where the sanity checks failed.
        Input:
            int ID_FLAG: 
                The (unique) int identifier of the sanity check
            function FN:
                The callback function. It should accept a single argument
                DATA, which is entirely determined by the output of
                invoke_sanity_checks() [the last element of each tuple].
        Output:
            True if FN was successfully registered, False o.w.
        """
        self.sanitychecks_callbacks[id_flag] = fn
        return True
