// FIXME: How do we remove the + from URL's?
function confirmAdvanceProcedure(proc, procName, queryString) {
    var warning = "Manually advance procedure to the \
next stage?\n\nNote that advancing the stage of an active procedure may make \
it impossible to recover the results of a procedure.";

    if (confirm(warning)) {
        document.location = "procadmin.php?" + queryString;
    }
}

function confirmResetProcedure(proc, procName, queryString) {
    var warning = "Manually end procedure?\n\n Note \
that stopping an active procedure which has not yet ended will restart the \
procedure from the beginning and may make it impossible to recover the \
results of a procedure."

    if (confirm(warning)) {
        document.location = "procadmin.php?" + queryString;
    }
}

function confirmDeleteProcedure(proc, procName, queryString) {
    var warning = "Manually delete procedure?\n\n \
Note that deleting an active procedure which has not yet ended may make it \
impossible to recover the results of a procedure.";

    if (confirm(warning)) {
        document.location = "procadmin.php?" + queryString;
    }
}
