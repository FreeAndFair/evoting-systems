function checkBox(elem) {
    var form = document.forms.securityForm;
    var num = form.num.value;
    var min = form.min.value;
    var max = form.max.value;
    var numSelected = 0;

    for (var i = 0; i < num; i++) {
        var vote = form.vote[i];
        if (vote.checked == true) {
            numSelected++;
        }
    }
    
    if (numSelected < max) {
        for (var i = 0; i < num; i++) {
            var vote = form.vote[i];

            if (vote.disabled == true) {
                vote.disabled = false;
            }
        }
    } else {
        for (var i = 0; i < num; i++) {
            var vote = form.vote[i];

            if (vote.checked == false) {
                vote.disabled = true;
            }
        }
    }
}

function clearBoxes() {
    var form = document.forms.securityForm;
    var num = form.num.value;

    for (var i = 0; i < num; i++) {
        var vote = form.vote[i];
        vote.checked = false;
        vote.disabled = false;
    }
}

function encryptVote() {
    var form = document.forms.securityForm;
    form.submitVote.disabled = true;
    var serverPublicKey = form.serverPublicKey.value;
    var voteString = "";
    var min = form.min.value;
    var max = form.max.value;
    var num = form.num.value;
    var numSelected = 0;

    for (var i = 0; i < num; i++) {
        var vote = form.vote[i];

        if (vote.checked == true) {
            voteString += "1";
            numSelected++;
        } else {
            voteString += "0";
        }
    }

    if (numSelected >= min && numSelected <= max) {
        var adder = document.getElementById("adderObject");
        var encryptedVote = null;

        try {
            encryptedVote = adder.encryptVote(serverPublicKey, voteString, min, max);
        } catch (e) {
            alert("Error: " + e);
        }

        /*var shortHash = null;

        try {
            shortHash = adder.shortHash(encryptedVote);
        } catch (e) {
            alert("Error: " + e);
        }*/

        if (encryptedVote == null || encryptedVote.length == 0 /*|| shortHash == null */) {
            alert("Error: Failed to encrypt ballot");
        } else if (confirm("Submit ballot?")) {
            var form = document.forms.securityForm;
            form.encryptedVote.value = encryptedVote;
            form.submit();
            return true;
        }
    } else {
        alert("Error: You must select the correct number of choices");
    }

    clearBoxes();

    form.submitVote.disabled = false;
    return false;
}
