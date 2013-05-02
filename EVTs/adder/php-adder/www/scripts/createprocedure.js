function validateSentence(elem) {
    var regex = /^.*(\s?.*)*$/;
    var str = elem.value;

    if (!str || str.length == 0) {
        return false;
    }

    if (str.match(regex)) {
        return true;
    } else {
        alert("Please enter a valid sentence");
        elem.select();
        elem.focus();
        return false;
    }
}

function validateNumber(elem) {
    var regex = /^[0-9]+[0-9]*$/;
    var str = elem.value;

    if (!str || str.length == 0) {
        return false;
    }

    if (str.match(regex)) {
        return true;
    } else {
        alert("Please enter a valid number");
        elem.select();
        elem.focus();
        return false;
    }
}

function validateTime(elem) {
    /* FIXME: How can we validate this without going through PHP? */
    return validateSentence(elem);
}

function validateChoices() {
    var regex = /^(.*(\s?.*)*)(\n\w+(\s?.*)*)*$/;
    var elem = document.forms.createProcedureForm.choices;
    var str = elem.value;

    if (!str || str.length == 0) {
        return false;
    }

    str = str.replace(/(.*)\s*$/, "$1");

    if (str.match(regex)) {
        return true;
    } else {
        alert("Please enter a valid set of choices");
        elem.select();
        elem.focus();
        return false;
    }
}

function validateAuthorities() {
    var elem = document.forms.createProcedureForm.authorities;

    if (elem.selectedIndex != -1) {
        return true;
    } else {
        alert("Please select at least one authority for the procedure");
        elem.focus();
        return false;
    }
}

function validateAll() {
    if (!validateSentence(document.forms.createProcedureForm.title)) {
        return false;
    }

    if (!validateNumber(document.forms.createProcedureForm.threshold)) {
        return false;
    }

    if (!validateTime(document.forms.createProcedureForm.publickeytime)) {
        return false;
    }

    if (!validateTime(document.forms.createProcedureForm.polynomialtime)) {
        return false;
    }

    if (!validateTime(document.forms.createProcedureForm.secretkeytime)) {
        return false;
    }

    if (!validateTime(document.forms.createProcedureForm.votetime)) {
        return false;
    }

    if (!validateNumber(document.forms.createProcedureForm.keylength)) {
        return false;
    }

    if (!validateNumber(document.forms.createProcedureForm.robustness)) {
        return false;
    }

    if (!validateSentence(document.forms.createProcedureForm.text)) {
        return true;
    }

    if (!validateChoices()) {
        return false;
    }

    if (!validateAuthorities()) {
        return false;
    }

    return true;
}

function validateForm() {
    if (validateAll()) {
        document.forms.createProcedureForm.submit();
        return true;
    } else {
        alert("One or more form values you entered are invalid");
        return false;
    }
}

