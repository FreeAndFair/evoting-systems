function validateUsername(elem) {
    var regex = /^\w+([-+.]\w+)*(@\w+([-.]\w+)*(\.\w+))?$/;
    var str = elem.value;

    if (!str || str.length == 0) {
        return false;
    }

    if (str.match(regex)) {
        return true;
    } else {
       alert("Please enter a valid username");
       elem.select();
       return false;
    }
}

function validatePassword(elem) {
    var regex = /^[^\s]{8,15}$/;
    var str = elem.value;

    if (!str || str.length == 0) {
        return false;
    }

    if (str.match(regex)) {
        return true;
    } else {
       alert("Please enter a valid password (between 8 and 15 characters long)");
       elem.select();
       return false;
    }
}

function validateAll() {
    if (!validateUsername(document.forms.loginForm.user)) {
        return false;
    }

    if (!validatePassword(document.forms.loginForm.password)) {
        return false;
    }

    return true;
}

