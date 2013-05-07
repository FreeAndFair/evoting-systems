function validateUsername(elem) {
    var regex = /^\w+([-+.]\w+)*(@\w+([-.]\w+)*(\.\w+))?$/;
    var str = elem.value;

    if (!str || str.length == 0) {
        return false;
    }

    if (str.match(regex)) {
        return true;
    } else {
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
       elem.select();
       return false;
    }
}

function validateAll() {
    var form = document.forms.createUserForm;
    form.createUser.disabled = true;
    var error_msg = "";
    var error = false;

    if (!validateUsername(form.user)) {
        error_msg += "Please enter a valid username. ";
        error = true;
    }

    if (!validatePassword(form.password)) {
       error_msg += "Please enter a valid password (between 8 and 15 characters long) ";
       error = true;
    }

    if (!validatePassword(form.password2)) {
       error_msg += "Please enter a valid second password (between 8 and 15 characters long) ";
       error = true;
    }

    if (form.password.value != form.password2.value) {
        error_msg += "Your passwords do not match";
        error = true;
    }

    if (error) {
        alert(error_msg);
        form.createUser.disabled = false;
        return false;
    } else {
        form.submit();
        return true;
    }
}
