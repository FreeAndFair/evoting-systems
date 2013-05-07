function createPolynomial() {
    var form = document.forms.createPolynomialForm;
    form.createPoly.disabled = true;
    var user = form.user.value;
    var procedure = form.procedure.value;
    var keyStr = form.keyStr.value;
    var threshold = form.threshold.value;
    var adder = document.getElementById("adderObject");
    var result = null;

    try {
        result = adder.encryptPoly(user, procedure, keyStr, threshold);
    } catch (e) {
        alert("Error: " + e);
    }

    if (result == null) {
        alert("Error: Failed to encrypt polynomial");
        form.createPolynomial.disabled = false;
        return false;
    } else {
        form.authPolynomial.value = result;
    }

    var gValues = null;

    try {
        gValues = adder.encryptGValue(user, procedure);
    } catch (e) {
        alert("Error: " + e);
    }

    if (gValues == null) {
        alert("Error: Failed to encrypt g values");
        form.createPolynomial.disabled = false;
    } else {
        form.gValues.value = gValues;
        form.submit();
        return true;
    }

    return false;
}
