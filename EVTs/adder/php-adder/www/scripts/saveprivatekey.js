function savePrivateKey() {
    var form = document.forms.savePrivateKeyForm;
    form.saveKey.disabled = true;
    var user = form.user.value;
    var procedure = form.procedure.value;
    var privKeyComponents = form.privKeyComponents.value;
    var adder = document.getElementById("adderObject");
    var result = false;

    try {
        result = adder.computeSecretKey(user, procedure, privKeyComponents);
    } catch (e) {
        alert("Error: " + e);
    }

    if (result == true) {
        alert("The private key has been saved");
        form.submit();
    } else {
        alert("Error: Failed to save private key");
        form.saveKey.disabled = false;
    }

    return result;
}

