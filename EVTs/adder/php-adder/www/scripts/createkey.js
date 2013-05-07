function createKeyPair() {
    var form = document.forms.createKeyForm;
    form.createKey.disabled = true;
    form.submitKey.disabled = true;
    var user = form.user.value;
    var procedure = form.procedure.value;
    var keyConstants = form.keyConstants.value;
    var adder = document.getElementById("adderObject");
    var result = false;

    try {
        result = adder.createKeyPair(user, procedure, keyConstants, false);
    } catch (e) {
        alert("Error: " + e);
    }

    if (result == true) {
        alert("Your private keypair has been created and stored in your home directory.");
        form.createKey.disabled = true;
        form.submitKey.disabled = false;
    } else {
        alert("Error: Failed to create keypair");
        form.createKey.disabled = false;
    }

    return result;
}

function readPubKey() {
    var form = document.forms.createKeyForm;
    form.submitKey.disabled = true;
    var user = form.user.value;
    var procedure = form.procedure.value;
    var adder = document.getElementById("adderObject");
    var pubKey = null;

    try {
        pubKey = adder.readPubKey(user, procedure);
    } catch (e) {
        alert("Error: " + e);
    }

    if (pubKey == null) {
        alert("Error: Failed to read public key");
        form.submitKey.disabled = false;
     } else {
         form.authPubKey.value = pubKey;
         form.submit();
         return true;
     }

     return true;
}
