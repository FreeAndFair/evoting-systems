var adder = document.getElementById("adderObject");

function savePrivateKey() {
    var user = document.forms.getKeyForm.user.value;
    var procedure = document.forms.getKeyForm.procedure.value;
    var privkey = document.forms.getKeyForm.privateKey.value;
    var result = adder.writePrivKey(user, procedure, privkey);

    if (result == true) {
        alert("Private key saved successfully");
    } else {
        alert("Error: Failed to save private key");
    }

    return result;
}

