function decryptSum() {
    var form = document.forms.decryptionForm;
    form.submitDecryption.disabled = true;
    var user = form.user.value;
    var procedure = form.procedure.value;
    var cipherSum = form.cipherSum.value;
    var adder = document.getElementById("adderObject");
    var result = null;

    try {
        result = adder.decryptSum(user, procedure, cipherSum);
    } catch (e) {
        alert("Error: " + e);
    }

    if (result != null) {
        form.partialDecryption.value = result;
        form.submit();
    } else {
        alert("Error: Failed to decrypt sum");
        form.submitDecryption.disabled = false;
    }

    return result;
}
