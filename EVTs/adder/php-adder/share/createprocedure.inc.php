<?php require_once 'header.inc.php' ?>
  <script type="text/javascript" src="scripts/createprocedure.js">
  </script>
</head>

<body>

<div class="container">

<?php include 'sidebar.inc.php' ?>
<div class="mainContent">

<h1>Procedure Creation</h1>
<?php
if (isset($errors) && is_array($errors) && count($errors) > 0) {
    require_once 'error.inc.php';
    exit();
}
?>
    <p>To create a new procedure, fill in the form below. See the <a href="#help">Help</a> section at the bottom of this page 
for a description of each field.</p>
    <div class="form">
    <form id="createProcedureForm" action="procadmin.php" method="post">
    <div class="row">
    <input type="hidden" id="createSubmitted" name="createSubmitted" value="<?php echo (isset($submit_count) && is_numeric($submit_count) ? $submit_count : 1); ?>" />
    </div>
    <div class="row">
    <a id="ret_title"></a>
    <span class="label">Displayed title (<a href="#help_title">Help</a>):</span>
    <span class="formw"><input type="text" id="title" name="title" maxlength="255" onchange="validateSentence(this)" /></span><br />
    </div>

    <div class="row">
    <a id="ret_threshold"></a>
    <span class="label">Authority threshold (<a href="#help_threshold">Help</a>):</span>
    <span class="formw"><input type="text" id="threshold" name="threshold" maxlength="3" onchange="validateNumber(this)" /></span><br />
    </div>

    <div class="row">
    <a id="ret_robustness"></a>
    <span class="label">Robustness factor (<a href="#help_robustness">Help</a>):</span>
    <span class="formw"><input type="text" id="robustness" name="robustness" maxlength="3" value="1" onchange="validateNumber(this)" /></span><br />
    </div>
    
    <!-- BEGIN DURATIONS -->
    <div>
    <a id="ret_dur"></a>
    <p>Procedure stage durations (<a href="#help_dur">Help</a>):</p>
    <div class="row">
    <a id="ret_publickeytime"></a>
    <span class="label">Public key submission duration (<a href="#help_publickeytime">Help</a>):</span>
    <span class="formw"><input type="text" id="publickeytime" name="publickeytime" maxlength="255" onchange="validateTime(this)" /></span><br />
    </div>
   
    <div class="row">
    <a id="ret_polynomialtime"></a>
    <span class="label">Secret share submission duration (<a href="#help_polynomialtime">Help</a>):</span>
    <span class="formw"><input type="text" id="polynomialtime" name="polynomialtime" maxlength="255" onchange="validateTime(this)" /></span><br />
    </div>

    <div class="row">
    <a id="ret_secretkeytime"></a>
    <span class="label">Secret key duration (<a href="#help_secretkeytime">Help</a>):</span>
    <span class="formw"><input type="text" id="secretkeytime" name="secretkeytime" maxlength="255" onchange="validateTime(this)" /></span><br />
    </div>

    <div class="row">
    <a id="ret_votetime"></a>
    <span class="label">Ballot casting duration (<a href="#help_votetime">Help</a>):</span>
    <span class="formw"><input type="text" id="votetime" name="votetime" maxlength="255" onchange="validateTime(this)" /></span><br />
    </div>

    </div>
    <!-- END DURATIONS -->

    <div class="row">
    <a id="ret_min"></a>
    <span class="label">Minimum choices (<a href="#help_min">Help</a>):</span>
    <span class="formw"><input type="text" id="min" name="min" maxlength="255" onchange="validateNumber(this)" /></span><br />
    </div>

    <div class="row">
    <a id="ret_max"></a>
    <span class="label">Maximum choices (<a href="#help_max">Help</a>):</span>
    <span class="formw"><input type="text" id="max" name="max" maxlength="255" onchange="validateNumber(this)" /></span><br />
    </div>

    <div class="row">
    <span class="formw"><input type="hidden" id="keylength" name="keylength" maxlength="4" value="1024" onchange="validateNumber(this)" /></span>
    </div>

    <div class="row"><br />
    <a id="ret_text"></a>
    <span class="label">Ballot question (<a href="#help_text">Help</a>):</span><br />
    <span class="bigelement"><input type="text" id="text" name="text" size="70" maxlength="255" onchange="validateSentence(this)" /></span><br />
    </div>
    <div class="row"><br />
    <a id="ret_choices"></a>
    <span class="label">Choices, enter one per line (<a href="#help_choices">Help</a>):</span><br />
    <span class="bigelement"><textarea id="choices" name="choices" rows="10" cols="40" onchange="validateChoices(this)"></textarea></span><br />
    </div>
    

    <div class="row"><br />
    <a id="ret_authorities"></a>
    <span class="label">Select one or more users to serve as authorities for this procedure (<a href="#help_authorities">Help</a>):</span>
    <span class="bigelement"><br />
    <select id="authorities" name="authorities[]" multiple="multiple" size="10" onchange="validateAuthorities()">
    <?php
    $auth_count = 0;
    sort($users);
    foreach ($users as $user) {
        if ($user != "") {
            $auth_count++;

            echo "<option id=\"authority" . $auth_count . "\">" . $user . "</option>";
        }
    }
?>
    </select></span></div>

    <div class="row formbuttons">
    <input type="button" id="create_procedure" name="create_procedure"
    value="Create Procedure" onclick="validateForm()" />
    <input type="reset" />
    </div>
    </form>
</div>
<hr />
<a id="help"></a>
<h3 style="text-align: center">Help</h3>
<dl>
    <dt><a id="help_title"></a>Displayed title:</dt>
    <dd>This is the title that will be shown to the users.<br />
    <em>Example: Choice for President</em>. (<a href="#ret_title">Back</a>)</dd>

    <dt><a id="help_threshold"></a>Authority threshold:</dt>
    <dd>The minimum number of authorities required to officiate a procedure.
    This could be any number less than or equal to the number of voters. (<a href="#ret_threshold">Back</a>)</dd>

    <dt><a id="help_robustness"></a>Robustness factor:</dt>
    <dd>This specifies what multiple of the threshold of authorities is required to participate. If in doubt, just enter 1. (<a href="#ret_robustness">Back</a>)</dd>

    <dt><a id="help_publickeytime"></a>Public key submission duration:</dt>
    <dd>The amount of time alloted for the public key submission stage. (<a href="#ret_publickeytime">Back</a>)</dd>

    <dt><a id="help_polynomialtime"></a>Secret share submission duration:</dt>
    <dd>The amount if time alloted for the secret share submission stage. (<a href="#ret_polynomialtime">Back</a>)</dd>

    <dt><a id="help_secretkeytime"></a>Secret key duration:</dt>
    <dd>The amount of time alloted for the stage in which the authorities create their secret keys. (<a href="#ret_secretkeytime">Back</a>)</dd>

    <dt><a id="help_votetime"></a>Ballot casting duration:</dt>
    <dd>The amount of time alloted for the voting stage. (<a href="#ret_votetime">Back</a>)</dd>

    <dt><a id="help_text"></a>Ballot question:</dt>
    <dd>This is the question displayed to the users when they vote.<br />
    <em>Example: Choose a President.</em> (<a href="#ret_text">Back</a>)</dd>

    <dt><a id="help_min"></a>Minimum choices:</dt>
    <dd>The minimum number of choices that a voter is allowed to select. (<a href="#ret_min">Back</a>)</dd>

    <dt><a id="help_max"></a>Maximum choices:</dt>
    <dd>The maximum number of choices that a voter is allowed to select. (<a href="#ret_max">Back</a>)</dd>

    <dt><a id="help_choices"></a>Choices:</dt>
    <dd>The choices available to the voter. You must enter one per line. (<a href="#ret_choices">Back</a>)</dd>

    <dt><a id="help_authorities"></a>Authorites:</dt>
    <dd>Select which users are eligible to serve as authorities.  
    It is better to choose a large number of authorities, even if you are 
not sure if all of them will participate. You must select a number of 
authorities that is greater than or equal to the threshold times the 
robustness factor that you selected. (<a href="#ret_authorities">Back</a>)</dd>
</dl>
<hr />
    <p><a id="help_dur"></a>Procedure stage durations</p>

    <p>You may enter either a time relative to the time you start the procedure or
       an absolute date and time.</p>

    <p>Examples:</p>

    <ul>
      <li>1 year 2 months 3 hours 4 minutes 5 seconds</li>
      <li>November 10, 2005 12:58:30 EST</li>
    </ul>

    <p>Standard abbreviations:</p>

    <ul>
      <li>November = Nov</li>
      <li>minutes = mins = min</li>
      <li>seconds = secs = sec</li>
    </ul>
    <p>(<a href="#ret_dur">Back</a>)</p>

<?php include 'footer.inc.php' ?>
</div>

</div>

</body>

</html>
