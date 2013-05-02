GRANT ALL ON adder.* TO adder_su@localhost IDENTIFIED BY 'password';

GRANT SELECT, INSERT, UPDATE, DELETE ON adder.is_authority TO adder_admin@localhost IDENTIFIED BY 'password';
GRANT SELECT, INSERT ON adder.proc TO adder_admin@localhost;
GRANT SELECT, INSERT ON adder.proc_choice TO adder_admin@localhost;
GRANT SELECT, INSERT ON adder.proc_data TO adder_admin@localhost;
GRANT SELECT, INSERT, UPDATE ON adder.users TO adder_admin@localhost;

GRANT SELECT ON adder.choice TO adder_auditor@localhost IDENTIFIED BY 'password';
GRANT SELECT ON adder.proc TO adder_auditor@localhost;
GRANT SELECT ON adder.proc_choice TO adder_auditor@localhost;
GRANT SELECT ON adder.proc_pubkey TO adder_auditor@localhost;
GRANT SELECT ON adder.preresult TO adder_auditor@localhost;
GRANT SELECT ON adder.pubkey TO adder_auditor@localhost;
GRANT SELECT ON adder.result TO adder_auditor@localhost;

GRANT INSERT ON adder.preresult TO adder_authority@localhost IDENTIFIED BY 'password';
GRANT INSERT ON adder.pubkey TO adder_authority@localhost;

GRANT SELECT, UPDATE ON adder.proc_data TO adder_server@localhost IDENTIFIED BY 'password';
GRANT INSERT ON adder.proc_pubkey TO adder_server@localhost;
GRANT SELECT ON adder.preresult TO adder_server@localhost;
GRANT INSERT ON adder.result TO adder_server@localhost;

GRANT INSERT ON adder.choice TO adder_user@localhost IDENTIFIED BY 'password';
GRANT SELECT ON adder.proc TO adder_user@localhost;
GRANT SELECT ON adder.proc_choice TO adder_user@localhost;
GRANT SELECT ON adder.proc_pubkey TO adder_user@localhost;
GRANT SELECT ON adder.users TO adder_user@localhost;
