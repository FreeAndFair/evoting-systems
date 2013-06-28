-- NOTE: This file creates an admin user with an empty password!

BEGIN;

INSERT INTO "unit" (
        "active",
        "name",
        "description"
    ) VALUES (
        true,
        'Default unit',
        'Default unit created by init script.'
    );
        

INSERT INTO "member" (
        "login",
        "password",
        "active",
        "admin",
        "name",
        "activated",
        "last_activity"
    ) VALUES (
        'admin',
        '$1$.EMPTY.$LDufa24OE2HZFXAXh71Eb1',
        TRUE,
        TRUE,
        'Administrator',
        NOW(),
        NOW()
    );

INSERT INTO "policy" (
        "index",
        "active",
        "name",
        "description",
        "admission_time",
        "discussion_time",
        "verification_time",
        "voting_time",
        "issue_quorum_num",
        "issue_quorum_den",
        "initiative_quorum_num",
        "initiative_quorum_den"
    ) VALUES (
        1,
        TRUE,
        'Extensive proceeding',
        DEFAULT,
        '1 month',
        '5 months',
        '1 month',
        '3 weeks',
        10, 100,
        10, 100
    ), (
        2,
        TRUE,
        'Standard proceeding',
        DEFAULT,
        '1 month',
        '1 month',
        '1 week',
        '1 week',
        10, 100,
        10, 100
    ), (
       3,
       TRUE,
       'Fast proceeding',
       DEFAULT,
       '48 hours',
       '3 hours',
       '1 hour',
       '20 hours',
        1, 100,
        1, 100 );

INSERT INTO "area" (
        "unit_id",
        "active",
        "name",
        "description"
    ) VALUES (
        1,
        TRUE,
        'Generic area',
        DEFAULT );

COMMIT;
