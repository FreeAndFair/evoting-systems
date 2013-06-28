-- NOTE: This file requires that sequence generators have not been used.
-- (All new rows need to start with id '1'.)

BEGIN;

-- set transaction isolation level to be able to call "check_everything"() function
SET TRANSACTION ISOLATION LEVEL REPEATABLE READ;

INSERT INTO "member" ("activated", "last_activity", "active", "login", "name") VALUES
  ('now', 'now', TRUE, 'user1',  'User #1'),   -- id  1
  ('now', 'now', TRUE, 'user2',  'User #2'),   -- id  2
  ('now', 'now', TRUE, 'user3',  'User #3'),   -- id  3
  ('now', 'now', TRUE, 'user4',  'User #4'),   -- id  4
  ('now', 'now', TRUE, 'user5',  'User #5'),   -- id  5
  ('now', 'now', TRUE, 'user6',  'User #6'),   -- id  6
  ('now', 'now', TRUE, 'user7',  'User #7'),   -- id  7
  ('now', 'now', TRUE, 'user8',  'User #8'),   -- id  8
  ('now', 'now', TRUE, 'user9',  'User #9'),   -- id  9
  ('now', 'now', TRUE, 'user10', 'User #10'),  -- id 10
  ('now', 'now', TRUE, 'user11', 'User #11'),  -- id 11
  ('now', 'now', TRUE, 'user12', 'User #12'),  -- id 12
  ('now', 'now', TRUE, 'user13', 'User #13'),  -- id 13
  ('now', 'now', TRUE, 'user14', 'User #14'),  -- id 14
  ('now', 'now', TRUE, 'user15', 'User #15'),  -- id 15
  ('now', 'now', TRUE, 'user16', 'User #16'),  -- id 16
  ('now', 'now', TRUE, 'user17', 'User #17'),  -- id 17
  ('now', 'now', TRUE, 'user18', 'User #18'),  -- id 18
  ('now', 'now', TRUE, 'user19', 'User #19'),  -- id 19
  ('now', 'now', TRUE, 'user20', 'User #20'),  -- id 20
  ('now', 'now', TRUE, 'user21', 'User #21'),  -- id 21
  ('now', 'now', TRUE, 'user22', 'User #22'),  -- id 22
  ('now', 'now', TRUE, 'user23', 'User #23');  -- id 23

-- set password to "login"
UPDATE "member" SET "password" = '$1$PcI6b1Bg$2SHjAZH2nMLFp0fxHis.Q0';

INSERT INTO "policy" (
    "index",
    "name",
    "admission_time",
    "discussion_time",
    "verification_time",
    "voting_time",
    "issue_quorum_num", "issue_quorum_den",
    "initiative_quorum_num", "initiative_quorum_den",
    "direct_majority_num", "direct_majority_den", "direct_majority_strict",
    "no_reverse_beat_path", "no_multistage_majority"
  ) VALUES (
    1,
    'Default policy',
    '1 hour', '1 hour', '1 hour', '1 hour',
    25, 100,
    20, 100,
    1, 2, TRUE,
    TRUE, FALSE );

CREATE FUNCTION "time_warp"() RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      UPDATE "issue" SET
        "snapshot"     = "snapshot"     - '1 hour 1 minute'::INTERVAL,
        "created"      = "created"      - '1 hour 1 minute'::INTERVAL,
        "accepted"     = "accepted"     - '1 hour 1 minute'::INTERVAL,
        "half_frozen"  = "half_frozen"  - '1 hour 1 minute'::INTERVAL,
        "fully_frozen" = "fully_frozen" - '1 hour 1 minute'::INTERVAL;
      PERFORM "check_everything"();
      RETURN;
    END;
  $$;

INSERT INTO "unit" ("name") VALUES ('Main');

INSERT INTO "privilege" ("unit_id", "member_id", "voting_right")
  SELECT 1 AS "unit_id", "id" AS "member_id", TRUE AS "voting_right"
  FROM "member";

INSERT INTO "area" ("unit_id", "name") VALUES
  (1, 'Area #1'),  -- id 1
  (1, 'Area #2'),  -- id 2
  (1, 'Area #3'),  -- id 3
  (1, 'Area #4');  -- id 4

INSERT INTO "allowed_policy" ("area_id", "policy_id", "default_policy")
  VALUES (1, 1, TRUE), (2, 1, TRUE), (3, 1, TRUE), (4, 1, TRUE);

INSERT INTO "membership" ("area_id", "member_id") VALUES
  (1,  9),
  (1, 19),
  (2,  9),
  (2, 10),
  (2, 17),
  (3,  9),
  (3, 11),
  (3, 12),
  (3, 14),
  (3, 20),
  (3, 21),
  (3, 22),
  (4,  6),
  (4,  9),
  (4, 13),
  (4, 22);

-- global delegations
INSERT INTO "delegation"
  ("truster_id", "scope", "unit_id", "trustee_id") VALUES
  ( 1, 'unit', 1,  9),
  ( 2, 'unit', 1, 11),
  ( 3, 'unit', 1, 12),
  ( 4, 'unit', 1, 13),
  ( 5, 'unit', 1, 14),
  ( 6, 'unit', 1,  7),
  ( 7, 'unit', 1,  8),
  ( 8, 'unit', 1,  6),
  (10, 'unit', 1,  9),
  (11, 'unit', 1,  9),
  (12, 'unit', 1, 21),
  (15, 'unit', 1, 10),
  (16, 'unit', 1, 17),
  (17, 'unit', 1, 19),
  (18, 'unit', 1, 19),
  (23, 'unit', 1, 22);

-- delegations for topics
INSERT INTO "delegation"
  ("area_id", "truster_id", "scope", "trustee_id") VALUES
  (1,  3, 'area', 17),
  (2,  5, 'area', 10),
  (2,  9, 'area', 10),
  (3,  4, 'area', 14),
  (3, 16, 'area', 20),
  (3, 19, 'area', 20),
  (4,  5, 'area', 13),
  (4, 12, 'area', 22);

INSERT INTO "issue" ("area_id", "policy_id") VALUES
  (3, 1);  -- id 1

INSERT INTO "initiative" ("issue_id", "name") VALUES
  (1, 'Initiative #1'),  -- id 1
  (1, 'Initiative #2'),  -- id 2
  (1, 'Initiative #3'),  -- id 3
  (1, 'Initiative #4'),  -- id 4
  (1, 'Initiative #5'),  -- id 5
  (1, 'Initiative #6'),  -- id 6
  (1, 'Initiative #7');  -- id 7

INSERT INTO "draft" ("initiative_id", "author_id", "content") VALUES
  (1, 17, 'Lorem ipsum...'),  -- id 1
  (2, 20, 'Lorem ipsum...'),  -- id 2
  (3, 20, 'Lorem ipsum...'),  -- id 3
  (4, 20, 'Lorem ipsum...'),  -- id 4
  (5, 14, 'Lorem ipsum...'),  -- id 5
  (6, 11, 'Lorem ipsum...'),  -- id 6
  (7, 12, 'Lorem ipsum...');  -- id 7

INSERT INTO "initiator" ("initiative_id", "member_id") VALUES
  (1, 17),
  (1, 19),
  (2, 20),
  (3, 20),
  (4, 20),
  (5, 14),
  (6, 11),
  (7, 12);

INSERT INTO "supporter" ("member_id", "initiative_id", "draft_id") VALUES
  ( 7,  4,  4),
  ( 8,  2,  2),
  (11,  6,  6),
  (12,  7,  7),
  (14,  1,  1),
  (14,  2,  2),
  (14,  3,  3),
  (14,  4,  4),
  (14,  5,  5),
  (14,  6,  6),
  (14,  7,  7),
  (17,  1,  1),
  (17,  3,  3),
  (19,  1,  1),
  (19,  2,  2),
  (20,  1,  1),
  (20,  2,  2),
  (20,  3,  3),
  (20,  4,  4),
  (20,  5,  5);

INSERT INTO "suggestion" ("initiative_id", "author_id", "name", "content") VALUES
  (1, 19, 'Suggestion #1', 'Lorem ipsum...');  -- id 1
INSERT INTO "opinion" ("member_id", "suggestion_id", "degree", "fulfilled") VALUES
  (14, 1, 2, FALSE);
INSERT INTO "opinion" ("member_id", "suggestion_id", "degree", "fulfilled") VALUES
  (19, 1, 2, FALSE);

INSERT INTO "issue" ("area_id", "policy_id") VALUES
  (4, 1);  -- id 2

INSERT INTO "initiative" ("issue_id", "name") VALUES
  (2, 'Initiative A'),  -- id  8
  (2, 'Initiative B'),  -- id  9
  (2, 'Initiative C'),  -- id 10
  (2, 'Initiative D');  -- id 11

INSERT INTO "draft" ("initiative_id", "author_id", "content") VALUES
  ( 8, 1, 'Lorem ipsum...'),  -- id  8
  ( 9, 2, 'Lorem ipsum...'),  -- id  9
  (10, 3, 'Lorem ipsum...'),  -- id 10
  (11, 4, 'Lorem ipsum...');  -- id 11

INSERT INTO "initiator" ("initiative_id", "member_id") VALUES
  ( 8, 1),
  ( 9, 2),
  (10, 3),
  (11, 4);

INSERT INTO "supporter" ("member_id", "initiative_id", "draft_id") VALUES
  (1,  8,  8),
  (1,  9,  9),
  (1, 10, 10),
  (1, 11, 11),
  (2,  8,  8),
  (2,  9,  9),
  (2, 10, 10),
  (2, 11, 11),
  (3,  8,  8),
  (3,  9,  9),
  (3, 10, 10),
  (3, 11, 11),
  (4,  8,  8),
  (4,  9,  9),
  (4, 10, 10),
  (4, 11, 11),
  (5,  8,  8),
  (5,  9,  9),
  (5, 10, 10),
  (5, 11, 11),
  (6,  8,  8),
  (6,  9,  9),
  (6, 10, 10),
  (6, 11, 11);
 
SELECT "time_warp"();
SELECT "time_warp"();
SELECT "time_warp"();

INSERT INTO "direct_voter" ("member_id", "issue_id") VALUES
  ( 8, 1),
  ( 9, 1),
  (11, 1),
  (12, 1),
  (14, 1),
  (19, 1),
  (20, 1),
  (21, 1);

INSERT INTO "vote" ("member_id", "issue_id", "initiative_id", "grade") VALUES
  ( 8, 1, 1,  1),
  ( 8, 1, 2,  1),
  ( 8, 1, 3,  1),
  ( 8, 1, 4,  1),
  ( 8, 1, 5,  1),
  ( 8, 1, 6, -1),
  ( 8, 1, 7, -1),
  ( 9, 1, 1, -2),
  ( 9, 1, 2, -3),
  ( 9, 1, 3, -2),
  ( 9, 1, 4, -2),
  ( 9, 1, 5, -2),
  ( 9, 1, 6, -1),
  (11, 1, 1, -1),
  (11, 1, 2, -1),
  (11, 1, 3, -1),
  (11, 1, 4, -1),
  (11, 1, 5, -1),
  (11, 1, 6,  2),
  (11, 1, 7,  1),
  (12, 1, 1, -1),
  (12, 1, 3, -1),
  (12, 1, 4, -1),
  (12, 1, 5, -1),
  (12, 1, 6, -2),
  (12, 1, 7,  1),
  (14, 1, 1,  1),
  (14, 1, 2,  3),
  (14, 1, 3,  1),
  (14, 1, 4,  2),
  (14, 1, 5,  1),
  (14, 1, 6,  1),
  (14, 1, 7,  1),
  (19, 1, 1,  3),
  (19, 1, 2,  4),
  (19, 1, 3,  2),
  (19, 1, 4,  2),
  (19, 1, 5,  2),
  (19, 1, 7,  1),
  (20, 1, 1,  1),
  (20, 1, 2,  2),
  (20, 1, 3,  1),
  (20, 1, 4,  1),
  (20, 1, 5,  1),
  (21, 1, 5, -1);

INSERT INTO "direct_voter" ("member_id", "issue_id") VALUES
  ( 1, 2),
  ( 2, 2),
  ( 3, 2),
  ( 4, 2),
  ( 5, 2),
  ( 6, 2),
  ( 7, 2),
  ( 8, 2),
  ( 9, 2),
  (10, 2),
  (11, 2),
  (12, 2),
  (13, 2),
  (14, 2),
  (15, 2),
  (16, 2),
  (17, 2),
  (18, 2),
  (19, 2),
  (20, 2);

INSERT INTO "vote" ("member_id", "issue_id", "initiative_id", "grade") VALUES
  ( 1, 2,  8,  3),
  ( 1, 2,  9,  4),
  ( 1, 2, 10,  2),
  ( 1, 2, 11,  1),
  ( 2, 2,  8,  3),
  ( 2, 2,  9,  4),
  ( 2, 2, 10,  2),
  ( 2, 2, 11,  1),
  ( 3, 2,  8,  4),
  ( 3, 2,  9,  3),
  ( 3, 2, 10,  2),
  ( 3, 2, 11,  1),
  ( 4, 2,  8,  4),
  ( 4, 2,  9,  3),
  ( 4, 2, 10,  2),
  ( 4, 2, 11,  1),
  ( 5, 2,  8,  4),
  ( 5, 2,  9,  3),
  ( 5, 2, 10,  2),
  ( 5, 2, 11,  1),
  ( 6, 2,  8,  4),
  ( 6, 2,  9,  3),
  ( 6, 2, 10,  2),
  ( 6, 2, 11,  1),
  ( 7, 2,  8,  4),
  ( 7, 2,  9,  3),
  ( 7, 2, 10,  2),
  ( 7, 2, 11,  1),
  ( 8, 2,  8,  4),
  ( 8, 2,  9,  3),
  ( 8, 2, 10,  2),
  ( 8, 2, 11,  1),
  ( 9, 2,  8, -1),
  ( 9, 2,  9,  1),
  ( 9, 2, 10,  3),
  ( 9, 2, 11,  2),
  (10, 2,  8, -1),
  (10, 2,  9,  1),
  (10, 2, 10,  3),
  (10, 2, 11,  2),
  (11, 2,  8, -1),
  (11, 2,  9,  1),
  (11, 2, 10,  3),
  (11, 2, 11,  2),
  (12, 2,  8, -1),
  (12, 2,  9,  1),
  (12, 2, 10,  3),
  (12, 2, 11,  2),
  (13, 2,  8, -1),
  (13, 2,  9,  1),
  (13, 2, 10,  3),
  (13, 2, 11,  2),
  (14, 2,  8, -1),
  (14, 2,  9,  1),
  (14, 2, 10,  3),
  (14, 2, 11,  2),
  (15, 2,  8, -1),
  (15, 2,  9, -3),
  (15, 2, 10, -4),
  (15, 2, 11, -2),
  (16, 2,  8, -1),
  (16, 2,  9, -3),
  (16, 2, 10, -4),
  (16, 2, 11, -2),
  (17, 2,  8, -1),
  (17, 2,  9, -3),
  (17, 2, 10, -4),
  (17, 2, 11, -2),
  (18, 2,  8, -1),
  (18, 2,  9,  1),
  (18, 2, 10, -2),
  (18, 2, 11,  2),
  (19, 2,  8, -1),
  (19, 2,  9,  1),
  (19, 2, 10, -2),
  (19, 2, 11,  2),
  (20, 2,  8,  1),
  (20, 2,  9,  2),
  (20, 2, 10, -1),
  (20, 2, 11,  3);

SELECT "time_warp"();

DROP FUNCTION "time_warp"();

-- Test policies that help with testing specific frontend parts

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
        'Test New',
        DEFAULT,
        '2 days',
        '1 second',
        '1 second',
        '1 second',
        0, 100,
        0, 100
    ), (
        1,
        TRUE,
        'Test Accept',
        DEFAULT,
        '1 second',
        '2 days',
        '1 second',
        '1 second',
        0, 100,
        0, 100
    ), (
        1,
        TRUE,
        'Test Frozen',
        DEFAULT,
        '1 second',
        '5 minutes',
        '2 days',
        '1 second',
        0, 100,
        0, 100
    ), (
        1,
        TRUE,
        'Test Voting',
        DEFAULT,
        '1 second',
        '5 minutes',
        '1 second',
        '2 days',
        0, 100,
        0, 100
    );

END;

