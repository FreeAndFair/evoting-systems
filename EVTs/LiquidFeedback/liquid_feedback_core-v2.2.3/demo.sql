-- NOTE: This file requires that sequence generators have not been used.
-- (All new rows need to start with id '1'.)

BEGIN;

INSERT INTO "system_setting" ("member_ttl") VALUES ('31 days');

INSERT INTO "contingent" ("time_frame", "text_entry_limit", "initiative_limit") VALUES
  ('60 minutes', 6, 1),
  ('1 day', 60, 10),
  ('1 week', 120, 20);

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
    "indirect_majority_num", "indirect_majority_den", "indirect_majority_strict",
    "no_reverse_beat_path", "no_multistage_majority"
  ) VALUES (
    1,
    'amendment of the statutes (solar system)',
    '8 days', '15 days', '8 days', '15 days',
    10, 100,
    10, 100,
    1, 2, TRUE,
    2, 3, FALSE,
    TRUE, FALSE
  ), (
    2,
    'amendment of the statutes (earth moon federation)',
    '8 days', '15 days', '8 days', '15 days',
    10, 100,
    10, 100,
    1, 2, TRUE,
    2, 3, FALSE,
    TRUE, FALSE
  ), (
    3,
    'amendment of the statutes (united mars colonies)',
    '8 days', '15 days', '8 days', '15 days',
    10, 100,
    10, 100,
    1, 2, TRUE,
    2, 3, FALSE,
    TRUE, FALSE
  ), (
    4,
    'proposition',
    '8 days', '15 days', '8 days', '15 days',
    10, 100,
    10, 100,
    1, 2, TRUE,
    1, 2, TRUE,
    TRUE, FALSE
  ), (
    5,
    'non-binding survey',
    '2 days', '3 days', '2 days', '3 days',
    5, 100,
    5, 100,
    1, 2, TRUE,
    1, 2, TRUE,
    TRUE, FALSE
  ), (
    6,
    'non-binding survey (super fast)',
    '1 hour', '30 minutes', '15 minutes', '30 minutes',
    5, 100,
    5, 100,
    1, 2, TRUE,
    1, 2, TRUE,
    TRUE, FALSE
  );

INSERT INTO "unit" ("parent_id", "name") VALUES
  (NULL, 'Solar System'),           -- id 1
  (1   , 'Earth Moon Federation'),  -- id 2
  (2   , 'Earth'),                  -- id 3
  (2   , 'Moon'),                   -- id 4
  (1   , 'Mars');                   -- id 5

INSERT INTO "area" ("unit_id", "name") VALUES
  ( 1, 'Statutes of the United Solar System'),       -- id  1
  ( 2, 'Statutes of the Earth Moon Federation'),     -- id  2
  ( 5, 'Statutes of the United Mars Colonies'),      -- id  3
  ( 1, 'Intra solar space travel'),                  -- id  4
  ( 1, 'Intra solar system trade and taxation'),     -- id  5
  ( 1, 'Comet defense and black holes management'),  -- id  6
  ( 1, 'Alien affairs'),                             -- id  7
  ( 2, 'Foreign affairs'),                           -- id  8
  ( 3, 'Moon affairs'),                              -- id  9
  ( 4, 'Earth affairs'),                             -- id 10
  ( 4, 'Moon tourism'),                              -- id 11
  ( 5, 'Foreign affairs'),                           -- id 12
  ( 2, 'Department of space vehicles'),              -- id 13
  ( 3, 'Environment'),                               -- id 14
  ( 4, 'Energy and oxygen'),                         -- id 15
  ( 5, 'Energy and oxygen'),                         -- id 16
  ( 5, 'Mineral resources');                         -- id 17

INSERT INTO "allowed_policy" ("area_id", "policy_id", "default_policy") VALUES
  ( 1, 1, TRUE),
  ( 1, 5, FALSE),
  ( 1, 6, FALSE),
  ( 2, 2, TRUE),
  ( 2, 5, FALSE),
  ( 2, 6, FALSE),
  ( 3, 3, TRUE),
  ( 3, 5, FALSE),
  ( 3, 6, FALSE),
  ( 4, 4, TRUE),
  ( 4, 5, FALSE),
  ( 4, 6, FALSE),
  ( 5, 4, TRUE),
  ( 5, 5, FALSE),
  ( 5, 6, FALSE),
  ( 6, 4, TRUE),
  ( 6, 5, FALSE),
  ( 6, 6, FALSE),
  ( 7, 4, TRUE),
  ( 7, 5, FALSE),
  ( 7, 6, FALSE),
  ( 8, 4, TRUE),
  ( 8, 5, FALSE),
  ( 8, 6, FALSE),
  ( 9, 4, TRUE),
  ( 9, 5, FALSE),
  ( 9, 6, FALSE),
  (10, 4, TRUE),
  (10, 5, FALSE),
  (10, 6, FALSE),
  (11, 4, TRUE),
  (11, 5, FALSE),
  (11, 6, FALSE),
  (12, 4, TRUE),
  (12, 5, FALSE),
  (12, 6, FALSE),
  (13, 4, TRUE),
  (13, 5, FALSE),
  (13, 6, FALSE),
  (14, 4, TRUE),
  (14, 5, FALSE),
  (14, 6, FALSE),
  (15, 4, TRUE),
  (15, 5, FALSE),
  (15, 6, FALSE),
  (16, 4, TRUE),
  (16, 5, FALSE),
  (16, 6, FALSE),
  (17, 4, TRUE),
  (17, 5, FALSE),
  (17, 6, FALSE);

END;

