BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.2.4', 1, 2, 4))
  AS "subquery"("string", "major", "minor", "revision");

-- no changes in database scheme except version number

COMMIT;
