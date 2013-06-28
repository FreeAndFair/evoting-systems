BEGIN;
 
CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.2.7', 1, 2, 7))
  AS "subquery"("string", "major", "minor", "revision");

DROP VIEW "global_delegation";

CREATE VIEW "global_delegation" AS
  SELECT "id", "truster_id", "trustee_id"
  FROM "active_delegation" WHERE "scope" = 'global';

COMMIT;
