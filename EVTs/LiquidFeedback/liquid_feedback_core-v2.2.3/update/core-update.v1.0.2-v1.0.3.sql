BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.0.3', 1, 0, 3))
  AS "subquery"("string", "major", "minor", "revision");

DROP INDEX "delegating_voter_member_id_idx";
CREATE INDEX "delegating_voter_member_id_idx" ON "delegating_voter" ("member_id");

COMMIT;
