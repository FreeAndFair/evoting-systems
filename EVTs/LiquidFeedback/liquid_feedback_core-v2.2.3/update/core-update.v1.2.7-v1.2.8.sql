BEGIN;
 
CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.2.8', 1, 2, 8))
  AS "subquery"("string", "major", "minor", "revision");

ALTER TABLE "delegation" DROP CONSTRAINT "delegation_area_id_key";
ALTER TABLE "delegation" DROP CONSTRAINT "delegation_issue_id_key";
DROP INDEX "delegation_global_truster_id_trustee_id_unique_idx";

ALTER TABLE "delegation" ADD UNIQUE ("area_id", "truster_id");
ALTER TABLE "delegation" ADD UNIQUE ("issue_id", "truster_id");
CREATE UNIQUE INDEX "delegation_global_truster_id_unique_idx"
  ON "delegation" ("truster_id") WHERE "scope" = 'global';

COMMIT;
