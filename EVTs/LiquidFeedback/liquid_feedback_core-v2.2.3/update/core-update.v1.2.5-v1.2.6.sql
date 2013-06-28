BEGIN;
 
CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.2.6', 1, 2, 6))
  AS "subquery"("string", "major", "minor", "revision");

CREATE VIEW "active_delegation" AS
  SELECT "delegation".* FROM "delegation"
  JOIN "member" ON "delegation"."truster_id" = "member"."id"
  WHERE "member"."active" = TRUE;

COMMENT ON VIEW "active_delegation" IS 'Delegations where the truster_id refers to an active member';

DROP VIEW "global_delegation";

CREATE VIEW "global_delegation" AS
  SELECT * FROM "active_delegation"
  WHERE "scope" = 'global';

COMMENT ON VIEW "global_delegation" IS 'Global delegations from active members';

CREATE OR REPLACE VIEW "area_delegation" AS
  SELECT DISTINCT ON ("area"."id", "delegation"."truster_id")
    "area"."id" AS "area_id",
    "delegation"."id",
    "delegation"."truster_id",
    "delegation"."trustee_id",
    "delegation"."scope"
  FROM "area" JOIN "active_delegation" AS "delegation"
  ON "delegation"."scope" = 'global'
  OR "delegation"."area_id" = "area"."id"
  ORDER BY
    "area"."id",
    "delegation"."truster_id",
    "delegation"."scope" DESC;

COMMENT ON VIEW "area_delegation" IS 'Resulting area delegations from active members';

CREATE OR REPLACE VIEW "issue_delegation" AS
  SELECT DISTINCT ON ("issue"."id", "delegation"."truster_id")
    "issue"."id" AS "issue_id",
    "delegation"."id",
    "delegation"."truster_id",
    "delegation"."trustee_id",
    "delegation"."scope"
  FROM "issue" JOIN "active_delegation" AS "delegation"
  ON "delegation"."scope" = 'global'
  OR "delegation"."area_id" = "issue"."area_id"
  OR "delegation"."issue_id" = "issue"."id"
  ORDER BY
    "issue"."id",
    "delegation"."truster_id",
    "delegation"."scope" DESC;

COMMENT ON VIEW "issue_delegation" IS 'Resulting issue delegations from active members';

COMMIT;
