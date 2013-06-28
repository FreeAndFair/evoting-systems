BEGIN;

-- update version number:
CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('2.0.2', 2, 0, 2))
  AS "subquery"("string", "major", "minor", "revision");

-- add column "authentication" to table "member":
ALTER TABLE "member" ADD COLUMN "authentication" TEXT;
COMMENT ON COLUMN "member"."authentication" IS 'Information about how this member was authenticated';

COMMIT;
