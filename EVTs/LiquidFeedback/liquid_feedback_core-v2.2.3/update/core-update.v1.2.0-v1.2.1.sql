BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.2.1', 1, 2, 1))
  AS "subquery"("string", "major", "minor", "revision");

ALTER TABLE "issue" ADD COLUMN "cleaned" TIMESTAMPTZ;
ALTER TABLE "issue" ADD CONSTRAINT "clean_restriction"
  CHECK (
    "cleaned" ISNULL OR (
      "closed" NOTNULL AND (
        "fully_frozen" ISNULL OR "ranks_available"
      )
    )
  );

COMMENT ON COLUMN "issue"."cleaned" IS 'Point in time, when discussion data and votes had been deleted';

CREATE FUNCTION "clean_issue"("issue_id_p" "issue"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row" "issue"%ROWTYPE;
    BEGIN
      SELECT * INTO "issue_row"
        FROM "issue" WHERE "id" = "issue_id_p"
        FOR UPDATE;
      IF "issue_row"."cleaned" ISNULL THEN
        UPDATE "issue" SET
          "closed" = NULL,
          "ranks_available" = FALSE
          WHERE "id" = "issue_id_p";
        DELETE FROM "delegating_voter"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "direct_voter"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "delegating_interest_snapshot"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "direct_interest_snapshot"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "delegating_population_snapshot"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "direct_population_snapshot"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "delegation"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "supporter"
          WHERE "issue_id" = "issue_id_p";
        UPDATE "issue" SET
          "closed"          = "issue_row"."closed",
          "ranks_available" = "issue_row"."ranks_available",
          "cleaned"         = now()
          WHERE "id" = "issue_id_p";
      END IF;
      RETURN;
    END;
  $$;

COMMENT ON FUNCTION "clean_issue"("issue"."id"%TYPE) IS 'Delete discussion data and votes belonging to an issue';

COMMIT;
