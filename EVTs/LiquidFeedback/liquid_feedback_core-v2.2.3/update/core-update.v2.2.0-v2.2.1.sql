BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('2.2.1', 2, 2, 1))
  AS "subquery"("string", "major", "minor", "revision");

ALTER TABLE "initiative" ADD COLUMN "final_suggestion_order_calculated" BOOLEAN NOT NULL DEFAULT FALSE;
COMMENT ON COLUMN "initiative"."final_suggestion_order_calculated" IS 'Set to TRUE, when "proportional_order" of suggestions has been calculated the last time';

ALTER TABLE "suggestion" ADD COLUMN "proportional_order" INT4;
COMMENT ON COLUMN "suggestion"."proportional_order" IS 'To be used for sorting suggestions within an initiative; NULL values sort last; updated by "lf_update_suggestion_order"';

CREATE VIEW "initiative_suggestion_order_calculation" AS
  SELECT
    "initiative"."id" AS "initiative_id",
    ("issue"."closed" NOTNULL OR "issue"."fully_frozen" NOTNULL) AS "final"
  FROM "initiative" JOIN "issue"
  ON "initiative"."issue_id" = "issue"."id"
  WHERE ("issue"."closed" ISNULL AND "issue"."fully_frozen" ISNULL)
  OR ("initiative"."final_suggestion_order_calculated" = FALSE);
COMMENT ON VIEW "initiative_suggestion_order_calculation" IS 'Initiatives, where the "proportional_order" of its suggestions has to be calculated';
COMMENT ON COLUMN "initiative_suggestion_order_calculation"."final" IS 'Set to TRUE, if the issue is fully frozen or closed, and the calculation has to be done only once for one last time';

CREATE VIEW "individual_suggestion_ranking" AS
  SELECT
    "opinion"."initiative_id",
    "opinion"."member_id",
    "direct_interest_snapshot"."weight",
    CASE WHEN
      ("opinion"."degree" = 2 AND "opinion"."fulfilled" = FALSE) OR
      ("opinion"."degree" = -2 AND "opinion"."fulfilled" = TRUE)
    THEN 1 ELSE
      CASE WHEN
        ("opinion"."degree" = 1 AND "opinion"."fulfilled" = FALSE) OR
        ("opinion"."degree" = -1 AND "opinion"."fulfilled" = TRUE)
      THEN 2 ELSE
        CASE WHEN
          ("opinion"."degree" = 2 AND "opinion"."fulfilled" = TRUE) OR
          ("opinion"."degree" = -2 AND "opinion"."fulfilled" = FALSE)
        THEN 3 ELSE 4 END
      END
    END AS "preference",
    "opinion"."suggestion_id"
  FROM "opinion"
  JOIN "initiative" ON "initiative"."id" = "opinion"."initiative_id"
  JOIN "issue" ON "issue"."id" = "initiative"."issue_id"
  JOIN "direct_interest_snapshot"
    ON  "direct_interest_snapshot"."issue_id" = "issue"."id"
    AND "direct_interest_snapshot"."event" = "issue"."latest_snapshot_event"
    AND "direct_interest_snapshot"."member_id" = "opinion"."member_id";
COMMENT ON VIEW "individual_suggestion_ranking" IS 'Helper view for "lf_update_suggestion_order" to allow a proportional ordering of suggestions within an initiative';

COMMIT;
