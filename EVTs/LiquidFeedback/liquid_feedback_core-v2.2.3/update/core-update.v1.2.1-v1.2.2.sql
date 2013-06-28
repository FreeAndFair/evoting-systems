BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.2.2', 1, 2, 2))
  AS "subquery"("string", "major", "minor", "revision");

ALTER TABLE "issue" DROP CONSTRAINT "clean_restriction";

ALTER TABLE "issue" ADD CONSTRAINT "only_closed_issues_may_be_cleaned"
  CHECK ("cleaned" ISNULL OR "closed" NOTNULL);

ALTER VIEW "battle" RENAME TO "battle_view";

CREATE TABLE "battle" (
        PRIMARY KEY ("issue_id", "winning_initiative_id", "losing_initiative_id"),
        "issue_id"              INT4,
        "winning_initiative_id" INT4,
        FOREIGN KEY ("issue_id", "winning_initiative_id") REFERENCES "initiative" ("issue_id", "id") ON DELETE CASCADE ON UPDATE CASCADE,
        "losing_initiative_id"  INT4,
        FOREIGN KEY ("issue_id", "losing_initiative_id") REFERENCES "initiative" ("issue_id", "id") ON DELETE CASCADE ON UPDATE CASCADE,
        "count"                 INT4            NOT NULL);

COMMENT ON TABLE "battle" IS 'Number of members preferring one initiative to another; Filled by "battle_view" when closing an issue';

CREATE OR REPLACE VIEW "battle_view" AS
  SELECT
    "issue"."id" AS "issue_id",
    "winning_initiative"."id" AS "winning_initiative_id",
    "losing_initiative"."id" AS "losing_initiative_id",
    sum(
      CASE WHEN
        coalesce("better_vote"."grade", 0) >
        coalesce("worse_vote"."grade", 0)
      THEN "direct_voter"."weight" ELSE 0 END
    ) AS "count"
  FROM "issue"
  LEFT JOIN "direct_voter"
  ON "issue"."id" = "direct_voter"."issue_id"
  JOIN "initiative" AS "winning_initiative"
    ON "issue"."id" = "winning_initiative"."issue_id"
    AND "winning_initiative"."agreed"
  JOIN "initiative" AS "losing_initiative"
    ON "issue"."id" = "losing_initiative"."issue_id"
    AND "losing_initiative"."agreed"
  LEFT JOIN "vote" AS "better_vote"
    ON "direct_voter"."member_id" = "better_vote"."member_id"
    AND "winning_initiative"."id" = "better_vote"."initiative_id"
  LEFT JOIN "vote" AS "worse_vote"
    ON "direct_voter"."member_id" = "worse_vote"."member_id"
    AND "losing_initiative"."id" = "worse_vote"."initiative_id"
  WHERE "issue"."closed" NOTNULL
  AND "issue"."cleaned" ISNULL
  AND "winning_initiative"."id" != "losing_initiative"."id"
  GROUP BY
    "issue"."id",
    "winning_initiative"."id",
    "losing_initiative"."id";

COMMENT ON VIEW "battle_view" IS 'Number of members preferring one initiative to another; Used to fill "battle" table';

INSERT INTO "battle" (
  "issue_id",
  "winning_initiative_id",
  "losing_initiative_id",
  "count"
) SELECT
  "issue_id",
  "winning_initiative_id", "losing_initiative_id",
  "count"
  FROM "battle_view";

CREATE OR REPLACE FUNCTION "close_voting"("issue_id_p" "issue"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row"   "issue"%ROWTYPE;
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "global_lock"();
      SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
      DELETE FROM "delegating_voter"
        WHERE "issue_id" = "issue_id_p";
      DELETE FROM "direct_voter"
        WHERE "issue_id" = "issue_id_p"
        AND "autoreject" = TRUE;
      DELETE FROM "direct_voter" USING "member"
        WHERE "direct_voter"."member_id" = "member"."id"
        AND "direct_voter"."issue_id" = "issue_id_p"
        AND "member"."active" = FALSE;
      UPDATE "direct_voter" SET "weight" = 1
        WHERE "issue_id" = "issue_id_p";
      PERFORM "add_vote_delegations"("issue_id_p");
      FOR "member_id_v" IN
        SELECT "interest"."member_id"
          FROM "interest"
          LEFT JOIN "direct_voter"
            ON "interest"."member_id" = "direct_voter"."member_id"
            AND "interest"."issue_id" = "direct_voter"."issue_id"
          LEFT JOIN "delegating_voter"
            ON "interest"."member_id" = "delegating_voter"."member_id"
            AND "interest"."issue_id" = "delegating_voter"."issue_id"
          WHERE "interest"."issue_id" = "issue_id_p"
          AND "interest"."autoreject" = TRUE
          AND "direct_voter"."member_id" ISNULL
          AND "delegating_voter"."member_id" ISNULL
        UNION SELECT "membership"."member_id"
          FROM "membership"
          LEFT JOIN "interest"
            ON "membership"."member_id" = "interest"."member_id"
            AND "interest"."issue_id" = "issue_id_p"
          LEFT JOIN "direct_voter"
            ON "membership"."member_id" = "direct_voter"."member_id"
            AND "direct_voter"."issue_id" = "issue_id_p"
          LEFT JOIN "delegating_voter"
            ON "membership"."member_id" = "delegating_voter"."member_id"
            AND "delegating_voter"."issue_id" = "issue_id_p"
          WHERE "membership"."area_id" = "issue_row"."area_id"
          AND "membership"."autoreject" = TRUE
          AND "interest"."autoreject" ISNULL
          AND "direct_voter"."member_id" ISNULL
          AND "delegating_voter"."member_id" ISNULL
      LOOP
        INSERT INTO "direct_voter"
          ("member_id", "issue_id", "weight", "autoreject") VALUES
          ("member_id_v", "issue_id_p", 1, TRUE);
        INSERT INTO "vote" (
          "member_id",
          "issue_id",
          "initiative_id",
          "grade"
          ) SELECT
            "member_id_v" AS "member_id",
            "issue_id_p"  AS "issue_id",
            "id"          AS "initiative_id",
            -1            AS "grade"
          FROM "initiative" WHERE "issue_id" = "issue_id_p";
      END LOOP;
      PERFORM "add_vote_delegations"("issue_id_p");
      UPDATE "issue" SET
        "closed" = now(),
        "voter_count" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_voter" WHERE "issue_id" = "issue_id_p"
        )
        WHERE "id" = "issue_id_p";
      UPDATE "initiative" SET
        "positive_votes" = "vote_counts"."positive_votes",
        "negative_votes" = "vote_counts"."negative_votes",
        "agreed" = CASE WHEN "majority_strict" THEN
          "vote_counts"."positive_votes" * "majority_den" >
          "majority_num" *
          ("vote_counts"."positive_votes"+"vote_counts"."negative_votes")
        ELSE
          "vote_counts"."positive_votes" * "majority_den" >=
          "majority_num" *
          ("vote_counts"."positive_votes"+"vote_counts"."negative_votes")
        END
        FROM
          ( SELECT
              "initiative"."id" AS "initiative_id",
              coalesce(
                sum(
                  CASE WHEN "grade" > 0 THEN "direct_voter"."weight" ELSE 0 END
                ),
                0
              ) AS "positive_votes",
              coalesce(
                sum(
                  CASE WHEN "grade" < 0 THEN "direct_voter"."weight" ELSE 0 END
                ),
                0
              ) AS "negative_votes"
            FROM "initiative"
            JOIN "issue" ON "initiative"."issue_id" = "issue"."id"
            JOIN "policy" ON "issue"."policy_id" = "policy"."id"
            LEFT JOIN "direct_voter"
              ON "direct_voter"."issue_id" = "initiative"."issue_id"
            LEFT JOIN "vote"
              ON "vote"."initiative_id" = "initiative"."id"
              AND "vote"."member_id" = "direct_voter"."member_id"
            WHERE "initiative"."issue_id" = "issue_id_p"
            AND "initiative"."admitted"  -- NOTE: NULL case is handled too
            GROUP BY "initiative"."id"
          ) AS "vote_counts",
          "issue",
          "policy"
        WHERE "vote_counts"."initiative_id" = "initiative"."id"
        AND "issue"."id" = "initiative"."issue_id"
        AND "policy"."id" = "issue"."policy_id";
      -- NOTE: "closed" column of issue must be set at this point
      DELETE FROM "battle" WHERE "issue_id" = "issue_id_p";
      INSERT INTO "battle" (
        "issue_id",
        "winning_initiative_id", "losing_initiative_id",
        "count"
      ) SELECT
        "issue_id",
        "winning_initiative_id", "losing_initiative_id",
        "count"
        FROM "battle_view" WHERE "issue_id" = "issue_id_p";
    END;
  $$;

COMMIT;
