BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.4.0_rc4', 1, 4, -1))
  AS "subquery"("string", "major", "minor", "revision");

CREATE OR REPLACE FUNCTION "close_voting"("issue_id_p" "issue"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "area_id_v"   "area"."id"%TYPE;
      "unit_id_v"   "unit"."id"%TYPE;
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "lock_issue"("issue_id_p");
      SELECT "area_id" INTO "area_id_v" FROM "issue" WHERE "id" = "issue_id_p";
      SELECT "unit_id" INTO "unit_id_v" FROM "area"  WHERE "id" = "area_id_v";
      DELETE FROM "delegating_voter"
        WHERE "issue_id" = "issue_id_p";
      DELETE FROM "direct_voter"
        WHERE "issue_id" = "issue_id_p"
        AND "autoreject" = TRUE;
      DELETE FROM "direct_voter"
        USING (
          SELECT
            "direct_voter"."member_id"
          FROM "direct_voter"
          JOIN "member" ON "direct_voter"."member_id" = "member"."id"
          LEFT JOIN "privilege"
          ON "privilege"."unit_id" = "unit_id_v"
          AND "privilege"."member_id" = "direct_voter"."member_id"
          WHERE "direct_voter"."issue_id" = "issue_id_p" AND (
            "member"."active" = FALSE OR
            "privilege"."voting_right" ISNULL OR
            "privilege"."voting_right" = FALSE
          )
        ) AS "subquery"
        WHERE "direct_voter"."issue_id" = "issue_id_p"
        AND "direct_voter"."member_id" = "subquery"."member_id";
      UPDATE "direct_voter" SET "weight" = 1
        WHERE "issue_id" = "issue_id_p";
      PERFORM "add_vote_delegations"("issue_id_p");
      FOR "member_id_v" IN
        SELECT "interest"."member_id"
          FROM "interest"
          JOIN "member"
            ON "interest"."member_id" = "member"."id"
          JOIN "privilege"
            ON "privilege"."unit_id" = "unit_id_v"
            AND "privilege"."member_id" = "member"."id"
          LEFT JOIN "direct_voter"
            ON "interest"."member_id" = "direct_voter"."member_id"
            AND "interest"."issue_id" = "direct_voter"."issue_id"
          LEFT JOIN "delegating_voter"
            ON "interest"."member_id" = "delegating_voter"."member_id"
            AND "interest"."issue_id" = "delegating_voter"."issue_id"
          WHERE "interest"."issue_id" = "issue_id_p"
          AND "interest"."autoreject" = TRUE
          AND "member"."active"
          AND "privilege"."voting_right"
          AND "direct_voter"."member_id" ISNULL
          AND "delegating_voter"."member_id" ISNULL
        UNION SELECT "membership"."member_id"
          FROM "membership"
          JOIN "member"
            ON "membership"."member_id" = "member"."id"
          JOIN "privilege"
            ON "privilege"."unit_id" = "unit_id_v"
            AND "privilege"."member_id" = "member"."id"
          LEFT JOIN "interest"
            ON "membership"."member_id" = "interest"."member_id"
            AND "interest"."issue_id" = "issue_id_p"
          LEFT JOIN "direct_voter"
            ON "membership"."member_id" = "direct_voter"."member_id"
            AND "direct_voter"."issue_id" = "issue_id_p"
          LEFT JOIN "delegating_voter"
            ON "membership"."member_id" = "delegating_voter"."member_id"
            AND "delegating_voter"."issue_id" = "issue_id_p"
          WHERE "membership"."area_id" = "area_id_v"
          AND "membership"."autoreject" = TRUE
          AND "member"."active"
          AND "privilege"."voting_right"
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
          FROM "initiative"
          WHERE "issue_id" = "issue_id_p" AND "admitted";
      END LOOP;
      PERFORM "add_vote_delegations"("issue_id_p");
      UPDATE "issue" SET
        "state"  = 'calculation',
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

CREATE OR REPLACE FUNCTION "clean_issue"("issue_id_p" "issue"."id"%TYPE)
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
          "state"           = 'voting',
          "closed"          = NULL,
          "ranks_available" = FALSE
          WHERE "id" = "issue_id_p";
        DELETE FROM "issue_comment"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "voting_comment"
          WHERE "issue_id" = "issue_id_p";
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
        DELETE FROM "non_voter"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "delegation"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "supporter"
          WHERE "issue_id" = "issue_id_p";
        UPDATE "issue" SET
          "state"           = "issue_row"."state",
          "closed"          = "issue_row"."closed",
          "ranks_available" = "issue_row"."ranks_available",
          "cleaned"         = now()
          WHERE "id" = "issue_id_p";
      END IF;
      RETURN;
    END;
  $$;

COMMIT;
