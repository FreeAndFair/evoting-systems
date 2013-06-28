BEGIN;


CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.2.5', 1, 2, 5))
   AS "subquery"("string", "major", "minor", "revision");


CREATE FUNCTION "share_row_lock_issue_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF TG_OP = 'UPDATE' OR TG_OP = 'DELETE' THEN
        PERFORM NULL FROM "issue" WHERE "id" = OLD."issue_id" FOR SHARE;
      END IF;
      IF TG_OP = 'INSERT' OR TG_OP = 'UPDATE' THEN
        PERFORM NULL FROM "issue" WHERE "id" = NEW."issue_id" FOR SHARE;
        RETURN NEW;
      ELSE
        RETURN OLD;
      END IF;
    END;
  $$;

COMMENT ON FUNCTION "share_row_lock_issue_trigger"() IS 'Implementation of triggers "share_row_lock_issue" on multiple tables';


CREATE FUNCTION "share_row_lock_issue_via_initiative_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF TG_OP = 'UPDATE' OR TG_OP = 'DELETE' THEN
        PERFORM NULL FROM "issue"
          JOIN "initiative" ON "issue"."id" = "initiative"."issue_id"
          WHERE "initiative"."id" = OLD."initiative_id"
          FOR SHARE OF "issue";
      END IF;
      IF TG_OP = 'INSERT' OR TG_OP = 'UPDATE' THEN
        PERFORM NULL FROM "issue"
          JOIN "initiative" ON "issue"."id" = "initiative"."issue_id"
          WHERE "initiative"."id" = NEW."initiative_id"
          FOR SHARE OF "issue";
        RETURN NEW;
      ELSE
        RETURN OLD;
      END IF;
    END;
  $$;

COMMENT ON FUNCTION "share_row_lock_issue_trigger"() IS 'Implementation of trigger "share_row_lock_issue_via_initiative" on table "opinion"';


CREATE TRIGGER "share_row_lock_issue"
  BEFORE INSERT OR UPDATE OR DELETE ON "initiative"
  FOR EACH ROW EXECUTE PROCEDURE
  "share_row_lock_issue_trigger"();

CREATE TRIGGER "share_row_lock_issue"
  BEFORE INSERT OR UPDATE OR DELETE ON "interest"
  FOR EACH ROW EXECUTE PROCEDURE
  "share_row_lock_issue_trigger"();

CREATE TRIGGER "share_row_lock_issue"
  BEFORE INSERT OR UPDATE OR DELETE ON "supporter"
  FOR EACH ROW EXECUTE PROCEDURE
  "share_row_lock_issue_trigger"();

CREATE TRIGGER "share_row_lock_issue_via_initiative"
  BEFORE INSERT OR UPDATE OR DELETE ON "opinion"
  FOR EACH ROW EXECUTE PROCEDURE
  "share_row_lock_issue_via_initiative_trigger"();

CREATE TRIGGER "share_row_lock_issue"
  BEFORE INSERT OR UPDATE OR DELETE ON "direct_voter"
  FOR EACH ROW EXECUTE PROCEDURE
  "share_row_lock_issue_trigger"();

CREATE TRIGGER "share_row_lock_issue"
  BEFORE INSERT OR UPDATE OR DELETE ON "delegating_voter"
  FOR EACH ROW EXECUTE PROCEDURE
  "share_row_lock_issue_trigger"();

CREATE TRIGGER "share_row_lock_issue"
  BEFORE INSERT OR UPDATE OR DELETE ON "vote"
  FOR EACH ROW EXECUTE PROCEDURE
  "share_row_lock_issue_trigger"();

COMMENT ON TRIGGER "share_row_lock_issue"                ON "initiative"       IS 'See "lock_issue" function';
COMMENT ON TRIGGER "share_row_lock_issue"                ON "interest"         IS 'See "lock_issue" function';
COMMENT ON TRIGGER "share_row_lock_issue"                ON "supporter"        IS 'See "lock_issue" function';
COMMENT ON TRIGGER "share_row_lock_issue_via_initiative" ON "opinion"          IS 'See "lock_issue" function';
COMMENT ON TRIGGER "share_row_lock_issue"                ON "direct_voter"     IS 'See "lock_issue" function';
COMMENT ON TRIGGER "share_row_lock_issue"                ON "delegating_voter" IS 'See "lock_issue" function';
COMMENT ON TRIGGER "share_row_lock_issue"                ON "vote"             IS 'See "lock_issue" function';


CREATE FUNCTION "lock_issue"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      LOCK TABLE "member"     IN SHARE MODE;
      LOCK TABLE "membership" IN SHARE MODE;
      LOCK TABLE "policy"     IN SHARE MODE;
      PERFORM NULL FROM "issue" WHERE "id" = "issue_id_p" FOR UPDATE;
      -- NOTE: The row-level exclusive lock in combination with the
      -- share_row_lock_issue(_via_initiative)_trigger functions (which
      -- acquire a row-level share lock on the issue) ensure that no data
      -- is changed, which could affect calculation of snapshots or
      -- counting of votes. Table "delegation" must be table-level-locked,
      -- as it also contains issue- and global-scope delegations.
      LOCK TABLE "delegation" IN SHARE MODE;
      LOCK TABLE "direct_population_snapshot"     IN EXCLUSIVE MODE;
      LOCK TABLE "delegating_population_snapshot" IN EXCLUSIVE MODE;
      LOCK TABLE "direct_interest_snapshot"       IN EXCLUSIVE MODE;
      LOCK TABLE "delegating_interest_snapshot"   IN EXCLUSIVE MODE;
      LOCK TABLE "direct_supporter_snapshot"      IN EXCLUSIVE MODE;
      RETURN;
    END;
  $$;

COMMENT ON FUNCTION "lock_issue"
  ( "issue"."id"%TYPE )
  IS 'Locks the issue and all other data which is used for calculating snapshots or counting votes.';


CREATE OR REPLACE FUNCTION "calculate_member_counts"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      LOCK TABLE "member"       IN SHARE MODE;
      LOCK TABLE "member_count" IN EXCLUSIVE MODE;
      LOCK TABLE "area"         IN EXCLUSIVE MODE;
      LOCK TABLE "membership"   IN SHARE MODE;
      DELETE FROM "member_count";
      INSERT INTO "member_count" ("total_count")
        SELECT "total_count" FROM "member_count_view";
      UPDATE "area" SET
        "direct_member_count" = "view"."direct_member_count",
        "member_weight"       = "view"."member_weight",
        "autoreject_weight"   = "view"."autoreject_weight"
        FROM "area_member_count" AS "view"
        WHERE "view"."area_id" = "area"."id";
      RETURN;
    END;
  $$;

CREATE OR REPLACE FUNCTION "create_snapshot"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "initiative_id_v"    "initiative"."id"%TYPE;
      "suggestion_id_v"    "suggestion"."id"%TYPE;
    BEGIN
      PERFORM "lock_issue"("issue_id_p");
      PERFORM "create_population_snapshot"("issue_id_p");
      PERFORM "create_interest_snapshot"("issue_id_p");
      UPDATE "issue" SET
        "snapshot" = now(),
        "latest_snapshot_event" = 'periodic',
        "population" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_population_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
        ),
        "vote_now" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_interest_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "voting_requested" = TRUE
        ),
        "vote_later" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_interest_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "voting_requested" = FALSE
        )
        WHERE "id" = "issue_id_p";
      FOR "initiative_id_v" IN
        SELECT "id" FROM "initiative" WHERE "issue_id" = "issue_id_p"
      LOOP
        UPDATE "initiative" SET
          "supporter_count" = (
            SELECT coalesce(sum("di"."weight"), 0)
            FROM "direct_interest_snapshot" AS "di"
            JOIN "direct_supporter_snapshot" AS "ds"
            ON "di"."member_id" = "ds"."member_id"
            WHERE "di"."issue_id" = "issue_id_p"
            AND "di"."event" = 'periodic'
            AND "ds"."initiative_id" = "initiative_id_v"
            AND "ds"."event" = 'periodic'
          ),
          "informed_supporter_count" = (
            SELECT coalesce(sum("di"."weight"), 0)
            FROM "direct_interest_snapshot" AS "di"
            JOIN "direct_supporter_snapshot" AS "ds"
            ON "di"."member_id" = "ds"."member_id"
            WHERE "di"."issue_id" = "issue_id_p"
            AND "di"."event" = 'periodic'
            AND "ds"."initiative_id" = "initiative_id_v"
            AND "ds"."event" = 'periodic'
            AND "ds"."informed"
          ),
          "satisfied_supporter_count" = (
            SELECT coalesce(sum("di"."weight"), 0)
            FROM "direct_interest_snapshot" AS "di"
            JOIN "direct_supporter_snapshot" AS "ds"
            ON "di"."member_id" = "ds"."member_id"
            WHERE "di"."issue_id" = "issue_id_p"
            AND "di"."event" = 'periodic'
            AND "ds"."initiative_id" = "initiative_id_v"
            AND "ds"."event" = 'periodic'
            AND "ds"."satisfied"
          ),
          "satisfied_informed_supporter_count" = (
            SELECT coalesce(sum("di"."weight"), 0)
            FROM "direct_interest_snapshot" AS "di"
            JOIN "direct_supporter_snapshot" AS "ds"
            ON "di"."member_id" = "ds"."member_id"
            WHERE "di"."issue_id" = "issue_id_p"
            AND "di"."event" = 'periodic'
            AND "ds"."initiative_id" = "initiative_id_v"
            AND "ds"."event" = 'periodic'
            AND "ds"."informed"
            AND "ds"."satisfied"
          )
          WHERE "id" = "initiative_id_v";
        FOR "suggestion_id_v" IN
          SELECT "id" FROM "suggestion"
          WHERE "initiative_id" = "initiative_id_v"
        LOOP
          UPDATE "suggestion" SET
            "minus2_unfulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = -2
              AND "opinion"."fulfilled" = FALSE
            ),
            "minus2_fulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = -2
              AND "opinion"."fulfilled" = TRUE
            ),
            "minus1_unfulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = -1
              AND "opinion"."fulfilled" = FALSE
            ),
            "minus1_fulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = -1
              AND "opinion"."fulfilled" = TRUE
            ),
            "plus1_unfulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = 1
              AND "opinion"."fulfilled" = FALSE
            ),
            "plus1_fulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = 1
              AND "opinion"."fulfilled" = TRUE
            ),
            "plus2_unfulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = 2
              AND "opinion"."fulfilled" = FALSE
            ),
            "plus2_fulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = 2
              AND "opinion"."fulfilled" = TRUE
            )
            WHERE "suggestion"."id" = "suggestion_id_v";
        END LOOP;
      END LOOP;
      RETURN;
    END;
  $$;

CREATE OR REPLACE FUNCTION "close_voting"("issue_id_p" "issue"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row"   "issue"%ROWTYPE;
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "lock_issue"("issue_id_p");
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

CREATE OR REPLACE FUNCTION "check_issue"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row"         "issue"%ROWTYPE;
      "policy_row"        "policy"%ROWTYPE;
      "voting_requested_v" BOOLEAN;
    BEGIN
      PERFORM "lock_issue"("issue_id_p");
      SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
      -- only process open issues:
      IF "issue_row"."closed" ISNULL THEN
        SELECT * INTO "policy_row" FROM "policy"
          WHERE "id" = "issue_row"."policy_id";
        -- create a snapshot, unless issue is already fully frozen:
        IF "issue_row"."fully_frozen" ISNULL THEN
          PERFORM "create_snapshot"("issue_id_p");
          SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
        END IF;
        -- eventually close or accept issues, which have not been accepted:
        IF "issue_row"."accepted" ISNULL THEN
          IF EXISTS (
            SELECT NULL FROM "initiative"
            WHERE "issue_id" = "issue_id_p"
            AND "supporter_count" > 0
            AND "supporter_count" * "policy_row"."issue_quorum_den"
            >= "issue_row"."population" * "policy_row"."issue_quorum_num"
          ) THEN
            -- accept issues, if supporter count is high enough
            PERFORM "set_snapshot_event"("issue_id_p", 'end_of_admission');
            "issue_row"."accepted" = now();  -- NOTE: "issue_row" used later
            UPDATE "issue" SET "accepted" = "issue_row"."accepted"
              WHERE "id" = "issue_row"."id";
          ELSIF
            now() >= "issue_row"."created" + "issue_row"."admission_time"
          THEN
            -- close issues, if admission time has expired
            PERFORM "set_snapshot_event"("issue_id_p", 'end_of_admission');
            UPDATE "issue" SET "closed" = now()
              WHERE "id" = "issue_row"."id";
          END IF;
        END IF;
        -- eventually half freeze issues:
        IF
          -- NOTE: issue can't be closed at this point, if it has been accepted
          "issue_row"."accepted" NOTNULL AND
          "issue_row"."half_frozen" ISNULL
        THEN
          SELECT
            CASE
              WHEN "vote_now" * 2 > "issue_row"."population" THEN
                TRUE
              WHEN "vote_later" * 2 > "issue_row"."population" THEN
                FALSE
              ELSE NULL
            END
            INTO "voting_requested_v"
            FROM "issue" WHERE "id" = "issue_id_p";
          IF
            "voting_requested_v" OR (
              "voting_requested_v" ISNULL AND
              now() >= "issue_row"."accepted" + "issue_row"."discussion_time"
            )
          THEN
            PERFORM "set_snapshot_event"("issue_id_p", 'half_freeze');
            "issue_row"."half_frozen" = now();  -- NOTE: "issue_row" used later
            UPDATE "issue" SET "half_frozen" = "issue_row"."half_frozen"
              WHERE "id" = "issue_row"."id";
          END IF;
        END IF;
        -- close issues after some time, if all initiatives have been revoked:
        IF
          "issue_row"."closed" ISNULL AND
          NOT EXISTS (
            -- all initiatives are revoked
            SELECT NULL FROM "initiative"
            WHERE "issue_id" = "issue_id_p" AND "revoked" ISNULL
          ) AND (
            NOT EXISTS (
              -- and no initiatives have been revoked lately
              SELECT NULL FROM "initiative"
              WHERE "issue_id" = "issue_id_p"
              AND now() < "revoked" + "issue_row"."verification_time"
            ) OR (
              -- or verification time has elapsed
              "issue_row"."half_frozen" NOTNULL AND
              "issue_row"."fully_frozen" ISNULL AND
              now() >= "issue_row"."half_frozen" + "issue_row"."verification_time"
            )
          )
        THEN
          "issue_row"."closed" = now();  -- NOTE: "issue_row" used later
          UPDATE "issue" SET "closed" = "issue_row"."closed"
            WHERE "id" = "issue_row"."id";
        END IF;
        -- fully freeze issue after verification time:
        IF
          "issue_row"."half_frozen" NOTNULL AND
          "issue_row"."fully_frozen" ISNULL AND
          "issue_row"."closed" ISNULL AND
          now() >= "issue_row"."half_frozen" + "issue_row"."verification_time"
        THEN
          PERFORM "freeze_after_snapshot"("issue_id_p");
          -- NOTE: "issue" might change, thus "issue_row" has to be updated below
        END IF;
        SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
        -- close issue by calling close_voting(...) after voting time:
        IF
          "issue_row"."closed" ISNULL AND
          "issue_row"."fully_frozen" NOTNULL AND
          now() >= "issue_row"."fully_frozen" + "issue_row"."voting_time"
        THEN
          PERFORM "close_voting"("issue_id_p");
        END IF;
      END IF;
      RETURN;
    END;
  $$;


DROP FUNCTION "global_lock"();


COMMIT;
