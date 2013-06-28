BEGIN;

SET TRANSACTION ISOLATION LEVEL REPEATABLE READ;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('2.2.0', 2, 2, 0))
  AS "subquery"("string", "major", "minor", "revision");

DROP VIEW "issue_with_ranks_missing";
DROP VIEW "open_issue"; -- recreated later
DROP VIEW "event_seen_by_member";  -- recreated later
DROP VIEW "selected_event_seen_by_member";  -- recreated later
ALTER TABLE "issue" DROP CONSTRAINT "valid_state";
ALTER TABLE "issue" DROP COLUMN "ranks_available";
ALTER TABLE "event" DROP CONSTRAINT "event_state_check";
ALTER TABLE "event" DROP CONSTRAINT "null_constraints_for_issue_state_changed";  -- recreated later
ALTER TABLE "event" DROP CONSTRAINT "null_constraints_for_initiative_creation_or_revocation_or_new_draft";  -- recreated later
ALTER TABLE "event" DROP CONSTRAINT "null_constraints_for_suggestion_creation";  -- recreated later
ALTER TYPE "issue_state" RENAME TO "issue_state_old";
CREATE TYPE "issue_state" AS ENUM (
        'admission', 'discussion', 'verification', 'voting',
        'canceled_revoked_before_accepted',
        'canceled_issue_not_accepted',
        'canceled_after_revocation_during_discussion',
        'canceled_after_revocation_during_verification',
        'canceled_no_initiative_admitted',
        'finished_without_winner', 'finished_with_winner');
ALTER TABLE "issue" ALTER COLUMN "state" DROP DEFAULT;
ALTER TABLE "issue" ALTER COLUMN "state" TYPE "issue_state" USING "state"::text::"issue_state";
ALTER TABLE "event" ALTER COLUMN "state" TYPE "issue_state" USING "state"::text::"issue_state";
DROP TYPE "issue_state_old";
ALTER TABLE "issue" ALTER COLUMN "state" SET DEFAULT 'admission';
ALTER TABLE "issue" ADD CONSTRAINT "valid_state"
        CHECK ((
          ("accepted" ISNULL  AND "half_frozen" ISNULL  AND "fully_frozen" ISNULL ) OR
          ("accepted" NOTNULL AND "half_frozen" ISNULL  AND "fully_frozen" ISNULL ) OR
          ("accepted" NOTNULL AND "half_frozen" NOTNULL AND "fully_frozen" ISNULL ) OR
          ("accepted" NOTNULL AND "half_frozen" NOTNULL AND "fully_frozen" NOTNULL)
        ) AND (
          ("state" = 'admission'    AND "closed" ISNULL AND "accepted" ISNULL) OR
          ("state" = 'discussion'   AND "closed" ISNULL AND "accepted" NOTNULL AND "half_frozen" ISNULL) OR
          ("state" = 'verification' AND "closed" ISNULL AND "half_frozen" NOTNULL AND "fully_frozen" ISNULL) OR
          ("state" = 'voting'       AND "closed" ISNULL AND "fully_frozen" NOTNULL) OR
          ("state" = 'canceled_revoked_before_accepted'              AND "closed" NOTNULL AND "accepted" ISNULL) OR
          ("state" = 'canceled_issue_not_accepted'                   AND "closed" NOTNULL AND "accepted" ISNULL) OR
          ("state" = 'canceled_after_revocation_during_discussion'   AND "closed" NOTNULL AND "half_frozen"  ISNULL) OR
          ("state" = 'canceled_after_revocation_during_verification' AND "closed" NOTNULL AND "fully_frozen" ISNULL) OR
          ("state" = 'canceled_no_initiative_admitted' AND "closed" NOTNULL AND "fully_frozen" NOTNULL AND "closed" = "fully_frozen") OR
          ("state" = 'finished_without_winner'         AND "closed" NOTNULL AND "fully_frozen" NOTNULL AND "closed" != "fully_frozen") OR
          ("state" = 'finished_with_winner'            AND "closed" NOTNULL AND "fully_frozen" NOTNULL AND "closed" != "fully_frozen")
        ));
ALTER TABLE "issue" ADD COLUMN "phase_finished" TIMESTAMPTZ;
COMMENT ON COLUMN "issue"."phase_finished" IS 'Set to a value NOTNULL, if the current phase has finished, but calculations are pending; No changes in this issue shall be made by the frontend or API when this value is set';
ALTER TABLE "issue" ADD CONSTRAINT "phase_finished_only_when_not_closed"
          CHECK ("phase_finished" ISNULL OR "closed" ISNULL);
ALTER TABLE "event" ADD CONSTRAINT "null_constraints_for_issue_state_changed" CHECK (
          "event" != 'issue_state_changed' OR (
            "member_id"     ISNULL  AND
            "issue_id"      NOTNULL AND
            "state"         NOTNULL AND
            "initiative_id" ISNULL  AND
            "draft_id"      ISNULL  AND
            "suggestion_id" ISNULL  ));
ALTER TABLE "event" ADD CONSTRAINT "null_constraints_for_initiative_creation_or_revocation_or_new_draft" CHECK (
          "event" NOT IN (
            'initiative_created_in_new_issue',
            'initiative_created_in_existing_issue',
            'initiative_revoked',
            'new_draft_created'
          ) OR (
            "member_id"     NOTNULL AND
            "issue_id"      NOTNULL AND
            "state"         NOTNULL AND
            "initiative_id" NOTNULL AND
            "draft_id"      NOTNULL AND
            "suggestion_id" ISNULL  ));
ALTER TABLE "event" ADD CONSTRAINT "null_constraints_for_suggestion_creation" CHECK (
          "event" != 'suggestion_created' OR (
            "member_id"     NOTNULL AND
            "issue_id"      NOTNULL AND
            "state"         NOTNULL AND
            "initiative_id" NOTNULL AND
            "draft_id"      ISNULL  AND
            "suggestion_id" NOTNULL ));
CREATE VIEW "open_issue" AS
  SELECT * FROM "issue" WHERE "closed" ISNULL;
COMMENT ON VIEW "open_issue" IS 'All open issues';
CREATE VIEW "event_seen_by_member" AS
  SELECT
    "member"."id" AS "seen_by_member_id",
    CASE WHEN "event"."state" IN (
      'voting',
      'finished_without_winner',
      'finished_with_winner'
    ) THEN
      'voting'::"notify_level"
    ELSE
      CASE WHEN "event"."state" IN (
        'verification',
        'canceled_after_revocation_during_verification',
        'canceled_no_initiative_admitted'
      ) THEN
        'verification'::"notify_level"
      ELSE
        CASE WHEN "event"."state" IN (
          'discussion',
          'canceled_after_revocation_during_discussion'
        ) THEN
          'discussion'::"notify_level"
        ELSE
          'all'::"notify_level"
        END
      END
    END AS "notify_level",
    "event".*
  FROM "member" CROSS JOIN "event"
  LEFT JOIN "issue"
    ON "event"."issue_id" = "issue"."id"
  LEFT JOIN "membership"
    ON "member"."id" = "membership"."member_id"
    AND "issue"."area_id" = "membership"."area_id"
  LEFT JOIN "interest"
    ON "member"."id" = "interest"."member_id"
    AND "event"."issue_id" = "interest"."issue_id"
  LEFT JOIN "supporter"
    ON "member"."id" = "supporter"."member_id"
    AND "event"."initiative_id" = "supporter"."initiative_id"
  LEFT JOIN "ignored_member"
    ON "member"."id" = "ignored_member"."member_id"
    AND "event"."member_id" = "ignored_member"."other_member_id"
  LEFT JOIN "ignored_initiative"
    ON "member"."id" = "ignored_initiative"."member_id"
    AND "event"."initiative_id" = "ignored_initiative"."initiative_id"
  WHERE (
    "supporter"."member_id" NOTNULL OR
    "interest"."member_id" NOTNULL OR
    ( "membership"."member_id" NOTNULL AND
      "event"."event" IN (
        'issue_state_changed',
        'initiative_created_in_new_issue',
        'initiative_created_in_existing_issue',
        'initiative_revoked' ) ) )
  AND "ignored_member"."member_id" ISNULL
  AND "ignored_initiative"."member_id" ISNULL;
COMMENT ON VIEW "event_seen_by_member" IS 'Events as seen by a member, depending on its memberships, interests and support, but ignoring members "notify_level"';
CREATE VIEW "selected_event_seen_by_member" AS
  SELECT
    "member"."id" AS "seen_by_member_id",
    CASE WHEN "event"."state" IN (
      'voting',
      'finished_without_winner',
      'finished_with_winner'
    ) THEN
      'voting'::"notify_level"
    ELSE
      CASE WHEN "event"."state" IN (
        'verification',
        'canceled_after_revocation_during_verification',
        'canceled_no_initiative_admitted'
      ) THEN
        'verification'::"notify_level"
      ELSE
        CASE WHEN "event"."state" IN (
          'discussion',
          'canceled_after_revocation_during_discussion'
        ) THEN
          'discussion'::"notify_level"
        ELSE
          'all'::"notify_level"
        END
      END
    END AS "notify_level",
    "event".*
  FROM "member" CROSS JOIN "event"
  LEFT JOIN "issue"
    ON "event"."issue_id" = "issue"."id"
  LEFT JOIN "membership"
    ON "member"."id" = "membership"."member_id"
    AND "issue"."area_id" = "membership"."area_id"
  LEFT JOIN "interest"
    ON "member"."id" = "interest"."member_id"
    AND "event"."issue_id" = "interest"."issue_id"
  LEFT JOIN "supporter"
    ON "member"."id" = "supporter"."member_id"
    AND "event"."initiative_id" = "supporter"."initiative_id"
  LEFT JOIN "ignored_member"
    ON "member"."id" = "ignored_member"."member_id"
    AND "event"."member_id" = "ignored_member"."other_member_id"
  LEFT JOIN "ignored_initiative"
    ON "member"."id" = "ignored_initiative"."member_id"
    AND "event"."initiative_id" = "ignored_initiative"."initiative_id"
  WHERE (
    ( "member"."notify_level" >= 'all' ) OR
    ( "member"."notify_level" >= 'voting' AND
      "event"."state" IN (
        'voting',
        'finished_without_winner',
        'finished_with_winner' ) ) OR
    ( "member"."notify_level" >= 'verification' AND
      "event"."state" IN (
        'verification',
        'canceled_after_revocation_during_verification',
        'canceled_no_initiative_admitted' ) ) OR
    ( "member"."notify_level" >= 'discussion' AND
      "event"."state" IN (
        'discussion',
        'canceled_after_revocation_during_discussion' ) ) )
  AND (
    "supporter"."member_id" NOTNULL OR
    "interest"."member_id" NOTNULL OR
    ( "membership"."member_id" NOTNULL AND
      "event"."event" IN (
        'issue_state_changed',
        'initiative_created_in_new_issue',
        'initiative_created_in_existing_issue',
        'initiative_revoked' ) ) )
  AND "ignored_member"."member_id" ISNULL
  AND "ignored_initiative"."member_id" ISNULL;
COMMENT ON VIEW "selected_event_seen_by_member" IS 'Events as seen by a member, depending on its memberships, interests, support and members "notify_level"';

ALTER TABLE "initiative" ADD COLUMN "harmonic_weight" NUMERIC(12, 3);
COMMENT ON COLUMN "initiative"."harmonic_weight" IS 'Indicates the relevancy of the initiative, calculated from the potential supporters weighted with the harmonic series to avoid a large number of clones affecting other initiative''s sorting positions too much; shall be used as secondary sorting key after "admitted" as primary sorting key';

CREATE OR REPLACE FUNCTION "write_event_issue_state_changed_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF NEW."state" != OLD."state" THEN
        INSERT INTO "event" ("event", "issue_id", "state")
          VALUES ('issue_state_changed', NEW."id", NEW."state");
      END IF;
      RETURN NULL;
    END;
  $$;

CREATE OR REPLACE FUNCTION "forbid_changes_on_closed_issue_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_id_v" "issue"."id"%TYPE;
      "issue_row"  "issue"%ROWTYPE;
    BEGIN
      IF TG_OP = 'DELETE' THEN
        "issue_id_v" := OLD."issue_id";
      ELSE
        "issue_id_v" := NEW."issue_id";
      END IF;
      SELECT INTO "issue_row" * FROM "issue"
        WHERE "id" = "issue_id_v" FOR SHARE;
      IF "issue_row"."closed" NOTNULL THEN
        IF
          TG_RELID = 'direct_voter'::regclass AND
          TG_OP = 'UPDATE'
        THEN
          IF
            OLD."issue_id"  = NEW."issue_id"  AND
            OLD."member_id" = NEW."member_id" AND
            OLD."weight" = NEW."weight"
          THEN
            RETURN NULL;  -- allows changing of voter comment
          END IF;
        END IF;
        RAISE EXCEPTION 'Tried to modify data belonging to a closed issue.';
      ELSIF
        "issue_row"."state" = 'voting' AND
        "issue_row"."phase_finished" NOTNULL
      THEN
        IF TG_RELID = 'vote'::regclass THEN
          RAISE EXCEPTION 'Tried to modify data after voting has been closed.';
        END IF;
      END IF;
      RETURN NULL;
    END;
  $$;

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
  JOIN "battle_participant" AS "winning_initiative"
    ON "issue"."id" = "winning_initiative"."issue_id"
  JOIN "battle_participant" AS "losing_initiative"
    ON "issue"."id" = "losing_initiative"."issue_id"
  LEFT JOIN "vote" AS "better_vote"
    ON "direct_voter"."member_id" = "better_vote"."member_id"
    AND "winning_initiative"."id" = "better_vote"."initiative_id"
  LEFT JOIN "vote" AS "worse_vote"
    ON "direct_voter"."member_id" = "worse_vote"."member_id"
    AND "losing_initiative"."id" = "worse_vote"."initiative_id"
  WHERE "issue"."state" = 'voting'
  AND "issue"."phase_finished" NOTNULL
  AND (
    "winning_initiative"."id" != "losing_initiative"."id" OR
    ( ("winning_initiative"."id" NOTNULL AND "losing_initiative"."id" ISNULL) OR
      ("winning_initiative"."id" ISNULL AND "losing_initiative"."id" NOTNULL) ) )
  GROUP BY
    "issue"."id",
    "winning_initiative"."id",
    "losing_initiative"."id";

DROP VIEW "timeline";
DROP VIEW "timeline_issue";
DROP VIEW "timeline_initiative";
DROP VIEW "timeline_draft";
DROP VIEW "timeline_suggestion";
DROP TYPE "timeline_event";

DROP TRIGGER "share_row_lock_issue" ON "initiative";
DROP TRIGGER "share_row_lock_issue" ON "interest";
DROP TRIGGER "share_row_lock_issue" ON "supporter";
DROP TRIGGER "share_row_lock_issue_via_initiative" ON "opinion";
DROP TRIGGER "share_row_lock_issue" ON "direct_voter";
DROP TRIGGER "share_row_lock_issue" ON "delegating_voter";
DROP TRIGGER "share_row_lock_issue" ON "vote";
DROP FUNCTION "share_row_lock_issue_trigger"();

CREATE FUNCTION "require_transaction_isolation"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF
        current_setting('transaction_isolation') NOT IN
        ('repeatable read', 'serializable')
      THEN
        RAISE EXCEPTION 'Insufficient transaction isolation level';
      END IF;
      RETURN;
    END;
  $$;
COMMENT ON FUNCTION "require_transaction_isolation"() IS 'Throws an exception, if transaction isolation level is too low to provide a consistent snapshot';

CREATE FUNCTION "dont_require_transaction_isolation"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF
        current_setting('transaction_isolation') IN
        ('repeatable read', 'serializable')
      THEN
        RAISE WARNING 'Unneccessary transaction isolation level: %',
          current_setting('transaction_isolation');
      END IF;
      RETURN;
    END;
  $$;
COMMENT ON FUNCTION "dont_require_transaction_isolation"() IS 'Raises a warning, if transaction isolation level is higher than READ COMMITTED';

CREATE OR REPLACE FUNCTION "check_activity"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "system_setting_row" "system_setting"%ROWTYPE;
    BEGIN
      PERFORM "dont_require_transaction_isolation"();
      SELECT * INTO "system_setting_row" FROM "system_setting";
      IF "system_setting_row"."member_ttl" NOTNULL THEN
        UPDATE "member" SET "active" = FALSE
          WHERE "active" = TRUE
          AND "last_activity" < (now() - "system_setting_row"."member_ttl")::DATE;
      END IF;
      RETURN;
    END;
  $$;

CREATE OR REPLACE FUNCTION "calculate_member_counts"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      PERFORM "require_transaction_isolation"();
      DELETE FROM "member_count";
      INSERT INTO "member_count" ("total_count")
        SELECT "total_count" FROM "member_count_view";
      UPDATE "unit" SET "member_count" = "view"."member_count"
        FROM "unit_member_count" AS "view"
        WHERE "view"."unit_id" = "unit"."id";
      UPDATE "area" SET
        "direct_member_count" = "view"."direct_member_count",
        "member_weight"       = "view"."member_weight"
        FROM "area_member_count" AS "view"
        WHERE "view"."area_id" = "area"."id";
      RETURN;
    END;
  $$;

CREATE VIEW "remaining_harmonic_supporter_weight" AS
  SELECT
    "direct_interest_snapshot"."issue_id",
    "direct_interest_snapshot"."event",
    "direct_interest_snapshot"."member_id",
    "direct_interest_snapshot"."weight" AS "weight_num",
    count("initiative"."id") AS "weight_den"
  FROM "issue"
  JOIN "direct_interest_snapshot"
    ON "issue"."id" = "direct_interest_snapshot"."issue_id"
    AND "issue"."latest_snapshot_event" = "direct_interest_snapshot"."event"
  JOIN "initiative"
    ON "issue"."id" = "initiative"."issue_id"
    AND "initiative"."harmonic_weight" ISNULL
  JOIN "direct_supporter_snapshot"
    ON "initiative"."id" = "direct_supporter_snapshot"."initiative_id"
    AND "direct_interest_snapshot"."event" = "direct_supporter_snapshot"."event"
    AND "direct_interest_snapshot"."member_id" = "direct_supporter_snapshot"."member_id"
    AND (
      "direct_supporter_snapshot"."satisfied" = TRUE OR
      coalesce("initiative"."admitted", FALSE) = FALSE
    )
  GROUP BY
    "direct_interest_snapshot"."issue_id",
    "direct_interest_snapshot"."event",
    "direct_interest_snapshot"."member_id",
    "direct_interest_snapshot"."weight";
COMMENT ON VIEW "remaining_harmonic_supporter_weight" IS 'Helper view for function "set_harmonic_initiative_weights"';

CREATE VIEW "remaining_harmonic_initiative_weight_summands" AS
  SELECT
    "initiative"."issue_id",
    "initiative"."id" AS "initiative_id",
    "initiative"."admitted",
    sum("remaining_harmonic_supporter_weight"."weight_num") AS "weight_num",
    "remaining_harmonic_supporter_weight"."weight_den"
  FROM "remaining_harmonic_supporter_weight"
  JOIN "initiative"
    ON "remaining_harmonic_supporter_weight"."issue_id" = "initiative"."issue_id"
    AND "initiative"."harmonic_weight" ISNULL
  JOIN "direct_supporter_snapshot"
    ON "initiative"."id" = "direct_supporter_snapshot"."initiative_id"
    AND "remaining_harmonic_supporter_weight"."event" = "direct_supporter_snapshot"."event"
    AND "remaining_harmonic_supporter_weight"."member_id" = "direct_supporter_snapshot"."member_id"
    AND (
      "direct_supporter_snapshot"."satisfied" = TRUE OR
      coalesce("initiative"."admitted", FALSE) = FALSE
    )
  GROUP BY
    "initiative"."issue_id",
    "initiative"."id",
    "initiative"."admitted",
    "remaining_harmonic_supporter_weight"."weight_den";
COMMENT ON VIEW "remaining_harmonic_initiative_weight_summands" IS 'Helper view for function "set_harmonic_initiative_weights"';

CREATE VIEW "remaining_harmonic_initiative_weight_dummies" AS
  SELECT
    "issue_id",
    "id" AS "initiative_id",
    "admitted",
    0 AS "weight_num",
    1 AS "weight_den"
  FROM "initiative"
  WHERE "harmonic_weight" ISNULL;
COMMENT ON VIEW "remaining_harmonic_initiative_weight_dummies" IS 'Helper view for function "set_harmonic_initiative_weights" providing dummy weights of zero value, which are needed for corner cases where there are no supporters for an initiative at all';

CREATE FUNCTION "set_harmonic_initiative_weights"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "weight_row"   "remaining_harmonic_initiative_weight_summands"%ROWTYPE;
      "i"            INT4;
      "count_v"      INT4;
      "summand_v"    FLOAT;
      "id_ary"       INT4[];
      "weight_ary"   FLOAT[];
      "min_weight_v" FLOAT;
    BEGIN
      PERFORM "require_transaction_isolation"();
      UPDATE "initiative" SET "harmonic_weight" = NULL
        WHERE "issue_id" = "issue_id_p";
      LOOP
        "min_weight_v" := NULL;
        "i" := 0;
        "count_v" := 0;
        FOR "weight_row" IN
          SELECT * FROM "remaining_harmonic_initiative_weight_summands"
          WHERE "issue_id" = "issue_id_p"
          AND (
            coalesce("admitted", FALSE) = FALSE OR NOT EXISTS (
              SELECT NULL FROM "initiative"
              WHERE "issue_id" = "issue_id_p"
              AND "harmonic_weight" ISNULL
              AND coalesce("admitted", FALSE) = FALSE
            )
          )
          UNION ALL  -- needed for corner cases
          SELECT * FROM "remaining_harmonic_initiative_weight_dummies"
          WHERE "issue_id" = "issue_id_p"
          AND (
            coalesce("admitted", FALSE) = FALSE OR NOT EXISTS (
              SELECT NULL FROM "initiative"
              WHERE "issue_id" = "issue_id_p"
              AND "harmonic_weight" ISNULL
              AND coalesce("admitted", FALSE) = FALSE
            )
          )
          ORDER BY "initiative_id" DESC, "weight_den" DESC
          -- NOTE: non-admitted initiatives placed first (at last positions),
          --       latest initiatives treated worse in case of tie
        LOOP
          "summand_v" := "weight_row"."weight_num"::FLOAT / "weight_row"."weight_den"::FLOAT;
          IF "i" = 0 OR "weight_row"."initiative_id" != "id_ary"["i"] THEN
            "i" := "i" + 1;
            "count_v" := "i";
            "id_ary"["i"] := "weight_row"."initiative_id";
            "weight_ary"["i"] := "summand_v";
          ELSE
            "weight_ary"["i"] := "weight_ary"["i"] + "summand_v";
          END IF;
        END LOOP;
        EXIT WHEN "count_v" = 0;
        "i" := 1;
        LOOP
          "weight_ary"["i"] := "weight_ary"["i"]::NUMERIC(18,9)::NUMERIC(12,3);
          IF "min_weight_v" ISNULL OR "weight_ary"["i"] < "min_weight_v" THEN
            "min_weight_v" := "weight_ary"["i"];
          END IF;
          "i" := "i" + 1;
          EXIT WHEN "i" > "count_v";
        END LOOP;
        "i" := 1;
        LOOP
          IF "weight_ary"["i"] = "min_weight_v" THEN
            UPDATE "initiative" SET "harmonic_weight" = "min_weight_v"
              WHERE "id" = "id_ary"["i"];
            EXIT;
          END IF;
          "i" := "i" + 1;
        END LOOP;
      END LOOP;
      UPDATE "initiative" SET "harmonic_weight" = 0
        WHERE "issue_id" = "issue_id_p" AND "harmonic_weight" ISNULL;
    END;
  $$;
COMMENT ON FUNCTION "set_harmonic_initiative_weights"
  ( "issue"."id"%TYPE )
  IS 'Calculates and sets "harmonic_weight" of initiatives in a given issue';

CREATE OR REPLACE FUNCTION "weight_of_added_delegations_for_population_snapshot"
  ( "issue_id_p"            "issue"."id"%TYPE,
    "member_id_p"           "member"."id"%TYPE,
    "delegate_member_ids_p" "delegating_population_snapshot"."delegate_member_ids"%TYPE )
  RETURNS "direct_population_snapshot"."weight"%TYPE
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_delegation_row"  "issue_delegation"%ROWTYPE;
      "delegate_member_ids_v" "delegating_population_snapshot"."delegate_member_ids"%TYPE;
      "weight_v"              INT4;
      "sub_weight_v"          INT4;
    BEGIN
      PERFORM "require_transaction_isolation"();
      "weight_v" := 0;
      FOR "issue_delegation_row" IN
        SELECT * FROM "issue_delegation"
        WHERE "trustee_id" = "member_id_p"
        AND "issue_id" = "issue_id_p"
      LOOP
        IF NOT EXISTS (
          SELECT NULL FROM "direct_population_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "issue_delegation_row"."truster_id"
        ) AND NOT EXISTS (
          SELECT NULL FROM "delegating_population_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "issue_delegation_row"."truster_id"
        ) THEN
          "delegate_member_ids_v" :=
            "member_id_p" || "delegate_member_ids_p";
          INSERT INTO "delegating_population_snapshot" (
              "issue_id",
              "event",
              "member_id",
              "scope",
              "delegate_member_ids"
            ) VALUES (
              "issue_id_p",
              'periodic',
              "issue_delegation_row"."truster_id",
              "issue_delegation_row"."scope",
              "delegate_member_ids_v"
            );
          "sub_weight_v" := 1 +
            "weight_of_added_delegations_for_population_snapshot"(
              "issue_id_p",
              "issue_delegation_row"."truster_id",
              "delegate_member_ids_v"
            );
          UPDATE "delegating_population_snapshot"
            SET "weight" = "sub_weight_v"
            WHERE "issue_id" = "issue_id_p"
            AND "event" = 'periodic'
            AND "member_id" = "issue_delegation_row"."truster_id";
          "weight_v" := "weight_v" + "sub_weight_v";
        END IF;
      END LOOP;
      RETURN "weight_v";
    END;
  $$;

CREATE OR REPLACE FUNCTION "create_population_snapshot"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "require_transaction_isolation"();
      DELETE FROM "direct_population_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic';
      DELETE FROM "delegating_population_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic';
      INSERT INTO "direct_population_snapshot"
        ("issue_id", "event", "member_id")
        SELECT
          "issue_id_p"                 AS "issue_id",
          'periodic'::"snapshot_event" AS "event",
          "member"."id"                AS "member_id"
        FROM "issue"
        JOIN "area" ON "issue"."area_id" = "area"."id"
        JOIN "membership" ON "area"."id" = "membership"."area_id"
        JOIN "member" ON "membership"."member_id" = "member"."id"
        JOIN "privilege"
          ON "privilege"."unit_id" = "area"."unit_id"
          AND "privilege"."member_id" = "member"."id"
        WHERE "issue"."id" = "issue_id_p"
        AND "member"."active" AND "privilege"."voting_right"
        UNION
        SELECT
          "issue_id_p"                 AS "issue_id",
          'periodic'::"snapshot_event" AS "event",
          "member"."id"                AS "member_id"
        FROM "issue"
        JOIN "area" ON "issue"."area_id" = "area"."id"
        JOIN "interest" ON "issue"."id" = "interest"."issue_id"
        JOIN "member" ON "interest"."member_id" = "member"."id"
        JOIN "privilege"
          ON "privilege"."unit_id" = "area"."unit_id"
          AND "privilege"."member_id" = "member"."id"
        WHERE "issue"."id" = "issue_id_p"
        AND "member"."active" AND "privilege"."voting_right";
      FOR "member_id_v" IN
        SELECT "member_id" FROM "direct_population_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic'
      LOOP
        UPDATE "direct_population_snapshot" SET
          "weight" = 1 +
            "weight_of_added_delegations_for_population_snapshot"(
              "issue_id_p",
              "member_id_v",
              '{}'
            )
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "member_id_v";
      END LOOP;
      RETURN;
    END;
  $$;

CREATE OR REPLACE FUNCTION "weight_of_added_delegations_for_interest_snapshot"
  ( "issue_id_p"            "issue"."id"%TYPE,
    "member_id_p"           "member"."id"%TYPE,
    "delegate_member_ids_p" "delegating_interest_snapshot"."delegate_member_ids"%TYPE )
  RETURNS "direct_interest_snapshot"."weight"%TYPE
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_delegation_row"  "issue_delegation"%ROWTYPE;
      "delegate_member_ids_v" "delegating_interest_snapshot"."delegate_member_ids"%TYPE;
      "weight_v"              INT4;
      "sub_weight_v"          INT4;
    BEGIN
      PERFORM "require_transaction_isolation"();
      "weight_v" := 0;
      FOR "issue_delegation_row" IN
        SELECT * FROM "issue_delegation"
        WHERE "trustee_id" = "member_id_p"
        AND "issue_id" = "issue_id_p"
      LOOP
        IF NOT EXISTS (
          SELECT NULL FROM "direct_interest_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "issue_delegation_row"."truster_id"
        ) AND NOT EXISTS (
          SELECT NULL FROM "delegating_interest_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "issue_delegation_row"."truster_id"
        ) THEN
          "delegate_member_ids_v" :=
            "member_id_p" || "delegate_member_ids_p";
          INSERT INTO "delegating_interest_snapshot" (
              "issue_id",
              "event",
              "member_id",
              "scope",
              "delegate_member_ids"
            ) VALUES (
              "issue_id_p",
              'periodic',
              "issue_delegation_row"."truster_id",
              "issue_delegation_row"."scope",
              "delegate_member_ids_v"
            );
          "sub_weight_v" := 1 +
            "weight_of_added_delegations_for_interest_snapshot"(
              "issue_id_p",
              "issue_delegation_row"."truster_id",
              "delegate_member_ids_v"
            );
          UPDATE "delegating_interest_snapshot"
            SET "weight" = "sub_weight_v"
            WHERE "issue_id" = "issue_id_p"
            AND "event" = 'periodic'
            AND "member_id" = "issue_delegation_row"."truster_id";
          "weight_v" := "weight_v" + "sub_weight_v";
        END IF;
      END LOOP;
      RETURN "weight_v";
    END;
  $$;

CREATE OR REPLACE FUNCTION "create_interest_snapshot"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "require_transaction_isolation"();
      DELETE FROM "direct_interest_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic';
      DELETE FROM "delegating_interest_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic';
      DELETE FROM "direct_supporter_snapshot"
        USING "initiative"  -- NOTE: due to missing index on issue_id
        WHERE "initiative"."issue_id" = "issue_id_p"
        AND "direct_supporter_snapshot"."initiative_id" = "initiative"."id"
        AND "direct_supporter_snapshot"."event" = 'periodic';
      INSERT INTO "direct_interest_snapshot"
        ("issue_id", "event", "member_id")
        SELECT
          "issue_id_p"  AS "issue_id",
          'periodic'    AS "event",
          "member"."id" AS "member_id"
        FROM "issue"
        JOIN "area" ON "issue"."area_id" = "area"."id"
        JOIN "interest" ON "issue"."id" = "interest"."issue_id"
        JOIN "member" ON "interest"."member_id" = "member"."id"
        JOIN "privilege"
          ON "privilege"."unit_id" = "area"."unit_id"
          AND "privilege"."member_id" = "member"."id"
        WHERE "issue"."id" = "issue_id_p"
        AND "member"."active" AND "privilege"."voting_right";
      FOR "member_id_v" IN
        SELECT "member_id" FROM "direct_interest_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic'
      LOOP
        UPDATE "direct_interest_snapshot" SET
          "weight" = 1 +
            "weight_of_added_delegations_for_interest_snapshot"(
              "issue_id_p",
              "member_id_v",
              '{}'
            )
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "member_id_v";
      END LOOP;
      INSERT INTO "direct_supporter_snapshot"
        ( "issue_id", "initiative_id", "event", "member_id",
          "draft_id", "informed", "satisfied" )
        SELECT
          "issue_id_p"            AS "issue_id",
          "initiative"."id"       AS "initiative_id",
          'periodic'              AS "event",
          "supporter"."member_id" AS "member_id",
          "supporter"."draft_id"  AS "draft_id",
          "supporter"."draft_id" = "current_draft"."id" AS "informed",
          NOT EXISTS (
            SELECT NULL FROM "critical_opinion"
            WHERE "initiative_id" = "initiative"."id"
            AND "member_id" = "supporter"."member_id"
          ) AS "satisfied"
        FROM "initiative"
        JOIN "supporter"
        ON "supporter"."initiative_id" = "initiative"."id"
        JOIN "current_draft"
        ON "initiative"."id" = "current_draft"."initiative_id"
        JOIN "direct_interest_snapshot"
        ON "supporter"."member_id" = "direct_interest_snapshot"."member_id"
        AND "initiative"."issue_id" = "direct_interest_snapshot"."issue_id"
        AND "event" = 'periodic'
        WHERE "initiative"."issue_id" = "issue_id_p";
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
      PERFORM "require_transaction_isolation"();
      PERFORM "create_population_snapshot"("issue_id_p");
      PERFORM "create_interest_snapshot"("issue_id_p");
      UPDATE "issue" SET
        "snapshot" = coalesce("phase_finished", now()),
        "latest_snapshot_event" = 'periodic',
        "population" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_population_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
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

CREATE OR REPLACE FUNCTION "set_snapshot_event"
  ( "issue_id_p" "issue"."id"%TYPE,
    "event_p" "snapshot_event" )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "event_v" "issue"."latest_snapshot_event"%TYPE;
    BEGIN
      PERFORM "require_transaction_isolation"();
      SELECT "latest_snapshot_event" INTO "event_v" FROM "issue"
        WHERE "id" = "issue_id_p" FOR UPDATE;
      UPDATE "issue" SET "latest_snapshot_event" = "event_p"
        WHERE "id" = "issue_id_p";
      UPDATE "direct_population_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      UPDATE "delegating_population_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      UPDATE "direct_interest_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      UPDATE "delegating_interest_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      UPDATE "direct_supporter_snapshot" SET "event" = "event_p"
        FROM "initiative"  -- NOTE: due to missing index on issue_id
        WHERE "initiative"."issue_id" = "issue_id_p"
        AND "direct_supporter_snapshot"."initiative_id" = "initiative"."id"
        AND "direct_supporter_snapshot"."event" = "event_v";
      RETURN;
    END;
  $$;

DROP FUNCTION "freeze_after_snapshot"("issue"."id"%TYPE);
DROP FUNCTION "manual_freeze"("issue"."id"%TYPE);

CREATE OR REPLACE FUNCTION "weight_of_added_vote_delegations"
  ( "issue_id_p"            "issue"."id"%TYPE,
    "member_id_p"           "member"."id"%TYPE,
    "delegate_member_ids_p" "delegating_voter"."delegate_member_ids"%TYPE )
  RETURNS "direct_voter"."weight"%TYPE
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_delegation_row"  "issue_delegation"%ROWTYPE;
      "delegate_member_ids_v" "delegating_voter"."delegate_member_ids"%TYPE;
      "weight_v"              INT4;
      "sub_weight_v"          INT4;
    BEGIN
      PERFORM "require_transaction_isolation"();
      "weight_v" := 0;
      FOR "issue_delegation_row" IN
        SELECT * FROM "issue_delegation"
        WHERE "trustee_id" = "member_id_p"
        AND "issue_id" = "issue_id_p"
      LOOP
        IF NOT EXISTS (
          SELECT NULL FROM "direct_voter"
          WHERE "member_id" = "issue_delegation_row"."truster_id"
          AND "issue_id" = "issue_id_p"
        ) AND NOT EXISTS (
          SELECT NULL FROM "delegating_voter"
          WHERE "member_id" = "issue_delegation_row"."truster_id"
          AND "issue_id" = "issue_id_p"
        ) THEN
          "delegate_member_ids_v" :=
            "member_id_p" || "delegate_member_ids_p";
          INSERT INTO "delegating_voter" (
              "issue_id",
              "member_id",
              "scope",
              "delegate_member_ids"
            ) VALUES (
              "issue_id_p",
              "issue_delegation_row"."truster_id",
              "issue_delegation_row"."scope",
              "delegate_member_ids_v"
            );
          "sub_weight_v" := 1 +
            "weight_of_added_vote_delegations"(
              "issue_id_p",
              "issue_delegation_row"."truster_id",
              "delegate_member_ids_v"
            );
          UPDATE "delegating_voter"
            SET "weight" = "sub_weight_v"
            WHERE "issue_id" = "issue_id_p"
            AND "member_id" = "issue_delegation_row"."truster_id";
          "weight_v" := "weight_v" + "sub_weight_v";
        END IF;
      END LOOP;
      RETURN "weight_v";
    END;
  $$;

CREATE OR REPLACE FUNCTION "add_vote_delegations"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "require_transaction_isolation"();
      FOR "member_id_v" IN
        SELECT "member_id" FROM "direct_voter"
        WHERE "issue_id" = "issue_id_p"
      LOOP
        UPDATE "direct_voter" SET
          "weight" = "weight" + "weight_of_added_vote_delegations"(
            "issue_id_p",
            "member_id_v",
            '{}'
          )
          WHERE "member_id" = "member_id_v"
          AND "issue_id" = "issue_id_p";
      END LOOP;
      RETURN;
    END;
  $$;

CREATE OR REPLACE FUNCTION "close_voting"("issue_id_p" "issue"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "area_id_v"   "area"."id"%TYPE;
      "unit_id_v"   "unit"."id"%TYPE;
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "require_transaction_isolation"();
      SELECT "area_id" INTO "area_id_v" FROM "issue" WHERE "id" = "issue_id_p";
      SELECT "unit_id" INTO "unit_id_v" FROM "area"  WHERE "id" = "area_id_v";
      -- delete timestamp of voting comment:
      UPDATE "direct_voter" SET "comment_changed" = NULL
        WHERE "issue_id" = "issue_id_p";
      -- delete delegating votes (in cases of manual reset of issue state):
      DELETE FROM "delegating_voter"
        WHERE "issue_id" = "issue_id_p";
      -- delete votes from non-privileged voters:
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
      -- consider delegations:
      UPDATE "direct_voter" SET "weight" = 1
        WHERE "issue_id" = "issue_id_p";
      PERFORM "add_vote_delegations"("issue_id_p");
      -- materialize battle_view:
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
      -- set voter count:
      UPDATE "issue" SET
        "voter_count" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_voter" WHERE "issue_id" = "issue_id_p"
        )
        WHERE "id" = "issue_id_p";
      -- copy "positive_votes" and "negative_votes" from "battle" table:
      UPDATE "initiative" SET
        "positive_votes" = "battle_win"."count",
        "negative_votes" = "battle_lose"."count"
        FROM "battle" AS "battle_win", "battle" AS "battle_lose"
        WHERE
          "battle_win"."issue_id" = "issue_id_p" AND
          "battle_win"."winning_initiative_id" = "initiative"."id" AND
          "battle_win"."losing_initiative_id" ISNULL AND
          "battle_lose"."issue_id" = "issue_id_p" AND
          "battle_lose"."losing_initiative_id" = "initiative"."id" AND
          "battle_lose"."winning_initiative_id" ISNULL;
    END;
  $$;

CREATE OR REPLACE FUNCTION "calculate_ranks"("issue_id_p" "issue"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row"         "issue"%ROWTYPE;
      "policy_row"        "policy"%ROWTYPE;
      "dimension_v"       INTEGER;
      "vote_matrix"       INT4[][];  -- absolute votes
      "matrix"            INT8[][];  -- defeat strength / best paths
      "i"                 INTEGER;
      "j"                 INTEGER;
      "k"                 INTEGER;
      "battle_row"        "battle"%ROWTYPE;
      "rank_ary"          INT4[];
      "rank_v"            INT4;
      "done_v"            INTEGER;
      "winners_ary"       INTEGER[];
      "initiative_id_v"   "initiative"."id"%TYPE;
    BEGIN
      PERFORM "require_transaction_isolation"();
      SELECT * INTO "issue_row"
        FROM "issue" WHERE "id" = "issue_id_p";
      SELECT * INTO "policy_row"
        FROM "policy" WHERE "id" = "issue_row"."policy_id";
      SELECT count(1) INTO "dimension_v"
        FROM "battle_participant" WHERE "issue_id" = "issue_id_p";
      -- Create "vote_matrix" with absolute number of votes in pairwise
      -- comparison:
      "vote_matrix" := array_fill(NULL::INT4, ARRAY["dimension_v", "dimension_v"]);
      "i" := 1;
      "j" := 2;
      FOR "battle_row" IN
        SELECT * FROM "battle" WHERE "issue_id" = "issue_id_p"
        ORDER BY
        "winning_initiative_id" NULLS LAST,
        "losing_initiative_id" NULLS LAST
      LOOP
        "vote_matrix"["i"]["j"] := "battle_row"."count";
        IF "j" = "dimension_v" THEN
          "i" := "i" + 1;
          "j" := 1;
        ELSE
          "j" := "j" + 1;
          IF "j" = "i" THEN
            "j" := "j" + 1;
          END IF;
        END IF;
      END LOOP;
      IF "i" != "dimension_v" OR "j" != "dimension_v" + 1 THEN
        RAISE EXCEPTION 'Wrong battle count (should not happen)';
      END IF;
      -- Store defeat strengths in "matrix" using "defeat_strength"
      -- function:
      "matrix" := array_fill(NULL::INT8, ARRAY["dimension_v", "dimension_v"]);
      "i" := 1;
      LOOP
        "j" := 1;
        LOOP
          IF "i" != "j" THEN
            "matrix"["i"]["j"] := "defeat_strength"(
              "vote_matrix"["i"]["j"],
              "vote_matrix"["j"]["i"]
            );
          END IF;
          EXIT WHEN "j" = "dimension_v";
          "j" := "j" + 1;
        END LOOP;
        EXIT WHEN "i" = "dimension_v";
        "i" := "i" + 1;
      END LOOP;
      -- Find best paths:
      "i" := 1;
      LOOP
        "j" := 1;
        LOOP
          IF "i" != "j" THEN
            "k" := 1;
            LOOP
              IF "i" != "k" AND "j" != "k" THEN
                IF "matrix"["j"]["i"] < "matrix"["i"]["k"] THEN
                  IF "matrix"["j"]["i"] > "matrix"["j"]["k"] THEN
                    "matrix"["j"]["k"] := "matrix"["j"]["i"];
                  END IF;
                ELSE
                  IF "matrix"["i"]["k"] > "matrix"["j"]["k"] THEN
                    "matrix"["j"]["k"] := "matrix"["i"]["k"];
                  END IF;
                END IF;
              END IF;
              EXIT WHEN "k" = "dimension_v";
              "k" := "k" + 1;
            END LOOP;
          END IF;
          EXIT WHEN "j" = "dimension_v";
          "j" := "j" + 1;
        END LOOP;
        EXIT WHEN "i" = "dimension_v";
        "i" := "i" + 1;
      END LOOP;
      -- Determine order of winners:
      "rank_ary" := array_fill(NULL::INT4, ARRAY["dimension_v"]);
      "rank_v" := 1;
      "done_v" := 0;
      LOOP
        "winners_ary" := '{}';
        "i" := 1;
        LOOP
          IF "rank_ary"["i"] ISNULL THEN
            "j" := 1;
            LOOP
              IF
                "i" != "j" AND
                "rank_ary"["j"] ISNULL AND
                "matrix"["j"]["i"] > "matrix"["i"]["j"]
              THEN
                -- someone else is better
                EXIT;
              END IF;
              IF "j" = "dimension_v" THEN
                -- noone is better
                "winners_ary" := "winners_ary" || "i";
                EXIT;
              END IF;
              "j" := "j" + 1;
            END LOOP;
          END IF;
          EXIT WHEN "i" = "dimension_v";
          "i" := "i" + 1;
        END LOOP;
        "i" := 1;
        LOOP
          "rank_ary"["winners_ary"["i"]] := "rank_v";
          "done_v" := "done_v" + 1;
          EXIT WHEN "i" = array_upper("winners_ary", 1);
          "i" := "i" + 1;
        END LOOP;
        EXIT WHEN "done_v" = "dimension_v";
        "rank_v" := "rank_v" + 1;
      END LOOP;
      -- write preliminary results:
      "i" := 1;
      FOR "initiative_id_v" IN
        SELECT "id" FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "admitted"
        ORDER BY "id"
      LOOP
        UPDATE "initiative" SET
          "direct_majority" =
            CASE WHEN "policy_row"."direct_majority_strict" THEN
              "positive_votes" * "policy_row"."direct_majority_den" >
              "policy_row"."direct_majority_num" * ("positive_votes"+"negative_votes")
            ELSE
              "positive_votes" * "policy_row"."direct_majority_den" >=
              "policy_row"."direct_majority_num" * ("positive_votes"+"negative_votes")
            END
            AND "positive_votes" >= "policy_row"."direct_majority_positive"
            AND "issue_row"."voter_count"-"negative_votes" >=
                "policy_row"."direct_majority_non_negative",
            "indirect_majority" =
            CASE WHEN "policy_row"."indirect_majority_strict" THEN
              "positive_votes" * "policy_row"."indirect_majority_den" >
              "policy_row"."indirect_majority_num" * ("positive_votes"+"negative_votes")
            ELSE
              "positive_votes" * "policy_row"."indirect_majority_den" >=
              "policy_row"."indirect_majority_num" * ("positive_votes"+"negative_votes")
            END
            AND "positive_votes" >= "policy_row"."indirect_majority_positive"
            AND "issue_row"."voter_count"-"negative_votes" >=
                "policy_row"."indirect_majority_non_negative",
          "schulze_rank"           = "rank_ary"["i"],
          "better_than_status_quo" = "rank_ary"["i"] < "rank_ary"["dimension_v"],
          "worse_than_status_quo"  = "rank_ary"["i"] > "rank_ary"["dimension_v"],
          "multistage_majority"    = "rank_ary"["i"] >= "rank_ary"["dimension_v"],
          "reverse_beat_path"      = "matrix"["dimension_v"]["i"] >= 0,
          "eligible"               = FALSE,
          "winner"                 = FALSE,
          "rank"                   = NULL  -- NOTE: in cases of manual reset of issue state
          WHERE "id" = "initiative_id_v";
        "i" := "i" + 1;
      END LOOP;
      IF "i" != "dimension_v" THEN
        RAISE EXCEPTION 'Wrong winner count (should not happen)';
      END IF;
      -- take indirect majorities into account:
      LOOP
        UPDATE "initiative" SET "indirect_majority" = TRUE
          FROM (
            SELECT "new_initiative"."id" AS "initiative_id"
            FROM "initiative" "old_initiative"
            JOIN "initiative" "new_initiative"
              ON "new_initiative"."issue_id" = "issue_id_p"
              AND "new_initiative"."indirect_majority" = FALSE
            JOIN "battle" "battle_win"
              ON "battle_win"."issue_id" = "issue_id_p"
              AND "battle_win"."winning_initiative_id" = "new_initiative"."id"
              AND "battle_win"."losing_initiative_id" = "old_initiative"."id"
            JOIN "battle" "battle_lose"
              ON "battle_lose"."issue_id" = "issue_id_p"
              AND "battle_lose"."losing_initiative_id" = "new_initiative"."id"
              AND "battle_lose"."winning_initiative_id" = "old_initiative"."id"
            WHERE "old_initiative"."issue_id" = "issue_id_p"
            AND "old_initiative"."indirect_majority" = TRUE
            AND CASE WHEN "policy_row"."indirect_majority_strict" THEN
              "battle_win"."count" * "policy_row"."indirect_majority_den" >
              "policy_row"."indirect_majority_num" *
              ("battle_win"."count"+"battle_lose"."count")
            ELSE
              "battle_win"."count" * "policy_row"."indirect_majority_den" >=
              "policy_row"."indirect_majority_num" *
              ("battle_win"."count"+"battle_lose"."count")
            END
            AND "battle_win"."count" >= "policy_row"."indirect_majority_positive"
            AND "issue_row"."voter_count"-"battle_lose"."count" >=
                "policy_row"."indirect_majority_non_negative"
          ) AS "subquery"
          WHERE "id" = "subquery"."initiative_id";
        EXIT WHEN NOT FOUND;
      END LOOP;
      -- set "multistage_majority" for remaining matching initiatives:
      UPDATE "initiative" SET "multistage_majority" = TRUE
        FROM (
          SELECT "losing_initiative"."id" AS "initiative_id"
          FROM "initiative" "losing_initiative"
          JOIN "initiative" "winning_initiative"
            ON "winning_initiative"."issue_id" = "issue_id_p"
            AND "winning_initiative"."admitted"
          JOIN "battle" "battle_win"
            ON "battle_win"."issue_id" = "issue_id_p"
            AND "battle_win"."winning_initiative_id" = "winning_initiative"."id"
            AND "battle_win"."losing_initiative_id" = "losing_initiative"."id"
          JOIN "battle" "battle_lose"
            ON "battle_lose"."issue_id" = "issue_id_p"
            AND "battle_lose"."losing_initiative_id" = "winning_initiative"."id"
            AND "battle_lose"."winning_initiative_id" = "losing_initiative"."id"
          WHERE "losing_initiative"."issue_id" = "issue_id_p"
          AND "losing_initiative"."admitted"
          AND "winning_initiative"."schulze_rank" <
              "losing_initiative"."schulze_rank"
          AND "battle_win"."count" > "battle_lose"."count"
          AND (
            "battle_win"."count" > "winning_initiative"."positive_votes" OR
            "battle_lose"."count" < "losing_initiative"."negative_votes" )
        ) AS "subquery"
        WHERE "id" = "subquery"."initiative_id";
      -- mark eligible initiatives:
      UPDATE "initiative" SET "eligible" = TRUE
        WHERE "issue_id" = "issue_id_p"
        AND "initiative"."direct_majority"
        AND "initiative"."indirect_majority"
        AND "initiative"."better_than_status_quo"
        AND (
          "policy_row"."no_multistage_majority" = FALSE OR
          "initiative"."multistage_majority" = FALSE )
        AND (
          "policy_row"."no_reverse_beat_path" = FALSE OR
          "initiative"."reverse_beat_path" = FALSE );
      -- mark final winner:
      UPDATE "initiative" SET "winner" = TRUE
        FROM (
          SELECT "id" AS "initiative_id"
          FROM "initiative"
          WHERE "issue_id" = "issue_id_p" AND "eligible"
          ORDER BY
            "schulze_rank",
            "id"
          LIMIT 1
        ) AS "subquery"
        WHERE "id" = "subquery"."initiative_id";
      -- write (final) ranks:
      "rank_v" := 1;
      FOR "initiative_id_v" IN
        SELECT "id"
        FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "admitted"
        ORDER BY
          "winner" DESC,
          "eligible" DESC,
          "schulze_rank",
          "id"
      LOOP
        UPDATE "initiative" SET "rank" = "rank_v"
          WHERE "id" = "initiative_id_v";
        "rank_v" := "rank_v" + 1;
      END LOOP;
      -- set schulze rank of status quo and mark issue as finished:
      UPDATE "issue" SET
        "status_quo_schulze_rank" = "rank_ary"["dimension_v"],
        "state" =
          CASE WHEN EXISTS (
            SELECT NULL FROM "initiative"
            WHERE "issue_id" = "issue_id_p" AND "winner"
          ) THEN
            'finished_with_winner'::"issue_state"
          ELSE
            'finished_without_winner'::"issue_state"
          END,
        "closed" = "phase_finished",
        "phase_finished" = NULL
        WHERE "id" = "issue_id_p";
      RETURN;
    END;
  $$;

DROP FUNCTION "check_issue"("issue"."id"%TYPE);

CREATE TYPE "check_issue_persistence" AS (
        "state"                 "issue_state",
        "phase_finished"        BOOLEAN,
        "issue_revoked"         BOOLEAN,
        "snapshot_created"      BOOLEAN,
        "harmonic_weights_set"  BOOLEAN,
        "closed_voting"         BOOLEAN );
COMMENT ON TYPE "check_issue_persistence" IS 'Type of data returned by "check_issue" function, to be passed to subsequent calls of the same function';

CREATE FUNCTION "check_issue"
  ( "issue_id_p" "issue"."id"%TYPE,
    "persist"    "check_issue_persistence" )
  RETURNS "check_issue_persistence"
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row"      "issue"%ROWTYPE;
      "policy_row"     "policy"%ROWTYPE;
      "initiative_row" "initiative"%ROWTYPE;
      "state_v"        "issue_state";
    BEGIN
      PERFORM "require_transaction_isolation"();
      IF "persist" ISNULL THEN
        SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p"
          FOR UPDATE;
        IF "issue_row"."closed" NOTNULL THEN
          RETURN NULL;
        END IF;
        "persist"."state" := "issue_row"."state";
        IF
          ( "issue_row"."state" = 'admission' AND now() >=
            "issue_row"."created" + "issue_row"."admission_time" ) OR
          ( "issue_row"."state" = 'discussion' AND now() >=
            "issue_row"."accepted" + "issue_row"."discussion_time" ) OR
          ( "issue_row"."state" = 'verification' AND now() >=
            "issue_row"."half_frozen" + "issue_row"."verification_time" ) OR
          ( "issue_row"."state" = 'voting' AND now() >=
            "issue_row"."fully_frozen" + "issue_row"."voting_time" )
        THEN
          "persist"."phase_finished" := TRUE;
        ELSE
          "persist"."phase_finished" := FALSE;
        END IF;
        IF
          NOT EXISTS (
            -- all initiatives are revoked
            SELECT NULL FROM "initiative"
            WHERE "issue_id" = "issue_id_p" AND "revoked" ISNULL
          ) AND (
            -- and issue has not been accepted yet
            "persist"."state" = 'admission' OR
            -- or verification time has elapsed
            ( "persist"."state" = 'verification' AND
              "persist"."phase_finished" ) OR
            -- or no initiatives have been revoked lately
            NOT EXISTS (
              SELECT NULL FROM "initiative"
              WHERE "issue_id" = "issue_id_p"
              AND now() < "revoked" + "issue_row"."verification_time"
            )
          )
        THEN
          "persist"."issue_revoked" := TRUE;
        ELSE
          "persist"."issue_revoked" := FALSE;
        END IF;
        IF "persist"."phase_finished" OR "persist"."issue_revoked" THEN
          UPDATE "issue" SET "phase_finished" = now()
            WHERE "id" = "issue_row"."id";
          RETURN "persist";
        ELSIF
          "persist"."state" IN ('admission', 'discussion', 'verification')
        THEN
          RETURN "persist";
        ELSE
          RETURN NULL;
        END IF;
      END IF;
      IF
        "persist"."state" IN ('admission', 'discussion', 'verification') AND
        coalesce("persist"."snapshot_created", FALSE) = FALSE
      THEN
        PERFORM "create_snapshot"("issue_id_p");
        "persist"."snapshot_created" = TRUE;
        IF "persist"."phase_finished" THEN
          IF "persist"."state" = 'admission' THEN
            PERFORM "set_snapshot_event"("issue_id_p", 'end_of_admission');
          ELSIF "persist"."state" = 'discussion' THEN
            PERFORM "set_snapshot_event"("issue_id_p", 'half_freeze');
          ELSIF "persist"."state" = 'verification' THEN
            PERFORM "set_snapshot_event"("issue_id_p", 'full_freeze');
            SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
            SELECT * INTO "policy_row" FROM "policy"
              WHERE "id" = "issue_row"."policy_id";
            FOR "initiative_row" IN
              SELECT * FROM "initiative"
              WHERE "issue_id" = "issue_id_p" AND "revoked" ISNULL
              FOR UPDATE
            LOOP
              IF
                "initiative_row"."polling" OR (
                  "initiative_row"."satisfied_supporter_count" > 0 AND
                  "initiative_row"."satisfied_supporter_count" *
                  "policy_row"."initiative_quorum_den" >=
                  "issue_row"."population" * "policy_row"."initiative_quorum_num"
                )
              THEN
                UPDATE "initiative" SET "admitted" = TRUE
                  WHERE "id" = "initiative_row"."id";
              ELSE
                UPDATE "initiative" SET "admitted" = FALSE
                  WHERE "id" = "initiative_row"."id";
              END IF;
            END LOOP;
          END IF;
        END IF;
        RETURN "persist";
      END IF;
      IF
        "persist"."state" IN ('admission', 'discussion', 'verification') AND
        coalesce("persist"."harmonic_weights_set", FALSE) = FALSE
      THEN
        PERFORM "set_harmonic_initiative_weights"("issue_id_p");
        "persist"."harmonic_weights_set" = TRUE;
        IF
          "persist"."phase_finished" OR
          "persist"."issue_revoked" OR
          "persist"."state" = 'admission'
        THEN
          RETURN "persist";
        ELSE
          RETURN NULL;
        END IF;
      END IF;
      IF "persist"."issue_revoked" THEN
        IF "persist"."state" = 'admission' THEN
          "state_v" := 'canceled_revoked_before_accepted';
        ELSIF "persist"."state" = 'discussion' THEN
          "state_v" := 'canceled_after_revocation_during_discussion';
        ELSIF "persist"."state" = 'verification' THEN
          "state_v" := 'canceled_after_revocation_during_verification';
        END IF;
        UPDATE "issue" SET
          "state"          = "state_v",
          "closed"         = "phase_finished",
          "phase_finished" = NULL
          WHERE "id" = "issue_id_p";
        RETURN NULL;
      END IF;
      IF "persist"."state" = 'admission' THEN
        SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p"
          FOR UPDATE;
        SELECT * INTO "policy_row"
          FROM "policy" WHERE "id" = "issue_row"."policy_id";
        IF EXISTS (
          SELECT NULL FROM "initiative"
          WHERE "issue_id" = "issue_id_p"
          AND "supporter_count" > 0
          AND "supporter_count" * "policy_row"."issue_quorum_den"
          >= "issue_row"."population" * "policy_row"."issue_quorum_num"
        ) THEN
          UPDATE "issue" SET
            "state"          = 'discussion',
            "accepted"       = coalesce("phase_finished", now()),
            "phase_finished" = NULL
            WHERE "id" = "issue_id_p";
        ELSIF "issue_row"."phase_finished" NOTNULL THEN
          UPDATE "issue" SET
            "state"          = 'canceled_issue_not_accepted',
            "closed"         = "phase_finished",
            "phase_finished" = NULL
            WHERE "id" = "issue_id_p";
        END IF;
        RETURN NULL;
      END IF;
      IF "persist"."phase_finished" THEN
        if "persist"."state" = 'discussion' THEN
          UPDATE "issue" SET
            "state"          = 'verification',
            "half_frozen"    = "phase_finished",
            "phase_finished" = NULL
            WHERE "id" = "issue_id_p";
          RETURN NULL;
        END IF;
        IF "persist"."state" = 'verification' THEN
          SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p"
            FOR UPDATE;
          SELECT * INTO "policy_row" FROM "policy"
            WHERE "id" = "issue_row"."policy_id";
          IF EXISTS (
            SELECT NULL FROM "initiative"
            WHERE "issue_id" = "issue_id_p" AND "admitted" = TRUE
          ) THEN
            UPDATE "issue" SET
              "state"          = 'voting',
              "fully_frozen"   = "phase_finished",
              "phase_finished" = NULL
              WHERE "id" = "issue_id_p";
          ELSE
            UPDATE "issue" SET
              "state"          = 'canceled_no_initiative_admitted',
              "fully_frozen"   = "phase_finished",
              "closed"         = "phase_finished",
              "phase_finished" = NULL
              WHERE "id" = "issue_id_p";
            -- NOTE: The following DELETE statements have effect only when
            --       issue state has been manipulated
            DELETE FROM "direct_voter"     WHERE "issue_id" = "issue_id_p";
            DELETE FROM "delegating_voter" WHERE "issue_id" = "issue_id_p";
            DELETE FROM "battle"           WHERE "issue_id" = "issue_id_p";
          END IF;
          RETURN NULL;
        END IF;
        IF "persist"."state" = 'voting' THEN
          IF coalesce("persist"."closed_voting", FALSE) = FALSE THEN
            PERFORM "close_voting"("issue_id_p");
            "persist"."closed_voting" = TRUE;
            RETURN "persist";
          END IF;
          PERFORM "calculate_ranks"("issue_id_p");
          RETURN NULL;
        END IF;
      END IF;
      RAISE WARNING 'should not happen';
      RETURN NULL;
    END;
  $$;
COMMENT ON FUNCTION "check_issue"
  ( "issue"."id"%TYPE,
    "check_issue_persistence" )
  IS 'Precalculate supporter counts etc. for a given issue, and check, if status change is required, and perform the status change when necessary; Function must be called multiple times with the previous result as second parameter, until the result is NULL (see source code of function "check_everything")';

CREATE OR REPLACE FUNCTION "check_everything"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_id_v" "issue"."id"%TYPE;
      "persist_v"  "check_issue_persistence";
    BEGIN
      RAISE WARNING 'Function "check_everything" should only be used for development and debugging purposes';
      DELETE FROM "expired_session";
      PERFORM "check_activity"();
      PERFORM "calculate_member_counts"();
      FOR "issue_id_v" IN SELECT "id" FROM "open_issue" LOOP
        "persist_v" := NULL;
        LOOP
          "persist_v" := "check_issue"("issue_id_v", "persist_v");
          EXIT WHEN "persist_v" ISNULL;
        END LOOP;
      END LOOP;
      RETURN;
    END;
  $$;
COMMENT ON FUNCTION "check_everything"() IS 'Amongst other regular tasks this function performs "check_issue" for every open issue. Use this function only for development and debugging purposes, as you may run into locking and/or serialization problems in productive environments.';

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
          "state"  = 'voting',
          "closed" = NULL
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
        DELETE FROM "non_voter"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "delegation"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "supporter"
          USING "initiative"  -- NOTE: due to missing index on issue_id
          WHERE "initiative"."issue_id" = "issue_id_p"
          AND "supporter"."initiative_id" = "initiative_id";
        UPDATE "issue" SET
          "state"   = "issue_row"."state",
          "closed"  = "issue_row"."closed",
          "cleaned" = now()
          WHERE "id" = "issue_id_p";
      END IF;
      RETURN;
    END;
  $$;

SELECT "set_harmonic_initiative_weights"("id") FROM "issue";

COMMIT;
