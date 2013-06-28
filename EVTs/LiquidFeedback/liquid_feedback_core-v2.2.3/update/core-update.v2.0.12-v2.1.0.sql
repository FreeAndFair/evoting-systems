BEGIN;


-- update version number

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('2.1.0', 2, 1, 0))
  AS "subquery"("string", "major", "minor", "revision");


-- old API tables are now deprecated

COMMENT ON TYPE "application_access_level" IS 'DEPRECATED, WILL BE REMOVED! Access privileges for applications using the API';
COMMENT ON TABLE "member_application" IS 'DEPRECATED, WILL BE REMOVED! Registered application being allowed to use the API';


-- new polling mode and changed privileges

ALTER TABLE "policy" ADD COLUMN "polling" BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE "policy" ALTER COLUMN "admission_time"    DROP NOT NULL;
ALTER TABLE "policy" ALTER COLUMN "discussion_time"   DROP NOT NULL;
ALTER TABLE "policy" ALTER COLUMN "verification_time" DROP NOT NULL;
ALTER TABLE "policy" ALTER COLUMN "voting_time"       DROP NOT NULL;
ALTER TABLE "policy" ALTER COLUMN "issue_quorum_num"  DROP NOT NULL;
ALTER TABLE "policy" ALTER COLUMN "issue_quorum_den"  DROP NOT NULL;
ALTER TABLE "policy" ADD CONSTRAINT "timing" CHECK (
          ( "polling" = FALSE AND
            "admission_time" NOTNULL AND "discussion_time" NOTNULL AND
            "verification_time" NOTNULL AND "voting_time" NOTNULL ) OR
          ( "polling" = TRUE AND
            "admission_time" ISNULL AND "discussion_time" NOTNULL AND
            "verification_time" NOTNULL AND "voting_time" NOTNULL ) OR
          ( "polling" = TRUE AND
            "admission_time" ISNULL AND "discussion_time" ISNULL AND
            "verification_time" ISNULL AND "voting_time" ISNULL ) );
ALTER TABLE "policy" ADD CONSTRAINT "issue_quorum_if_and_only_if_not_polling" CHECK (
          "polling" = "issue_quorum_num" ISNULL AND
          "polling" = "issue_quorum_den" ISNULL );
COMMENT ON COLUMN "policy"."polling" IS 'TRUE = special policy for non-user-generated issues without issue quorum, where certain initiatives (those having the "polling" flag set) do not need to pass the initiative quorum; "admission_time" MUST be set to NULL, the other timings may be set to NULL altogether, allowing individual timing for those issues';

ALTER TABLE "issue" ALTER COLUMN "admission_time" DROP NOT NULL;
ALTER TABLE "issue" ADD CONSTRAINT "admission_time_not_null_unless_instantly_accepted" CHECK (
  "admission_time" NOTNULL OR ("accepted" NOTNULL AND "accepted" = "created") );

ALTER TABLE "initiative" ADD COLUMN "polling" BOOLEAN NOT NULL DEFAULT FALSE;
COMMENT ON COLUMN "initiative"."polling" IS 'Initiative does not need to pass the initiative quorum (see "policy"."polling")';

ALTER TABLE "privilege" RENAME COLUMN "voting_right_manager" TO "member_manager";
ALTER TABLE "privilege" ADD COLUMN "initiative_right" BOOLEAN NOT NULL DEFAULT TRUE;
ALTER TABLE "privilege" ADD COLUMN "polling_right"    BOOLEAN NOT NULL DEFAULT FALSE;
UPDATE "privilege" SET "initiative_right" = "voting_right";
COMMENT ON COLUMN "privilege"."admin_manager"    IS 'Grant/revoke any privileges to/from other members';
COMMENT ON COLUMN "privilege"."member_manager"   IS 'Adding/removing members from the unit, granting or revoking "initiative_right" and "voting_right"';
COMMENT ON COLUMN "privilege"."initiative_right" IS 'Right to create an initiative';
COMMENT ON COLUMN "privilege"."voting_right"     IS 'Right to support initiatives, create and rate suggestions, and to vote';
COMMENT ON COLUMN "privilege"."polling_right"    IS 'Right to create issues with policies having the "policy"."polling" flag set, and to add initiatives having the "initiative"."polling" flag set to those issues';

DROP VIEW "member_contingent_left";
DROP VIEW "member_contingent";
ALTER TABLE "contingent" DROP CONSTRAINT "contingent_pkey";
ALTER TABLE "contingent" ALTER COLUMN "time_frame" DROP NOT NULL;
ALTER TABLE "contingent" ADD COLUMN "polling" BOOLEAN DEFAULT FALSE;
ALTER TABLE "contingent" ADD PRIMARY KEY ("polling", "time_frame");
ALTER TABLE "contingent" ALTER COLUMN "polling" DROP DEFAULT;
COMMENT ON COLUMN "contingent"."polling" IS 'Determines if settings are for creating initiatives and new drafts of initiatives with "polling" flag set';

CREATE VIEW "member_contingent" AS
  SELECT
    "member"."id" AS "member_id",
    "contingent"."polling",
    "contingent"."time_frame",
    CASE WHEN "contingent"."text_entry_limit" NOTNULL THEN
      (
        SELECT count(1) FROM "draft"
        JOIN "initiative" ON "initiative"."id" = "draft"."initiative_id"
        WHERE "draft"."author_id" = "member"."id"
        AND "initiative"."polling" = "contingent"."polling"
        AND "draft"."created" > now() - "contingent"."time_frame"
      ) + (
        SELECT count(1) FROM "suggestion"
        JOIN "initiative" ON "initiative"."id" = "suggestion"."initiative_id"
        WHERE "suggestion"."author_id" = "member"."id"
        AND "contingent"."polling" = FALSE
        AND "suggestion"."created" > now() - "contingent"."time_frame"
      )
    ELSE NULL END AS "text_entry_count",
    "contingent"."text_entry_limit",
    CASE WHEN "contingent"."initiative_limit" NOTNULL THEN (
      SELECT count(1) FROM "opening_draft" AS "draft"
        JOIN "initiative" ON "initiative"."id" = "draft"."initiative_id"
      WHERE "draft"."author_id" = "member"."id"
      AND "initiative"."polling" = "contingent"."polling"
      AND "draft"."created" > now() - "contingent"."time_frame"
    ) ELSE NULL END AS "initiative_count",
    "contingent"."initiative_limit"
  FROM "member" CROSS JOIN "contingent";

COMMENT ON VIEW "member_contingent" IS 'Actual counts of text entries and initiatives are calculated per member for each limit in the "contingent" table.';

COMMENT ON COLUMN "member_contingent"."text_entry_count" IS 'Only calculated when "text_entry_limit" is not null in the same row';
COMMENT ON COLUMN "member_contingent"."initiative_count" IS 'Only calculated when "initiative_limit" is not null in the same row';

CREATE VIEW "member_contingent_left" AS
  SELECT
    "member_id",
    "polling",
    max("text_entry_limit" - "text_entry_count") AS "text_entries_left",
    max("initiative_limit" - "initiative_count") AS "initiatives_left"
  FROM "member_contingent" GROUP BY "member_id", "polling";

COMMENT ON VIEW "member_contingent_left" IS 'Amount of text entries or initiatives which can be posted now instantly by a member. This view should be used by a frontend to determine, if the contingent for posting is exhausted.';

CREATE OR REPLACE FUNCTION "freeze_after_snapshot"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row"      "issue"%ROWTYPE;
      "policy_row"     "policy"%ROWTYPE;
      "initiative_row" "initiative"%ROWTYPE;
    BEGIN
      SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
      SELECT * INTO "policy_row"
        FROM "policy" WHERE "id" = "issue_row"."policy_id";
      PERFORM "set_snapshot_event"("issue_id_p", 'full_freeze');
      FOR "initiative_row" IN
        SELECT * FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "revoked" ISNULL
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
      IF EXISTS (
        SELECT NULL FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "admitted" = TRUE
      ) THEN
        UPDATE "issue" SET
          "state"        = 'voting',
          "accepted"     = coalesce("accepted", now()),
          "half_frozen"  = coalesce("half_frozen", now()),
          "fully_frozen" = now()
          WHERE "id" = "issue_id_p";
      ELSE
        UPDATE "issue" SET
          "state"           = 'canceled_no_initiative_admitted',
          "accepted"        = coalesce("accepted", now()),
          "half_frozen"     = coalesce("half_frozen", now()),
          "fully_frozen"    = now(),
          "closed"          = now(),
          "ranks_available" = TRUE
          WHERE "id" = "issue_id_p";
        -- NOTE: The following DELETE statements have effect only when
        --       issue state has been manipulated
        DELETE FROM "direct_voter"     WHERE "issue_id" = "issue_id_p";
        DELETE FROM "delegating_voter" WHERE "issue_id" = "issue_id_p";
        DELETE FROM "battle"           WHERE "issue_id" = "issue_id_p";
      END IF;
      RETURN;
    END;
  $$;


-- issue comments removed, voting comments integrated in "direct_voter" table

ALTER TABLE "direct_voter" ADD COLUMN "comment_changed"   TIMESTAMPTZ;
ALTER TABLE "direct_voter" ADD COLUMN "formatting_engine" TEXT;
ALTER TABLE "direct_voter" ADD COLUMN "comment"           TEXT;
ALTER TABLE "direct_voter" ADD COLUMN "text_search_data"  TSVECTOR;
CREATE INDEX "direct_voter_text_search_data_idx" ON "direct_voter" USING gin ("text_search_data");
CREATE TRIGGER "update_text_search_data"
  BEFORE INSERT OR UPDATE ON "direct_voter"
  FOR EACH ROW EXECUTE PROCEDURE
  tsvector_update_trigger('text_search_data', 'pg_catalog.simple', "comment");

COMMENT ON COLUMN "direct_voter"."comment_changed"   IS 'Shall be set on comment change, to indicate a comment being modified after voting has been finished; Automatically set to NULL after voting phase; Automatically set to NULL by trigger, if "comment" is set to NULL';
COMMENT ON COLUMN "direct_voter"."formatting_engine" IS 'Allows different formatting engines (i.e. wiki formats) to be used for "direct_voter"."comment"; Automatically set to NULL by trigger, if "comment" is set to NULL';
COMMENT ON COLUMN "direct_voter"."comment"           IS 'Is to be set or updated by the frontend, if comment was inserted or updated AFTER the issue has been closed. Otherwise it shall be set to NULL.';

CREATE TABLE "rendered_voter_comment" (
        PRIMARY KEY ("issue_id", "member_id", "format"),
        FOREIGN KEY ("issue_id", "member_id")
          REFERENCES "direct_voter" ("issue_id", "member_id")
          ON DELETE CASCADE ON UPDATE CASCADE,
        "issue_id"              INT4,
        "member_id"             INT4,
        "format"                TEXT,
        "content"               TEXT            NOT NULL );

COMMENT ON TABLE "rendered_voter_comment" IS 'This table may be used by frontends to cache "rendered" voter comments (e.g. HTML output generated from wiki text)';

DROP TABLE "rendered_issue_comment";
DROP TABLE "issue_comment";
DROP TABLE "rendered_voting_comment";
DROP TABLE "voting_comment";

CREATE FUNCTION "voter_comment_fields_only_set_when_voter_comment_is_set_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF NEW."comment" ISNULL THEN
        NEW."comment_changed" := NULL;
        NEW."formatting_engine" := NULL;
      END IF;
      RETURN NEW;
    END;
  $$;

CREATE TRIGGER "voter_comment_fields_only_set_when_voter_comment_is_set"
  BEFORE INSERT OR UPDATE ON "direct_voter"
  FOR EACH ROW EXECUTE PROCEDURE
  "voter_comment_fields_only_set_when_voter_comment_is_set_trigger"();

COMMENT ON FUNCTION "voter_comment_fields_only_set_when_voter_comment_is_set_trigger"() IS 'Implementation of trigger "voter_comment_fields_only_set_when_voter_comment_is_set" ON table "direct_voter"';
COMMENT ON TRIGGER "voter_comment_fields_only_set_when_voter_comment_is_set" ON "direct_voter" IS 'If "comment" is set to NULL, then other comment related fields are also set to NULL.';

CREATE OR REPLACE FUNCTION "forbid_changes_on_closed_issue_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_id_v" "issue"."id"%TYPE;
      "issue_row"  "issue"%ROWTYPE;
    BEGIN
      IF TG_RELID = 'direct_voter'::regclass AND TG_OP = 'UPDATE' THEN
        IF
          OLD."issue_id"  = NEW."issue_id"  AND
          OLD."member_id" = NEW."member_id" AND
          OLD."weight"    = NEW."weight"
        THEN
          RETURN NULL;  -- allows changing of voter comment
        END IF;
      END IF;
      IF TG_OP = 'DELETE' THEN
        "issue_id_v" := OLD."issue_id";
      ELSE
        "issue_id_v" := NEW."issue_id";
      END IF;
      SELECT INTO "issue_row" * FROM "issue"
        WHERE "id" = "issue_id_v" FOR SHARE;
      IF "issue_row"."closed" NOTNULL THEN
        RAISE EXCEPTION 'Tried to modify data belonging to a closed issue.';
      END IF;
      RETURN NULL;
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
      PERFORM "lock_issue"("issue_id_p");
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
      -- set voter count and mark issue as being calculated:
      UPDATE "issue" SET
        "state"  = 'calculation',
        "closed" = now(),
        "voter_count" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_voter" WHERE "issue_id" = "issue_id_p"
        )
        WHERE "id" = "issue_id_p";
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


-- "non_voter" deletes "direct_voter" and vice versa

CREATE FUNCTION "non_voter_deletes_direct_voter_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      DELETE FROM "direct_voter"
        WHERE "issue_id" = NEW."issue_id" AND "member_id" = NEW."member_id";
      RETURN NULL;
    END;
  $$;

CREATE TRIGGER "non_voter_deletes_direct_voter"
  AFTER INSERT OR UPDATE ON "non_voter"
  FOR EACH ROW EXECUTE PROCEDURE
  "non_voter_deletes_direct_voter_trigger"();

COMMENT ON FUNCTION "non_voter_deletes_direct_voter_trigger"()     IS 'Implementation of trigger "non_voter_deletes_direct_voter" on table "non_voter"';
COMMENT ON TRIGGER "non_voter_deletes_direct_voter" ON "non_voter" IS 'An entry in the "non_voter" table deletes an entry in the "direct_voter" table (and vice versa due to trigger "direct_voter_deletes_non_voter" on table "direct_voter")';

CREATE FUNCTION "direct_voter_deletes_non_voter_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      DELETE FROM "non_voter"
        WHERE "issue_id" = NEW."issue_id" AND "member_id" = NEW."member_id";
      RETURN NULL;
    END;
  $$;

CREATE TRIGGER "direct_voter_deletes_non_voter"
  AFTER INSERT OR UPDATE ON "direct_voter"
  FOR EACH ROW EXECUTE PROCEDURE
  "direct_voter_deletes_non_voter_trigger"();

COMMENT ON FUNCTION "direct_voter_deletes_non_voter_trigger"()        IS 'Implementation of trigger "direct_voter_deletes_non_voter" on table "direct_voter"';
COMMENT ON TRIGGER "direct_voter_deletes_non_voter" ON "direct_voter" IS 'An entry in the "direct_voter" table deletes an entry in the "non_voter" table (and vice versa due to trigger "non_voter_deletes_direct_voter" on table "non_voter")';


-- different locking levels and different locking order to avoid deadlocks

CREATE OR REPLACE FUNCTION "lock_issue"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      -- The following locking order is used:
      -- 1st) row-level lock on the issue
      -- 2nd) table-level locks in order of occurrence in the core.sql file
      PERFORM NULL FROM "issue" WHERE "id" = "issue_id_p" FOR UPDATE;
      -- NOTE: The row-level exclusive lock in combination with the
      -- share_row_lock_issue(_via_initiative)_trigger functions (which
      -- acquire a row-level share lock on the issue) ensure that no data
      -- is changed, which could affect calculation of snapshots or
      -- counting of votes. Table "delegation" must be table-level-locked,
      -- as it also contains issue- and global-scope delegations.
      PERFORM NULL FROM "member" WHERE "active" FOR SHARE;
      -- NOTE: As we later cause implicit row-level share locks on many
      -- active members, we lock them before locking any other table
      -- to avoid deadlocks
      LOCK TABLE "member"     IN SHARE MODE;
      LOCK TABLE "privilege"  IN SHARE MODE;
      LOCK TABLE "membership" IN SHARE MODE;
      LOCK TABLE "policy"     IN SHARE MODE;
      LOCK TABLE "delegation" IN SHARE MODE;
      LOCK TABLE "direct_population_snapshot"     IN EXCLUSIVE MODE;
      LOCK TABLE "delegating_population_snapshot" IN EXCLUSIVE MODE;
      LOCK TABLE "direct_interest_snapshot"       IN EXCLUSIVE MODE;
      LOCK TABLE "delegating_interest_snapshot"   IN EXCLUSIVE MODE;
      LOCK TABLE "direct_supporter_snapshot"      IN EXCLUSIVE MODE;
      RETURN;
    END;
  $$;


-- new comment on function "delete_private_data"()

COMMENT ON FUNCTION "delete_private_data"() IS 'Used by lf_export script. DO NOT USE on productive database, but only on a copy! This function deletes all data which should not be publicly available, and can be used to create a database dump for publication. See source code to see which data is deleted. If you need a different behaviour, copy this function and modify lf_export accordingly, to avoid data-leaks after updating.';


-- NOTE: The first version of the previous update script didn't
-- remove the "vote_ratio" function.
-- The function is therefore removed here as well, if existent.

DROP FUNCTION IF EXISTS "vote_ratio"
  ( "initiative"."positive_votes"%TYPE,
    "initiative"."negative_votes"%TYPE );


COMMIT;
