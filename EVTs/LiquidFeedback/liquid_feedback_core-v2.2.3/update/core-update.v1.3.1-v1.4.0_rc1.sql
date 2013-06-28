BEGIN;  -- NOTE: file contains additional statements AFTER this BEGIN/COMMIT block!


-- Update version information:

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.4.0_rc1', 1, 4, -1))
  AS "subquery"("string", "major", "minor", "revision");


-- New columns "notify_level" and "notify_event_id" in "member" table:

CREATE TYPE "notify_level" AS ENUM
  ('none', 'voting', 'verification', 'discussion', 'all');

COMMENT ON TYPE "notify_level" IS 'Level of notification: ''none'' = no notifications, ''voting'' = notifications about finished issues and issues in voting, ''verification'' = notifications about finished issues, issues in voting and verification phase, ''discussion'' = notifications about everything except issues in admission phase, ''all'' = notifications about everything';

ALTER TABLE "member" ADD "notify_level" "notify_level" NOT NULL DEFAULT 'none';
ALTER TABLE "member" ADD "notify_event_id" INT8;

COMMENT ON COLUMN "member"."notify_level"    IS 'Selects which event notifications are to be sent to the "notify_email" mail address';
COMMENT ON COLUMN "member"."notify_event_id" IS 'Latest "id" of an "event" the member was notified about';


-- Add primary key with type SERIAL8 (INT8) for "invite_code" table:

ALTER TABLE "invite_code" DROP CONSTRAINT "invite_code_pkey";
ALTER TABLE "invite_code" ALTER "code" SET NOT NULL;
ALTER TABLE "invite_code" ADD UNIQUE ("code");
ALTER TABLE "invite_code" ADD "id" SERIAL8 PRIMARY KEY;


-- Add index for "other_member_id" column of "contact" table:

CREATE INDEX "contact_other_member_id_idx" ON "contact" ("other_member_id");


-- New table "ignored_member":

CREATE TABLE "ignored_member" (
        PRIMARY KEY ("member_id", "other_member_id"),
        "member_id"             INT4            REFERENCES "member" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "other_member_id"       INT4            REFERENCES "member" ("id") ON DELETE CASCADE ON UPDATE CASCADE );
CREATE INDEX "ignored_member_other_member_id_idx" ON "ignored_member" ("other_member_id");

COMMENT ON TABLE "ignored_member" IS 'Possibility to filter other members';

COMMENT ON COLUMN "ignored_member"."member_id"       IS 'Member ignoring someone';
COMMENT ON COLUMN "ignored_member"."other_member_id" IS 'Member being ignored';


-- New table "unit" with default entry:

CREATE TABLE "unit" (
        "id"                    SERIAL4         PRIMARY KEY,
        "parent_id"             INT4            REFERENCES "unit" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "active"                BOOLEAN         NOT NULL DEFAULT TRUE,
        "name"                  TEXT            NOT NULL,
        "description"           TEXT            NOT NULL DEFAULT '',
        "member_count"          INT4,
        "text_search_data"      TSVECTOR );
CREATE INDEX "unit_root_idx" ON "unit" ("id") WHERE "parent_id" ISNULL;
CREATE INDEX "unit_parent_id_idx" ON "unit" ("parent_id");
CREATE INDEX "unit_active_idx" ON "unit" ("active");
CREATE INDEX "unit_text_search_data_idx" ON "unit" USING gin ("text_search_data");
CREATE TRIGGER "update_text_search_data"
  BEFORE INSERT OR UPDATE ON "unit"
  FOR EACH ROW EXECUTE PROCEDURE
  tsvector_update_trigger('text_search_data', 'pg_catalog.simple',
    "name", "description" );

COMMENT ON TABLE "unit" IS 'Organizational units organized as trees; Delegations are not inherited through these trees.';

COMMENT ON COLUMN "unit"."parent_id"    IS 'Parent id of tree node; Multiple roots allowed';
COMMENT ON COLUMN "unit"."active"       IS 'TRUE means new issues can be created in units of this area';
COMMENT ON COLUMN "unit"."member_count" IS 'Count of members as determined by column "voting_right" in table "privilege"';

INSERT INTO "unit" ("name") VALUES ('Main');  -- NOTE: gets id 1


-- New column "unit_id" in table "area":

ALTER TABLE "area" ADD "unit_id" INT4 DEFAULT 1
  NOT NULL REFERENCES "unit" ("id") ON DELETE CASCADE ON UPDATE CASCADE;
ALTER TABLE "area" ALTER "unit_id" DROP DEFAULT;

CREATE INDEX "area_unit_id_idx" ON "area" ("unit_id");


-- Issue states:

CREATE TYPE "issue_state" AS ENUM (
        'admission', 'discussion', 'verification', 'voting',
        'canceled_revoked_before_accepted',
        'canceled_issue_not_accepted',
        'canceled_after_revocation_during_discussion',
        'canceled_after_revocation_during_verification',
        'calculation',
        'canceled_no_initiative_admitted',
        'finished_without_winner', 'finished_with_winner');

COMMENT ON TYPE "issue_state" IS 'State of issues';

ALTER TABLE "issue" ADD "state" "issue_state" DEFAULT NULL;
ALTER TABLE "issue" ALTER "state" SET DEFAULT 'admission';

-- NOTE: Filling new column with values is done after this transaction (see below)


-- New column "revoked_by_member_id" in table "initiative":

ALTER TABLE "initiative" ADD "revoked_by_member_id" INT4 REFERENCES "member" ("id") ON DELETE RESTRICT ON UPDATE CASCADE;

COMMENT ON COLUMN "initiative"."revoked_by_member_id" IS 'Member, who decided to revoked the initiative';

-- NOTE: Filling new column with values is done after this transaction (see below)


-- New table "ignored_initiative":

CREATE TABLE "ignored_initiative" (
        PRIMARY KEY ("initiative_id", "member_id"),
        "initiative_id"         INT4            REFERENCES "initiative" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "member_id"             INT4            REFERENCES "member" ("id") ON DELETE CASCADE ON UPDATE CASCADE );
CREATE INDEX "ignored_initiative_member_id_idx" ON "ignored_initiative" ("member_id");

COMMENT ON TABLE "ignored_initiative" IS 'Possibility to filter initiatives';


-- New table "invite_code_unit":

CREATE TABLE "invite_code_unit" (
        PRIMARY KEY ("invite_code_id", "unit_id"),
        "invite_code_id"        INT8            REFERENCES "invite_code" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "unit_id"               INT4            REFERENCES "unit" ("id") ON DELETE CASCADE ON UPDATE CASCADE );

COMMENT ON TABLE "invite_code_unit" IS 'Units where accounts created with a given invite codes get voting rights';

INSERT INTO "invite_code_unit" ("invite_code_id", "unit_id")
  SELECT "id" AS "invite_code_id", 1 AS "unit_id" FROM "invite_code";


-- New table "privilege":

CREATE TABLE "privilege" (
        PRIMARY KEY ("unit_id", "member_id"),
        "unit_id"               INT4            REFERENCES "unit" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "member_id"             INT4            REFERENCES "member" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "admin_manager"         BOOLEAN         NOT NULL DEFAULT FALSE,
        "unit_manager"          BOOLEAN         NOT NULL DEFAULT FALSE,
        "area_manager"          BOOLEAN         NOT NULL DEFAULT FALSE,
        "voting_right_manager"  BOOLEAN         NOT NULL DEFAULT FALSE,
        "voting_right"          BOOLEAN         NOT NULL DEFAULT TRUE );

COMMENT ON TABLE "privilege" IS 'Members rights related to each unit';

COMMENT ON COLUMN "privilege"."admin_manager"        IS 'Grant/revoke admin privileges to/from other users';
COMMENT ON COLUMN "privilege"."unit_manager"         IS 'Create or lock sub units';
COMMENT ON COLUMN "privilege"."area_manager"         IS 'Create or lock areas and set area parameters';
COMMENT ON COLUMN "privilege"."voting_right_manager" IS 'Select which members are allowed to discuss and vote inside the unit';
COMMENT ON COLUMN "privilege"."voting_right"         IS 'Right to discuss and vote';

INSERT INTO "privilege" ("unit_id", "member_id", "voting_right")
  SELECT 1 AS "unit_id", "id" AS "member_id", TRUE AS "voting_right"
  FROM "member";


-- Remove table "ignored_issue", which is no longer existent:

DROP TABLE "ignored_issue";


-- Replace TYPE "delegation_scope" with a new type, where 'global' is replaced by 'unit':

ALTER TYPE "delegation_scope" RENAME TO "delegation_scope_old";  -- NOTE: dropped later
CREATE TYPE "delegation_scope" AS ENUM ('unit', 'area', 'issue');
COMMENT ON TYPE "delegation_scope" IS 'Scope for delegations: ''unit'', ''area'', or ''issue'' (order is relevant)';


-- Delete views and functions being dependent on type "delegation_scope":

DROP FUNCTION "delegation_chain"
  ( "member_id_p" "member"."id"%TYPE,
    "area_id_p"   "area"."id"%TYPE,
    "issue_id_p"  "issue"."id"%TYPE );

DROP FUNCTION "delegation_chain"
  ( "member_id_p"           "member"."id"%TYPE,
    "area_id_p"             "area"."id"%TYPE,
    "issue_id_p"            "issue"."id"%TYPE,
    "simulate_trustee_id_p" "member"."id"%TYPE );

DROP TYPE "delegation_chain_row";

DROP VIEW "issue_delegation";
DROP VIEW "area_delegation";
DROP VIEW "global_delegation";
DROP VIEW "active_delegation";


-- Modify "delegation" table to use new "delegation_scope" type:

ALTER TABLE "delegation" DROP CONSTRAINT "no_global_delegation_to_null";
ALTER TABLE "delegation" DROP CONSTRAINT "area_id_and_issue_id_set_according_to_scope";

DROP INDEX "delegation_global_truster_id_unique_idx";

ALTER TABLE "delegation" ALTER "scope" TYPE "delegation_scope"
  USING CASE WHEN "scope" = 'global'
  THEN 'unit'::"delegation_scope"
  ELSE "scope"::text::"delegation_scope" END;

ALTER TABLE "delegation" ADD "unit_id" INT4 REFERENCES "unit" ("id") ON DELETE CASCADE ON UPDATE CASCADE;

ALTER TABLE "delegation" ADD CONSTRAINT "no_unit_delegation_to_null"
  CHECK ("trustee_id" NOTNULL OR "scope" != 'unit');

ALTER TABLE "delegation" ADD UNIQUE ("unit_id", "truster_id");

COMMENT ON COLUMN "delegation"."unit_id"  IS 'Reference to unit, if delegation is unit-wide, otherwise NULL';

-- NOTE: Column "unit_id" filled after transaction (see below)


-- Modify snapshot tables to use new "delegation_scope" type:

ALTER TABLE "delegating_population_snapshot" ALTER "scope" TYPE "delegation_scope"
  USING CASE WHEN "scope" = 'global'
  THEN 'unit'::"delegation_scope"
  ELSE "scope"::text::"delegation_scope" END;

ALTER TABLE "delegating_interest_snapshot" ALTER "scope" TYPE "delegation_scope"
  USING CASE WHEN "scope" = 'global'
  THEN 'unit'::"delegation_scope"
  ELSE "scope"::text::"delegation_scope" END;

ALTER TABLE "delegating_voter" ALTER "scope" TYPE "delegation_scope"
  USING CASE WHEN "scope" = 'global'
  THEN 'unit'::"delegation_scope"
  ELSE "scope"::text::"delegation_scope" END;


-- New table "non_voter":

CREATE TABLE "non_voter" (
        PRIMARY KEY ("issue_id", "member_id"),
        "issue_id"              INT4            REFERENCES "issue" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "member_id"             INT4            REFERENCES "member" ("id") ON DELETE CASCADE ON UPDATE CASCADE );
CREATE INDEX "non_voter_member_id_idx" ON "non_voter" ("member_id");

COMMENT ON TABLE "non_voter" IS 'Members who decided to not vote directly on an issue';


-- New tables "issue_comment" and "rendered_issue_comment":

CREATE TABLE "issue_comment" (
        PRIMARY KEY ("issue_id", "member_id"),
        "issue_id"              INT4            REFERENCES "issue" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "member_id"             INT4            REFERENCES "member" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "changed"               TIMESTAMPTZ     NOT NULL DEFAULT now(),
        "formatting_engine"     TEXT,
        "content"               TEXT            NOT NULL,
        "text_search_data"      TSVECTOR );
CREATE INDEX "issue_comment_member_id_idx" ON "issue_comment" ("member_id");
CREATE INDEX "issue_comment_text_search_data_idx" ON "issue_comment" USING gin ("text_search_data");
CREATE TRIGGER "update_text_search_data"
  BEFORE INSERT OR UPDATE ON "issue_comment"
  FOR EACH ROW EXECUTE PROCEDURE
  tsvector_update_trigger('text_search_data', 'pg_catalog.simple', "content");

COMMENT ON TABLE "issue_comment" IS 'Place to store free comments of members related to issues';

COMMENT ON COLUMN "issue_comment"."changed" IS 'Time the comment was last changed';

CREATE TABLE "rendered_issue_comment" (
        PRIMARY KEY ("issue_id", "member_id", "format"),
        FOREIGN KEY ("issue_id", "member_id")
          REFERENCES "issue_comment" ("issue_id", "member_id")
          ON DELETE CASCADE ON UPDATE CASCADE,
        "issue_id"              INT4,
        "member_id"             INT4,
        "format"                TEXT,
        "content"               TEXT            NOT NULL );

COMMENT ON TABLE "rendered_issue_comment" IS 'This table may be used by frontends to cache "rendered" issue comments (e.g. HTML output generated from wiki text)';


-- New tables "voting_comment" and "rendered_voting_comment":

CREATE TABLE "voting_comment" (
        PRIMARY KEY ("issue_id", "member_id"),
        "issue_id"              INT4            REFERENCES "issue" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "member_id"             INT4            REFERENCES "member" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "changed"               TIMESTAMPTZ,
        "formatting_engine"     TEXT,
        "content"               TEXT            NOT NULL,
        "text_search_data"      TSVECTOR );
CREATE INDEX "voting_comment_member_id_idx" ON "voting_comment" ("member_id");
CREATE INDEX "voting_comment_text_search_data_idx" ON "voting_comment" USING gin ("text_search_data");
CREATE TRIGGER "update_text_search_data"
  BEFORE INSERT OR UPDATE ON "voting_comment"
  FOR EACH ROW EXECUTE PROCEDURE
  tsvector_update_trigger('text_search_data', 'pg_catalog.simple', "content");

COMMENT ON TABLE "voting_comment" IS 'Storage for comments of voters to be published after voting has finished.';

COMMENT ON COLUMN "voting_comment"."changed" IS 'Is to be set or updated by the frontend, if comment was inserted or updated AFTER the issue has been closed. Otherwise it shall be set to NULL.';

CREATE TABLE "rendered_voting_comment" (
        PRIMARY KEY ("issue_id", "member_id", "format"),
        FOREIGN KEY ("issue_id", "member_id")
          REFERENCES "voting_comment" ("issue_id", "member_id")
          ON DELETE CASCADE ON UPDATE CASCADE,
        "issue_id"              INT4,
        "member_id"             INT4,
        "format"                TEXT,
        "content"               TEXT            NOT NULL );

COMMENT ON TABLE "rendered_voting_comment" IS 'This table may be used by frontends to cache "rendered" voting comments (e.g. HTML output generated from wiki text)';


-- New table "event":

CREATE TYPE "event_type" AS ENUM (
        'issue_state_changed',
        'initiative_created_in_new_issue',
        'initiative_created_in_existing_issue',
        'initiative_revoked',
        'new_draft_created',
        'suggestion_created');

COMMENT ON TYPE "event_type" IS 'Type used for column "event" of table "event"';

CREATE TABLE "event" (
        "id"                    SERIAL8         PRIMARY KEY,
        "occurrence"            TIMESTAMPTZ     NOT NULL DEFAULT now(),
        "event"                 "event_type"    NOT NULL,
        "member_id"             INT4            REFERENCES "member" ("id") ON DELETE RESTRICT ON UPDATE CASCADE,
        "issue_id"              INT4            REFERENCES "issue" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "state"                 "issue_state"   CHECK ("state" != 'calculation'),
        "initiative_id"         INT4,
        "draft_id"              INT8,
        "suggestion_id"         INT8,
        FOREIGN KEY ("issue_id", "initiative_id")
          REFERENCES "initiative" ("issue_id", "id")
          ON DELETE CASCADE ON UPDATE CASCADE,
        FOREIGN KEY ("initiative_id", "draft_id")
          REFERENCES "draft" ("initiative_id", "id")
          ON DELETE CASCADE ON UPDATE CASCADE,
        FOREIGN KEY ("initiative_id", "suggestion_id")
          REFERENCES "suggestion" ("initiative_id", "id")
          ON DELETE CASCADE ON UPDATE CASCADE,
        CONSTRAINT "null_constraints_for_issue_state_changed" CHECK (
          "event" != 'issue_state_changed' OR (
            "member_id"     ISNULL  AND
            "issue_id"      NOTNULL AND
            "state"         NOTNULL AND
            "initiative_id" ISNULL  AND
            "draft_id"      ISNULL  AND
            "suggestion_id" ISNULL  )),
        CONSTRAINT "null_constraints_for_initiative_creation_or_revocation_or_new_draft" CHECK (
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
            "suggestion_id" ISNULL  )),
        CONSTRAINT "null_constraints_for_suggestion_creation" CHECK (
          "event" != 'suggestion_created' OR (
            "member_id"     NOTNULL AND
            "issue_id"      NOTNULL AND
            "state"         NOTNULL AND
            "initiative_id" NOTNULL AND
            "draft_id"      ISNULL  AND
            "suggestion_id" NOTNULL )) );

COMMENT ON TABLE "event" IS 'Event table, automatically filled by triggers';

COMMENT ON COLUMN "event"."occurrence" IS 'Point in time, when event occurred';
COMMENT ON COLUMN "event"."event"      IS 'Type of event (see TYPE "event_type")';
COMMENT ON COLUMN "event"."member_id"  IS 'Member who caused the event, if applicable';
COMMENT ON COLUMN "event"."state"      IS 'If issue_id is set: state of affected issue; If state changed: new state';


-- Triggers to fill "event" table:

CREATE FUNCTION "write_event_issue_state_changed_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF NEW."state" != OLD."state" AND NEW."state" != 'calculation' THEN
        INSERT INTO "event" ("event", "issue_id", "state")
          VALUES ('issue_state_changed', NEW."id", NEW."state");
      END IF;
      RETURN NULL;
    END;
  $$;

CREATE TRIGGER "write_event_issue_state_changed"
  AFTER UPDATE ON "issue" FOR EACH ROW EXECUTE PROCEDURE
  "write_event_issue_state_changed_trigger"();

COMMENT ON FUNCTION "write_event_issue_state_changed_trigger"() IS 'Implementation of trigger "write_event_issue_state_changed" on table "issue"';
COMMENT ON TRIGGER "write_event_issue_state_changed" ON "issue" IS 'Create entry in "event" table on "state" change';

CREATE FUNCTION "write_event_initiative_or_draft_created_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "initiative_row" "initiative"%ROWTYPE;
      "issue_row"      "issue"%ROWTYPE;
      "event_v"        "event_type";
    BEGIN
      SELECT * INTO "initiative_row" FROM "initiative"
        WHERE "id" = NEW."initiative_id";
      SELECT * INTO "issue_row" FROM "issue"
        WHERE "id" = "initiative_row"."issue_id";
      IF EXISTS (
        SELECT NULL FROM "draft"
        WHERE "initiative_id" = NEW."initiative_id"
        AND "id" != NEW."id"
      ) THEN
        "event_v" := 'new_draft_created';
      ELSE
        IF EXISTS (
          SELECT NULL FROM "initiative"
          WHERE "issue_id" = "initiative_row"."issue_id"
          AND "id" != "initiative_row"."id"
        ) THEN
          "event_v" := 'initiative_created_in_existing_issue';
        ELSE
          "event_v" := 'initiative_created_in_new_issue';
        END IF;
      END IF;
      INSERT INTO "event" (
          "event", "member_id",
          "issue_id", "state", "initiative_id", "draft_id"
        ) VALUES (
          "event_v",
          NEW."author_id",
          "initiative_row"."issue_id",
          "issue_row"."state",
          "initiative_row"."id",
          NEW."id" );
      RETURN NULL;
    END;
  $$;

CREATE TRIGGER "write_event_initiative_or_draft_created"
  AFTER INSERT ON "draft" FOR EACH ROW EXECUTE PROCEDURE
  "write_event_initiative_or_draft_created_trigger"();

COMMENT ON FUNCTION "write_event_initiative_or_draft_created_trigger"() IS 'Implementation of trigger "write_event_initiative_or_draft_created" on table "issue"';
COMMENT ON TRIGGER "write_event_initiative_or_draft_created" ON "draft" IS 'Create entry in "event" table on draft creation';

CREATE FUNCTION "write_event_initiative_revoked_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row"      "issue"%ROWTYPE;
    BEGIN
      SELECT * INTO "issue_row" FROM "issue"
        WHERE "id" = NEW."issue_id";
      IF OLD."revoked" ISNULL AND NEW."revoked" NOTNULL THEN
        INSERT INTO "event" (
            "event", "member_id", "issue_id", "state", "initiative_id"
          ) VALUES (
            'initiative_revoked',
            NEW."revoked_by_member_id",
            NEW."issue_id",
            "issue_row"."state",
            NEW."id" );
      END IF;
      RETURN NULL;
    END;
  $$;

CREATE TRIGGER "write_event_initiative_revoked"
  AFTER UPDATE ON "initiative" FOR EACH ROW EXECUTE PROCEDURE
  "write_event_initiative_revoked_trigger"();

COMMENT ON FUNCTION "write_event_initiative_revoked_trigger"()      IS 'Implementation of trigger "write_event_initiative_revoked" on table "issue"';
COMMENT ON TRIGGER "write_event_initiative_revoked" ON "initiative" IS 'Create entry in "event" table, when an initiative is revoked';

CREATE FUNCTION "write_event_suggestion_created_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "initiative_row" "initiative"%ROWTYPE;
      "issue_row"      "issue"%ROWTYPE;
    BEGIN
      SELECT * INTO "initiative_row" FROM "initiative"
        WHERE "id" = NEW."initiative_id";
      SELECT * INTO "issue_row" FROM "issue"
        WHERE "id" = "initiative_row"."issue_id";
      INSERT INTO "event" (
          "event", "member_id",
          "issue_id", "state", "initiative_id", "suggestion_id"
        ) VALUES (
          'suggestion_created',
          NEW."author_id",
          "initiative_row"."issue_id",
          "issue_row"."state",
          "initiative_row"."id",
          NEW."id" );
      RETURN NULL;
    END;
  $$;

CREATE TRIGGER "write_event_suggestion_created"
  AFTER INSERT ON "suggestion" FOR EACH ROW EXECUTE PROCEDURE
  "write_event_suggestion_created_trigger"();

COMMENT ON FUNCTION "write_event_suggestion_created_trigger"()      IS 'Implementation of trigger "write_event_suggestion_created" on table "issue"';
COMMENT ON TRIGGER "write_event_suggestion_created" ON "suggestion" IS 'Create entry in "event" table on suggestion creation';


-- Modified views:

CREATE VIEW "unit_delegation" AS
  SELECT
    "unit"."id" AS "unit_id",
    "delegation"."id",
    "delegation"."truster_id",
    "delegation"."trustee_id",
    "delegation"."scope"
  FROM "unit"
  JOIN "delegation"
    ON "delegation"."unit_id" = "unit"."id"
  JOIN "member"
    ON "delegation"."truster_id" = "member"."id"
  JOIN "privilege"
    ON "delegation"."unit_id" = "privilege"."unit_id"
    AND "delegation"."truster_id" = "privilege"."member_id"
  WHERE "member"."active" AND "privilege"."voting_right";

COMMENT ON VIEW "unit_delegation" IS 'Unit delegations where trusters are active and have voting right';

CREATE VIEW "area_delegation" AS
  SELECT DISTINCT ON ("area"."id", "delegation"."truster_id")
    "area"."id" AS "area_id",
    "delegation"."id",
    "delegation"."truster_id",
    "delegation"."trustee_id",
    "delegation"."scope"
  FROM "area"
  JOIN "delegation"
    ON "delegation"."unit_id" = "area"."unit_id"
    OR "delegation"."area_id" = "area"."id"
  JOIN "member"
    ON "delegation"."truster_id" = "member"."id"
  JOIN "privilege"
    ON "area"."unit_id" = "privilege"."unit_id"
    AND "delegation"."truster_id" = "privilege"."member_id"
  WHERE "member"."active" AND "privilege"."voting_right"
  ORDER BY
    "area"."id",
    "delegation"."truster_id",
    "delegation"."scope" DESC;

COMMENT ON VIEW "area_delegation" IS 'Area delegations where trusters are active and have voting right';

CREATE VIEW "issue_delegation" AS
  SELECT DISTINCT ON ("issue"."id", "delegation"."truster_id")
    "issue"."id" AS "issue_id",
    "delegation"."id",
    "delegation"."truster_id",
    "delegation"."trustee_id",
    "delegation"."scope"
  FROM "issue"
  JOIN "area"
    ON "area"."id" = "issue"."area_id"
  JOIN "delegation"
    ON "delegation"."unit_id" = "area"."unit_id"
    OR "delegation"."area_id" = "area"."id"
    OR "delegation"."issue_id" = "issue"."id"
  JOIN "member"
    ON "delegation"."truster_id" = "member"."id"
  JOIN "privilege"
    ON "area"."unit_id" = "privilege"."unit_id"
    AND "delegation"."truster_id" = "privilege"."member_id"
  WHERE "member"."active" AND "privilege"."voting_right"
  ORDER BY
    "issue"."id",
    "delegation"."truster_id",
    "delegation"."scope" DESC;

COMMENT ON VIEW "issue_delegation" IS 'Issue delegations where trusters are active and have voting right';

CREATE VIEW "unit_member_count" AS
  SELECT
    "unit"."id" AS "unit_id",
    sum("member"."id") AS "member_count"
  FROM "unit"
  LEFT JOIN "privilege"
  ON "privilege"."unit_id" = "unit"."id" 
  AND "privilege"."voting_right"
  LEFT JOIN "member"
  ON "member"."id" = "privilege"."member_id"
  AND "member"."active"
  GROUP BY "unit"."id";

COMMENT ON VIEW "unit_member_count" IS 'View used to update "member_count" column of "unit" table';

DROP VIEW "area_member_count";
CREATE VIEW "area_member_count" AS
  SELECT
    "area"."id" AS "area_id",
    count("member"."id") AS "direct_member_count",
    coalesce(
      sum(
        CASE WHEN "member"."id" NOTNULL THEN
          "membership_weight"("area"."id", "member"."id")
        ELSE 0 END
      )
    ) AS "member_weight",
    coalesce(
      sum(
        CASE WHEN "member"."id" NOTNULL AND "membership"."autoreject" THEN
          "membership_weight"("area"."id", "member"."id")
        ELSE 0 END
      )
    ) AS "autoreject_weight"
  FROM "area"
  LEFT JOIN "membership"
  ON "area"."id" = "membership"."area_id"
  LEFT JOIN "privilege"
  ON "privilege"."unit_id" = "area"."unit_id"
  AND "privilege"."member_id" = "membership"."member_id"
  AND "privilege"."voting_right"
  LEFT JOIN "member"
  ON "member"."id" = "privilege"."member_id"  -- NOTE: no membership here!
  AND "member"."active"
  GROUP BY "area"."id";

COMMENT ON VIEW "area_member_count" IS 'View used to update "direct_member_count", "member_weight" and "autoreject_weight" columns of table "area"';


-- New view "event_seen_by_member":

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

COMMENT ON VIEW "event_seen_by_member" IS 'Events as seen by a member, depending on its memberships, interests and support';


-- New view "pending_notification":

CREATE VIEW "pending_notification" AS
  SELECT
    "member"."id" AS "seen_by_member_id",
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
    "member"."notify_event_id" ISNULL OR
    ( "member"."notify_event_id" NOTNULL AND
      "member"."notify_event_id" < "event"."id" ) )
  AND (
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

COMMENT ON VIEW "pending_notification" IS 'Events to be sent to "notify_email" address of member referred to by "seen_by_member_id"';


COMMENT ON TYPE "timeline_event" IS 'Types of event in timeline tables (DEPRECATED)';
COMMENT ON VIEW "timeline_issue" IS 'Helper view for "timeline" view (DEPRECATED)';
COMMENT ON VIEW "timeline_initiative" IS 'Helper view for "timeline" view (DEPRECATED)';
COMMENT ON VIEW "timeline_draft" IS 'Helper view for "timeline" view (DEPRECATED)';
COMMENT ON VIEW "timeline_suggestion" IS 'Helper view for "timeline" view (DEPRECATED)';
COMMENT ON VIEW "timeline" IS 'Aggregation of different events in the system (DEPRECATED)';


-- Modified "delegation_chain" functions:

CREATE TYPE "delegation_chain_row" AS (
        "index"                 INT4,
        "member_id"             INT4,
        "member_valid"          BOOLEAN,
        "participation"         BOOLEAN,
        "overridden"            BOOLEAN,
        "scope_in"              "delegation_scope",
        "scope_out"             "delegation_scope",
        "disabled_out"          BOOLEAN,
        "loop"                  "delegation_chain_loop_tag" );

COMMENT ON TYPE "delegation_chain_row" IS 'Type of rows returned by "delegation_chain"(...) functions';

COMMENT ON COLUMN "delegation_chain_row"."index"         IS 'Index starting with 0 and counting up';
COMMENT ON COLUMN "delegation_chain_row"."participation" IS 'In case of delegation chains for issues: interest, for areas: membership, for global delegation chains: always null';
COMMENT ON COLUMN "delegation_chain_row"."overridden"    IS 'True, if an entry with lower index has "participation" set to true';
COMMENT ON COLUMN "delegation_chain_row"."scope_in"      IS 'Scope of used incoming delegation';
COMMENT ON COLUMN "delegation_chain_row"."scope_out"     IS 'Scope of used outgoing delegation';
COMMENT ON COLUMN "delegation_chain_row"."disabled_out"  IS 'Outgoing delegation is explicitly disabled by a delegation with trustee_id set to NULL';
COMMENT ON COLUMN "delegation_chain_row"."loop"          IS 'Not null, if member is part of a loop, see "delegation_chain_loop_tag" type';


CREATE FUNCTION "delegation_chain"
  ( "member_id_p"           "member"."id"%TYPE,
    "unit_id_p"             "unit"."id"%TYPE,
    "area_id_p"             "area"."id"%TYPE,
    "issue_id_p"            "issue"."id"%TYPE,
    "simulate_trustee_id_p" "member"."id"%TYPE )
  RETURNS SETOF "delegation_chain_row"
  LANGUAGE 'plpgsql' STABLE AS $$
    DECLARE
      "scope_v"            "delegation_scope";
      "unit_id_v"          "unit"."id"%TYPE;
      "area_id_v"          "area"."id"%TYPE;
      "visited_member_ids" INT4[];  -- "member"."id"%TYPE[]
      "loop_member_id_v"   "member"."id"%TYPE;
      "output_row"         "delegation_chain_row";
      "output_rows"        "delegation_chain_row"[];
      "delegation_row"     "delegation"%ROWTYPE;
      "row_count"          INT4;
      "i"                  INT4;
      "loop_v"             BOOLEAN;
    BEGIN
      IF
        "unit_id_p" NOTNULL AND
        "area_id_p" ISNULL AND
        "issue_id_p" ISNULL
      THEN
        "scope_v" := 'unit';
        "unit_id_v" := "unit_id_p";
      ELSIF
        "unit_id_p" ISNULL AND
        "area_id_p" NOTNULL AND
        "issue_id_p" ISNULL
      THEN
        "scope_v" := 'area';
        "area_id_v" := "area_id_p";
        SELECT "unit_id" INTO "unit_id_v"
          FROM "area" WHERE "id" = "area_id_v";
      ELSIF
        "unit_id_p" ISNULL AND
        "area_id_p" ISNULL AND
        "issue_id_p" NOTNULL
      THEN
        "scope_v" := 'issue';
        SELECT "area_id" INTO "area_id_v"
          FROM "issue" WHERE "id" = "issue_id_p";
        SELECT "unit_id" INTO "unit_id_v"
          FROM "area"  WHERE "id" = "area_id_v";
      ELSE
        RAISE EXCEPTION 'Exactly one of unit_id_p, area_id_p, or issue_id_p must be NOTNULL.';
      END IF;
      "visited_member_ids" := '{}';
      "loop_member_id_v"   := NULL;
      "output_rows"        := '{}';
      "output_row"."index"         := 0;
      "output_row"."member_id"     := "member_id_p";
      "output_row"."member_valid"  := TRUE;
      "output_row"."participation" := FALSE;
      "output_row"."overridden"    := FALSE;
      "output_row"."disabled_out"  := FALSE;
      "output_row"."scope_out"     := NULL;
      LOOP
        IF "visited_member_ids" @> ARRAY["output_row"."member_id"] THEN
          "loop_member_id_v" := "output_row"."member_id";
        ELSE
          "visited_member_ids" :=
            "visited_member_ids" || "output_row"."member_id";
        END IF;
        IF "output_row"."participation" THEN
          "output_row"."overridden" := TRUE;
        END IF;
        "output_row"."scope_in" := "output_row"."scope_out";
        IF EXISTS (
          SELECT NULL FROM "member" JOIN "privilege"
          ON "privilege"."member_id" = "member"."id"
          AND "privilege"."unit_id" = "unit_id_v"
          WHERE "id" = "output_row"."member_id"
          AND "member"."active" AND "privilege"."voting_right"
        ) THEN
          IF "scope_v" = 'unit' THEN
            SELECT * INTO "delegation_row" FROM "delegation"
              WHERE "truster_id" = "output_row"."member_id"
              AND "unit_id" = "unit_id_v";
          ELSIF "scope_v" = 'area' THEN
            "output_row"."participation" := EXISTS (
              SELECT NULL FROM "membership"
              WHERE "area_id" = "area_id_p"
              AND "member_id" = "output_row"."member_id"
            );
            SELECT * INTO "delegation_row" FROM "delegation"
              WHERE "truster_id" = "output_row"."member_id"
              AND (
                "unit_id" = "unit_id_v" OR
                "area_id" = "area_id_v"
              )
              ORDER BY "scope" DESC;
          ELSIF "scope_v" = 'issue' THEN
            "output_row"."participation" := EXISTS (
              SELECT NULL FROM "interest"
              WHERE "issue_id" = "issue_id_p"
              AND "member_id" = "output_row"."member_id"
            );
            SELECT * INTO "delegation_row" FROM "delegation"
              WHERE "truster_id" = "output_row"."member_id"
              AND (
                "unit_id" = "unit_id_v" OR
                "area_id" = "area_id_v" OR
                "issue_id" = "issue_id_p"
              )
              ORDER BY "scope" DESC;
          END IF;
        ELSE
          "output_row"."member_valid"  := FALSE;
          "output_row"."participation" := FALSE;
          "output_row"."scope_out"     := NULL;
          "delegation_row" := ROW(NULL);
        END IF;
        IF
          "output_row"."member_id" = "member_id_p" AND
          "simulate_trustee_id_p" NOTNULL
        THEN
          "output_row"."scope_out" := "scope_v";
          "output_rows" := "output_rows" || "output_row";
          "output_row"."member_id" := "simulate_trustee_id_p";
        ELSIF "delegation_row"."trustee_id" NOTNULL THEN
          "output_row"."scope_out" := "delegation_row"."scope";
          "output_rows" := "output_rows" || "output_row";
          "output_row"."member_id" := "delegation_row"."trustee_id";
        ELSIF "delegation_row"."scope" NOTNULL THEN
          "output_row"."scope_out" := "delegation_row"."scope";
          "output_row"."disabled_out" := TRUE;
          "output_rows" := "output_rows" || "output_row";
          EXIT;
        ELSE
          "output_row"."scope_out" := NULL;
          "output_rows" := "output_rows" || "output_row";
          EXIT;
        END IF;
        EXIT WHEN "loop_member_id_v" NOTNULL;
        "output_row"."index" := "output_row"."index" + 1;
      END LOOP;
      "row_count" := array_upper("output_rows", 1);
      "i"      := 1;
      "loop_v" := FALSE;
      LOOP
        "output_row" := "output_rows"["i"];
        EXIT WHEN "output_row" ISNULL;  -- NOTE: ISNULL and NOT ... NOTNULL produce different results!
        IF "loop_v" THEN
          IF "i" + 1 = "row_count" THEN
            "output_row"."loop" := 'last';
          ELSIF "i" = "row_count" THEN
            "output_row"."loop" := 'repetition';
          ELSE
            "output_row"."loop" := 'intermediate';
          END IF;
        ELSIF "output_row"."member_id" = "loop_member_id_v" THEN
          "output_row"."loop" := 'first';
          "loop_v" := TRUE;
        END IF;
        IF "scope_v" = 'unit' THEN
          "output_row"."participation" := NULL;
        END IF;
        RETURN NEXT "output_row";
        "i" := "i" + 1;
      END LOOP;
      RETURN;
    END;
  $$;

COMMENT ON FUNCTION "delegation_chain"
  ( "member"."id"%TYPE,
    "unit"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE,
    "member"."id"%TYPE )
  IS 'Helper function for frontends to display delegation chains; Not part of internal voting logic';


CREATE FUNCTION "delegation_chain"
  ( "member_id_p" "member"."id"%TYPE,
    "unit_id_p"   "unit"."id"%TYPE,
    "area_id_p"   "area"."id"%TYPE,
    "issue_id_p"  "issue"."id"%TYPE )
  RETURNS SETOF "delegation_chain_row"
  LANGUAGE 'plpgsql' STABLE AS $$
    DECLARE
      "result_row" "delegation_chain_row";
    BEGIN
      FOR "result_row" IN
        SELECT * FROM "delegation_chain"(
          "member_id_p", "unit_id_p", "area_id_p", "issue_id_p", NULL
        )
      LOOP
        RETURN NEXT "result_row";
      END LOOP;
      RETURN;
    END;
  $$;

COMMENT ON FUNCTION "delegation_chain"
  ( "member"."id"%TYPE,
    "unit"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE )
  IS 'Shortcut for "delegation_chain"(...) function where 4th parameter is null';


-- Other modified functions:

CREATE OR REPLACE FUNCTION "lock_issue"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      LOCK TABLE "member"     IN SHARE MODE;
      LOCK TABLE "privilege"  IN SHARE MODE;
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

CREATE OR REPLACE FUNCTION "calculate_member_counts"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      LOCK TABLE "member"       IN SHARE MODE;
      LOCK TABLE "member_count" IN EXCLUSIVE MODE;
      LOCK TABLE "unit"         IN EXCLUSIVE MODE;
      LOCK TABLE "area"         IN EXCLUSIVE MODE;
      LOCK TABLE "privilege"    IN SHARE MODE;
      LOCK TABLE "membership"   IN SHARE MODE;
      DELETE FROM "member_count";
      INSERT INTO "member_count" ("total_count")
        SELECT "total_count" FROM "member_count_view";
      UPDATE "unit" SET "member_count" = "view"."member_count"
        FROM "unit_member_count" AS "view"
        WHERE "view"."unit_id" = "unit"."id";
      UPDATE "area" SET
        "direct_member_count" = "view"."direct_member_count",
        "member_weight"       = "view"."member_weight",
        "autoreject_weight"   = "view"."autoreject_weight"
        FROM "area_member_count" AS "view"
        WHERE "view"."area_id" = "area"."id";
      RETURN;
    END;
  $$;

CREATE OR REPLACE FUNCTION "create_population_snapshot"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "member_id_v" "member"."id"%TYPE;
    BEGIN
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

CREATE OR REPLACE FUNCTION "create_interest_snapshot"
  ( "issue_id_p" "issue"."id"%TYPE )
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      DELETE FROM "direct_interest_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic';
      DELETE FROM "delegating_interest_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic';
      DELETE FROM "direct_supporter_snapshot"
        WHERE "issue_id" = "issue_id_p"
        AND "event" = 'periodic';
      INSERT INTO "direct_interest_snapshot"
        ("issue_id", "event", "member_id", "voting_requested")
        SELECT
          "issue_id_p"  AS "issue_id",
          'periodic'    AS "event",
          "member"."id" AS "member_id",
          "interest"."voting_requested"
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
          "informed", "satisfied" )
        SELECT
          "issue_id_p"            AS "issue_id",
          "initiative"."id"       AS "initiative_id",
          'periodic'              AS "event",
          "supporter"."member_id" AS "member_id",
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
          "initiative_row"."satisfied_supporter_count" > 0 AND
          "initiative_row"."satisfied_supporter_count" *
          "policy_row"."initiative_quorum_den" >=
          "issue_row"."population" * "policy_row"."initiative_quorum_num"
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

CREATE OR REPLACE FUNCTION "close_voting"("issue_id_p" "issue"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "area_id_v"   "area"."id"%TYPE;
      "unit_id_v"   "unit"."id"%TYPE;
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "lock_issue"("issue_id_p");
      SELECT "id" INTO "area_id_v" FROM "issue" WHERE "id" = "issue_id_p";
      SELECT "id" INTO "unit_id_v" FROM "area"  WHERE "id" = "area_id_v";
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
          LEFT JOIN "direct_voter"
            ON "interest"."member_id" = "direct_voter"."member_id"
            AND "interest"."issue_id" = "direct_voter"."issue_id"
          LEFT JOIN "delegating_voter"
            ON "interest"."member_id" = "delegating_voter"."member_id"
            AND "interest"."issue_id" = "delegating_voter"."issue_id"
          WHERE "interest"."issue_id" = "issue_id_p"
          AND "interest"."autoreject" = TRUE
          AND "member"."active"
          AND "direct_voter"."member_id" ISNULL
          AND "delegating_voter"."member_id" ISNULL
        UNION SELECT "membership"."member_id"
          FROM "membership"
          JOIN "member"
            ON "membership"."member_id" = "member"."id"
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

CREATE OR REPLACE FUNCTION "calculate_ranks"("issue_id_p" "issue"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "dimension_v"     INTEGER;
      "vote_matrix"     INT4[][];  -- absolute votes
      "matrix"          INT8[][];  -- defeat strength / best paths
      "i"               INTEGER;
      "j"               INTEGER;
      "k"               INTEGER;
      "battle_row"      "battle"%ROWTYPE;
      "rank_ary"        INT4[];
      "rank_v"          INT4;
      "done_v"          INTEGER;
      "winners_ary"     INTEGER[];
      "initiative_id_v" "initiative"."id"%TYPE;
    BEGIN
      PERFORM NULL FROM "issue" WHERE "id" = "issue_id_p" FOR UPDATE;
      SELECT count(1) INTO "dimension_v" FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "agreed";
      IF "dimension_v" = 1 THEN
        UPDATE "initiative" SET "rank" = 1
          WHERE "issue_id" = "issue_id_p" AND "agreed";
      ELSIF "dimension_v" > 1 THEN
        -- Create "vote_matrix" with absolute number of votes in pairwise
        -- comparison:
        "vote_matrix" := "square_matrix_init_string"("dimension_v");  -- TODO: replace by "array_fill" function (PostgreSQL 8.4)
        "i" := 1;
        "j" := 2;
        FOR "battle_row" IN
          SELECT * FROM "battle" WHERE "issue_id" = "issue_id_p"
          ORDER BY "winning_initiative_id", "losing_initiative_id"
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
        "matrix" := "square_matrix_init_string"("dimension_v");  -- TODO: replace by "array_fill" function (PostgreSQL 8.4)
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
        "rank_ary" := "array_init_string"("dimension_v");  -- TODO: replace by "array_fill" function (PostgreSQL 8.4)
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
        -- write preliminary ranks:
        "i" := 1;
        FOR "initiative_id_v" IN
          SELECT "id" FROM "initiative"
          WHERE "issue_id" = "issue_id_p" AND "agreed"
          ORDER BY "id"
        LOOP
          UPDATE "initiative" SET "rank" = "rank_ary"["i"]
            WHERE "id" = "initiative_id_v";
          "i" := "i" + 1;
        END LOOP;
        IF "i" != "dimension_v" + 1 THEN
          RAISE EXCEPTION 'Wrong winner count (should not happen)';
        END IF;
        -- straighten ranks (start counting with 1, no equal ranks):
        "rank_v" := 1;
        FOR "initiative_id_v" IN
          SELECT "id" FROM "initiative"
          WHERE "issue_id" = "issue_id_p" AND "rank" NOTNULL
          ORDER BY
            "rank",
            "vote_ratio"("positive_votes", "negative_votes") DESC,
            "id"
        LOOP
          UPDATE "initiative" SET "rank" = "rank_v"
            WHERE "id" = "initiative_id_v";
          "rank_v" := "rank_v" + 1;
        END LOOP;
      END IF;
      -- mark issue as finished
      UPDATE "issue" SET
        "state" =
          CASE WHEN "dimension_v" = 0 THEN
            'finished_without_winner'::"issue_state"
          ELSE
            'finished_with_winner'::"issue_state"
          END,
        "ranks_available" = TRUE
        WHERE "id" = "issue_id_p";
      RETURN;
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
            -- NOTE: "issue_row" used later
            "issue_row"."state" := 'discussion';
            "issue_row"."accepted" := now();
            UPDATE "issue" SET
              "state"    = "issue_row"."state",
              "accepted" = "issue_row"."accepted"
              WHERE "id" = "issue_row"."id";
          ELSIF
            now() >= "issue_row"."created" + "issue_row"."admission_time"
          THEN
            -- close issues, if admission time has expired
            PERFORM "set_snapshot_event"("issue_id_p", 'end_of_admission');
            UPDATE "issue" SET
              "state" = 'canceled_issue_not_accepted',
              "closed" = now()
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
            -- NOTE: "issue_row" used later
            "issue_row"."state" := 'verification';
            "issue_row"."half_frozen" := now();
            UPDATE "issue" SET
              "state"       = "issue_row"."state",
              "half_frozen" = "issue_row"."half_frozen"
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
            -- and issue has not been accepted yet
            "issue_row"."accepted" ISNULL OR
            NOT EXISTS (
              -- or no initiatives have been revoked lately
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
          -- NOTE: "issue_row" used later
          IF "issue_row"."accepted" ISNULL THEN
            "issue_row"."state" := 'canceled_revoked_before_accepted';
          ELSIF "issue_row"."half_frozen" ISNULL THEN
            "issue_row"."state" := 'canceled_after_revocation_during_discussion';
          ELSE
            "issue_row"."state" := 'canceled_after_revocation_during_verification';
          END IF;
          "issue_row"."closed" := now();
          UPDATE "issue" SET
            "state"  = "issue_row"."state",
            "closed" = "issue_row"."closed"
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
          -- calculate ranks will not consume much time and can be done now
          PERFORM "calculate_ranks"("issue_id_p");
        END IF;
      END IF;
      RETURN;
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
        DELETE FROM "non_voter"
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
            -- NOTE: "issue_row" used later
            "issue_row"."state" := 'discussion';
            "issue_row"."accepted" := now();
            UPDATE "issue" SET
              "state"    = "issue_row"."state",
              "accepted" = "issue_row"."accepted"
              WHERE "id" = "issue_row"."id";
          ELSIF
            now() >= "issue_row"."created" + "issue_row"."admission_time"
          THEN
            -- close issues, if admission time has expired
            PERFORM "set_snapshot_event"("issue_id_p", 'end_of_admission');
            UPDATE "issue" SET
              "state" = 'canceled_issue_not_accepted',
              "closed" = now()
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
            -- NOTE: "issue_row" used later
            "issue_row"."state" := 'verification';
            "issue_row"."half_frozen" := now();
            UPDATE "issue" SET
              "state"       = "issue_row"."state",
              "half_frozen" = "issue_row"."half_frozen"
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
            -- and issue has not been accepted yet
            "issue_row"."accepted" ISNULL OR
            NOT EXISTS (
              -- or no initiatives have been revoked lately
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
          -- NOTE: "issue_row" used later
          IF "issue_row"."accepted" ISNULL THEN
            "issue_row"."state" := 'canceled_revoked_before_accepted';
          ELSIF "issue_row"."half_frozen" ISNULL THEN
            "issue_row"."state" := 'canceled_after_revocation_during_discussion';
          ELSE
            "issue_row"."state" := 'canceled_after_revocation_during_verification';
          END IF;
          "issue_row"."closed" := now();
          UPDATE "issue" SET
            "state"  = "issue_row"."state",
            "closed" = "issue_row"."closed"
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
          -- calculate ranks will not consume much time and can be done now
          PERFORM "calculate_ranks"("issue_id_p");
        END IF;
      END IF;
      RETURN;
    END;
  $$;

CREATE OR REPLACE FUNCTION "delete_private_data"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      UPDATE "member" SET
        "last_login"                   = NULL,
        "login"                        = NULL,
        "password"                     = NULL,
        "notify_email"                 = NULL,
        "notify_email_unconfirmed"     = NULL,
        "notify_email_secret"          = NULL,
        "notify_email_secret_expiry"   = NULL,
        "notify_email_lock_expiry"     = NULL,
        "password_reset_secret"        = NULL,
        "password_reset_secret_expiry" = NULL,
        "organizational_unit"          = NULL,
        "internal_posts"               = NULL,
        "realname"                     = NULL,
        "birthday"                     = NULL,
        "address"                      = NULL,
        "email"                        = NULL,
        "xmpp_address"                 = NULL,
        "website"                      = NULL,
        "phone"                        = NULL,
        "mobile_phone"                 = NULL,
        "profession"                   = NULL,
        "external_memberships"         = NULL,
        "external_posts"               = NULL,
        "statement"                    = NULL;
      -- "text_search_data" is updated by triggers
      DELETE FROM "invite_code";
      DELETE FROM "setting";
      DELETE FROM "setting_map";
      DELETE FROM "member_relation_setting";
      DELETE FROM "member_image";
      DELETE FROM "contact";
      DELETE FROM "ignored_member";
      DELETE FROM "session";
      DELETE FROM "area_setting";
      DELETE FROM "issue_setting";
      DELETE FROM "ignored_initiative";
      DELETE FROM "initiative_setting";
      DELETE FROM "suggestion_setting";
      DELETE FROM "non_voter";
      DELETE FROM "direct_voter" USING "issue"
        WHERE "direct_voter"."issue_id" = "issue"."id"
        AND "issue"."closed" ISNULL;
      RETURN;
    END;
  $$;


-- Delete old "delegation_scope" TYPE:

DROP TYPE "delegation_scope_old";


COMMIT;


-- Generate issue states and add constraints:

UPDATE "issue" SET "state" =
  CASE
  WHEN "closed" ISNULL THEN
    CASE
    WHEN "accepted" ISNULL THEN
      'admission'::"issue_state"
    WHEN "half_frozen" ISNULL THEN
      'discussion'::"issue_state"
    WHEN "fully_frozen" ISNULL THEN
      'verification'::"issue_state"
    ELSE
      'voting'::"issue_state"
    END
  WHEN "fully_frozen" NOTNULL THEN
    CASE
    WHEN "fully_frozen" = "closed" THEN
      'canceled_no_initiative_admitted'::"issue_state"
    ELSE
      'finished_without_winner'::"issue_state"  -- NOTE: corrected later
    END
  WHEN "half_frozen" NOTNULL THEN
    'canceled_after_revocation_during_verification'::"issue_state"
  WHEN "accepted" NOTNULL THEN
    'canceled_after_revocation_during_discussion'::"issue_state"
  ELSE
    'canceled_revoked_before_accepted'::"issue_state"  -- NOTE: corrected later
  END;
UPDATE "issue" SET "state" = 'finished_with_winner'
  FROM "initiative"
  WHERE "issue"."id" = "initiative"."issue_id"
  AND "issue"."state" = 'finished_without_winner'
  AND "initiative"."agreed";
UPDATE "issue" SET "state" = 'canceled_issue_not_accepted'
  FROM "initiative"
  WHERE "issue"."id" = "initiative"."issue_id"
  AND "issue"."state" = 'canceled_revoked_before_accepted'
  AND "initiative"."revoked" ISNULL;

ALTER TABLE "issue" ALTER "state" SET NOT NULL;

ALTER TABLE "issue" DROP CONSTRAINT "valid_state";
ALTER TABLE "issue" ADD CONSTRAINT "valid_state" CHECK ((
    ("accepted" ISNULL  AND "half_frozen" ISNULL  AND "fully_frozen" ISNULL  AND "closed" ISNULL  AND "ranks_available" = FALSE) OR
    ("accepted" ISNULL  AND "half_frozen" ISNULL  AND "fully_frozen" ISNULL  AND "closed" NOTNULL AND "ranks_available" = FALSE) OR
    ("accepted" NOTNULL AND "half_frozen" ISNULL  AND "fully_frozen" ISNULL  AND "closed" ISNULL  AND "ranks_available" = FALSE) OR
    ("accepted" NOTNULL AND "half_frozen" ISNULL  AND "fully_frozen" ISNULL  AND "closed" NOTNULL AND "ranks_available" = FALSE) OR
    ("accepted" NOTNULL AND "half_frozen" NOTNULL AND "fully_frozen" ISNULL  AND "closed" ISNULL  AND "ranks_available" = FALSE) OR
    ("accepted" NOTNULL AND "half_frozen" NOTNULL AND "fully_frozen" ISNULL  AND "closed" NOTNULL AND "ranks_available" = FALSE) OR
    ("accepted" NOTNULL AND "half_frozen" NOTNULL AND "fully_frozen" NOTNULL AND "closed" ISNULL  AND "ranks_available" = FALSE) OR
    ("accepted" NOTNULL AND "half_frozen" NOTNULL AND "fully_frozen" NOTNULL AND "closed" NOTNULL AND "ranks_available" = FALSE) OR
    ("accepted" NOTNULL AND "half_frozen" NOTNULL AND "fully_frozen" NOTNULL AND "closed" NOTNULL AND "ranks_available" = TRUE)
  ) AND (
    ("state" = 'admission'    AND "closed" ISNULL AND "accepted" ISNULL) OR
    ("state" = 'discussion'   AND "closed" ISNULL AND "accepted" NOTNULL AND "half_frozen" ISNULL) OR
    ("state" = 'verification' AND "closed" ISNULL AND "half_frozen" NOTNULL AND "fully_frozen" ISNULL) OR
    ("state" = 'voting'       AND "closed" ISNULL AND "fully_frozen" NOTNULL) OR
    ("state" = 'canceled_revoked_before_accepted'              AND "closed" NOTNULL AND "accepted" ISNULL) OR
    ("state" = 'canceled_issue_not_accepted'                   AND "closed" NOTNULL AND "accepted" ISNULL) OR
    ("state" = 'canceled_after_revocation_during_discussion'   AND "closed" NOTNULL AND "half_frozen"  ISNULL) OR
    ("state" = 'canceled_after_revocation_during_verification' AND "closed" NOTNULL AND "fully_frozen" ISNULL) OR
    ("state" = 'calculation'                     AND "closed" NOTNULL AND "fully_frozen" NOTNULL AND "ranks_available" = FALSE) OR
    ("state" = 'canceled_no_initiative_admitted' AND "closed" NOTNULL AND "fully_frozen" NOTNULL AND "ranks_available" = TRUE) OR
    ("state" = 'finished_without_winner'         AND "closed" NOTNULL AND "fully_frozen" NOTNULL AND "ranks_available" = TRUE) OR
    ("state" = 'finished_with_winner'            AND "closed" NOTNULL AND "fully_frozen" NOTNULL AND "ranks_available" = TRUE)
  ));


-- Guess "revoked_by_member_id" values based on author of current draft and add constraint:

UPDATE "initiative" SET "revoked_by_member_id" = "author_id"
  FROM "current_draft"
  WHERE "initiative"."id" = "current_draft"."initiative_id"
  AND "initiative"."revoked" NOTNULL;

ALTER TABLE "initiative" ADD
  CONSTRAINT "all_or_none_of_revoked_and_revoked_by_member_id_must_be_null"
  CHECK ("revoked" NOTNULL = "revoked_by_member_id" NOTNULL);


-- Fill "unit_id" column with default value where neccessary and add constraints:

UPDATE "delegation" SET "unit_id" = 1 WHERE "scope" = 'unit';

ALTER TABLE "delegation" ADD CONSTRAINT "area_id_and_issue_id_set_according_to_scope"
  CHECK (
    ("scope" = 'unit'  AND "unit_id" NOTNULL AND "area_id" ISNULL  AND "issue_id" ISNULL ) OR
    ("scope" = 'area'  AND "unit_id" ISNULL  AND "area_id" NOTNULL AND "issue_id" ISNULL ) OR
    ("scope" = 'issue' AND "unit_id" ISNULL  AND "area_id" ISNULL  AND "issue_id" NOTNULL) );


-- Filling of "event" table with old (reconstructed) events:

DELETE FROM "event";
SELECT setval('event_id_seq', 1, false);

INSERT INTO "event"
  ( "occurrence", "event", "member_id", "issue_id", "state",
    "initiative_id", "draft_id", "suggestion_id" )
  SELECT * FROM (
    SELECT * FROM (
      SELECT DISTINCT ON ("initiative"."id")
        "timeline"."occurrence",
        CASE WHEN "issue_creation"."issue_id" NOTNULL THEN
          'initiative_created_in_new_issue'::"event_type"
        ELSE
          'initiative_created_in_existing_issue'::"event_type"
        END,
        "draft"."author_id",
        "issue"."id",
        CASE
          WHEN "timeline"."occurrence" < "issue"."accepted" THEN
            'admission'::"issue_state"
          WHEN "timeline"."occurrence" < "issue"."half_frozen" THEN
            'discussion'::"issue_state"
          ELSE
            'verification'::"issue_state"
        END,
        "initiative"."id",
        "draft"."id",
        NULL::INT8
      FROM "timeline"
      JOIN "initiative" ON "timeline"."initiative_id" = "initiative"."id"
      JOIN "issue" ON "issue"."id" = "initiative"."issue_id"
      LEFT JOIN "timeline" AS "issue_creation"
        ON "initiative"."issue_id" = "issue_creation"."issue_id"
        AND "issue_creation"."event" = 'issue_created'
        AND "timeline"."occurrence" = "issue_creation"."occurrence"
      JOIN "draft"
        ON "initiative"."id" = "draft"."initiative_id"
      WHERE "timeline"."event" = 'initiative_created'
      ORDER BY "initiative"."id", "draft"."id"
    ) AS "subquery"  -- NOTE: subquery needed due to DISTINCT/ORDER
  UNION ALL
    SELECT
      "timeline"."occurrence",
      'issue_state_changed'::"event_type",
      NULL,
      "issue"."id",
      CASE
        WHEN "timeline"."event" IN (
          'issue_canceled',
          'issue_finished_without_voting',
          'issue_finished_after_voting'
        ) THEN
          "issue"."state"
        WHEN "timeline"."event" = 'issue_accepted' THEN
          'discussion'::"issue_state"
        WHEN "timeline"."event" = 'issue_half_frozen' THEN
          'verification'::"issue_state"
        WHEN "timeline"."event" = 'issue_voting_started' THEN
          'voting'::"issue_state"
      END,
      NULL,
      NULL,
      NULL
    FROM "timeline"
    JOIN "issue" ON "timeline"."issue_id" = "issue"."id"
    WHERE "timeline"."event" IN (
      'issue_canceled',
      'issue_accepted',
      'issue_half_frozen',
      'issue_finished_without_voting',
      'issue_voting_started',
      'issue_finished_after_voting' )
  UNION ALL
    SELECT
      "timeline"."occurrence",
      'initiative_revoked'::"event_type",
      "initiative"."revoked_by_member_id",
      "issue"."id",
      CASE
        WHEN "timeline"."occurrence" < "issue"."accepted" THEN
          'admission'::"issue_state"
        WHEN "timeline"."occurrence" < "issue"."half_frozen" THEN
          'discussion'::"issue_state"
        ELSE
          'verification'::"issue_state"
      END,
      "initiative"."id",
      "current_draft"."id",
      NULL
    FROM "timeline"
    JOIN "initiative" ON "timeline"."initiative_id" = "initiative"."id"
    JOIN "issue" ON "issue"."id" = "initiative"."issue_id"
    JOIN "current_draft" ON "initiative"."id" = "current_draft"."initiative_id"
    WHERE "timeline"."event" = 'initiative_revoked'
  UNION ALL
    SELECT
      "timeline"."occurrence",
      'new_draft_created'::"event_type",
      "draft"."author_id",
      "issue"."id",
      CASE
        WHEN "timeline"."occurrence" < "issue"."accepted" THEN
          'admission'::"issue_state"
        WHEN "timeline"."occurrence" < "issue"."half_frozen" THEN
          'discussion'::"issue_state"
        ELSE
          'verification'::"issue_state"
      END,
      "initiative"."id",
      "draft"."id",
      NULL
    FROM "timeline"
    JOIN "draft" ON "timeline"."draft_id" = "draft"."id"
    JOIN "initiative" ON "draft"."initiative_id" = "initiative"."id"
    JOIN "issue" ON "initiative"."issue_id" = "issue"."id"
    LEFT JOIN "timeline" AS "initiative_creation"
      ON "initiative"."id" = "initiative_creation"."initiative_id"
      AND "initiative_creation"."event" = 'initiative_created'
      AND "timeline"."occurrence" = "initiative_creation"."occurrence"
    WHERE "timeline"."event" = 'draft_created'
    AND "initiative_creation"."initiative_id" ISNULL
  UNION ALL
    SELECT
      "timeline"."occurrence",
      'suggestion_created'::"event_type",
      "suggestion"."author_id",
      "issue"."id",
      CASE
        WHEN "timeline"."occurrence" < "issue"."accepted" THEN
          'admission'::"issue_state"
        WHEN "timeline"."occurrence" < "issue"."half_frozen" THEN
          'discussion'::"issue_state"
        ELSE
          'verification'::"issue_state"
      END,
      "initiative"."id",
      NULL,
      "suggestion"."id"
    FROM "timeline"
    JOIN "suggestion" ON "timeline"."suggestion_id" = "suggestion"."id"
    JOIN "initiative" ON "suggestion"."initiative_id" = "initiative"."id"
    JOIN "issue" ON "initiative"."issue_id" = "issue"."id"
    WHERE "timeline"."event" = 'suggestion_created'
  ) AS "subquery"
  ORDER BY "occurrence";


