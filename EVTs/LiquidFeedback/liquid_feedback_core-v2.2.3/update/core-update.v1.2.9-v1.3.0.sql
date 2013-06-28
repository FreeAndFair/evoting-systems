BEGIN;
 
CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.3.0', 1, 3, 0))
  AS "subquery"("string", "major", "minor", "revision");


-- update comment for column "fully_frozen" of table "issue"

COMMENT ON COLUMN "issue"."fully_frozen" IS 'Point in time, when "verification_time" has elapsed and voting has started; Frontends must ensure that for fully_frozen issues additionally to the restrictions for half_frozen issues a) initiatives are not created, b) no interest is created or removed, c) no supporters are added or removed, d) no opinions are created, changed or deleted.';


-- update comment for column "autoreject" of table "membership"

COMMENT ON COLUMN "membership"."autoreject" IS 'TRUE = member votes against all initiatives, if he is neither direct_ or delegating_voter; Entries in the "interest" table can override this setting.';


-- allow column "autoreject" of table "interest" to be NULL
-- (thus defaulting to "membership")

ALTER TABLE "interest" ALTER COLUMN "autoreject" DROP NOT NULL;


-- new table "ignored_issue" to allow members to ignore particular issues in certain states

CREATE TABLE "ignored_issue" (
        PRIMARY KEY ("issue_id", "member_id"),
        "issue_id"              INT4            REFERENCES "issue" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "member_id"             INT4            REFERENCES "member" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "new"                   BOOLEAN         NOT NULL DEFAULT FALSE,
        "accepted"              BOOLEAN         NOT NULL DEFAULT FALSE,
        "half_frozen"           BOOLEAN         NOT NULL DEFAULT FALSE,
        "fully_frozen"          BOOLEAN         NOT NULL DEFAULT FALSE );
CREATE INDEX "ignored_issue_member_id_idx" ON "ignored_issue" ("member_id");

COMMENT ON TABLE "ignored_issue" IS 'Table to store member specific options to ignore issues in selected states';

COMMENT ON COLUMN "ignored_issue"."new"          IS 'Apply when issue is neither closed nor accepted';
COMMENT ON COLUMN "ignored_issue"."accepted"     IS 'Apply when issue is accepted but not (half_)frozen or closed';
COMMENT ON COLUMN "ignored_issue"."half_frozen"  IS 'Apply when issue is half_frozen but not fully_frozen or closed';
COMMENT ON COLUMN "ignored_issue"."fully_frozen" IS 'Apply when issue is fully_frozen (in voting) and not closed';


-- allow area and issue delegations with trustee_id set to NULL
-- (indicating that global or area delegation is void for that area or issue)

ALTER TABLE "delegation" ALTER COLUMN "trustee_id" DROP NOT NULL;

ALTER TABLE "delegation" ADD CONSTRAINT "no_global_delegation_to_null"
  CHECK ("trustee_id" NOTNULL OR "scope" != 'global');


-- disable and delete "copy_autoreject" trigger on table "interest"

DROP TRIGGER "copy_autoreject" ON "interest";
DROP FUNCTION "copy_autoreject_trigger"();


-- update comments on delegation views

COMMENT ON VIEW "active_delegation" IS 'Helper view for views "global_delegation", "area_delegation" and "issue_delegation": Contains delegations where the truster_id refers to an active member and includes those delegations where trustee_id is NULL';

COMMENT ON VIEW "area_delegation" IS 'Resulting area delegations from active members; can include rows with trustee_id set to NULL';

COMMENT ON VIEW "issue_delegation" IS 'Resulting issue delegations from active members; can include rows with trustee_id set to NULL';


-- support for explicitly disabled delegations in "delegation_chain" functions

DROP FUNCTION "delegation_chain"
  ( "member"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE );

DROP FUNCTION "delegation_chain"
  ( "member"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE,
    "member"."id"%TYPE );

DROP TYPE "delegation_chain_row";

CREATE TYPE "delegation_chain_row" AS (
        "index"                 INT4,
        "member_id"             INT4,
        "member_active"         BOOLEAN,
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
    "area_id_p"             "area"."id"%TYPE,
    "issue_id_p"            "issue"."id"%TYPE,
    "simulate_trustee_id_p" "member"."id"%TYPE )
  RETURNS SETOF "delegation_chain_row"
  LANGUAGE 'plpgsql' STABLE AS $$
    DECLARE
      "issue_row"          "issue"%ROWTYPE;
      "visited_member_ids" INT4[];  -- "member"."id"%TYPE[]
      "loop_member_id_v"   "member"."id"%TYPE;
      "output_row"         "delegation_chain_row";
      "output_rows"        "delegation_chain_row"[];
      "delegation_row"     "delegation"%ROWTYPE;
      "row_count"          INT4;
      "i"                  INT4;
      "loop_v"             BOOLEAN;
    BEGIN
      SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
      "visited_member_ids" := '{}';
      "loop_member_id_v"   := NULL;
      "output_rows"        := '{}';
      "output_row"."index"         := 0;
      "output_row"."member_id"     := "member_id_p";
      "output_row"."member_active" := TRUE;
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
          SELECT NULL FROM "member" 
          WHERE "id" = "output_row"."member_id" AND "active"
        ) THEN
          IF "area_id_p" ISNULL AND "issue_id_p" ISNULL THEN
            SELECT * INTO "delegation_row" FROM "delegation"
              WHERE "truster_id" = "output_row"."member_id"
              AND "scope" = 'global';
          ELSIF "area_id_p" NOTNULL AND "issue_id_p" ISNULL THEN
            "output_row"."participation" := EXISTS (
              SELECT NULL FROM "membership"
              WHERE "area_id" = "area_id_p"
              AND "member_id" = "output_row"."member_id"
            );
            SELECT * INTO "delegation_row" FROM "delegation"
              WHERE "truster_id" = "output_row"."member_id"
              AND ("scope" = 'global' OR "area_id" = "area_id_p")
              ORDER BY "scope" DESC;
          ELSIF "area_id_p" ISNULL AND "issue_id_p" NOTNULL THEN
            "output_row"."participation" := EXISTS (
              SELECT NULL FROM "interest"
              WHERE "issue_id" = "issue_id_p"
              AND "member_id" = "output_row"."member_id"
            );
            SELECT * INTO "delegation_row" FROM "delegation"
              WHERE "truster_id" = "output_row"."member_id"
              AND ("scope" = 'global' OR
                "area_id" = "issue_row"."area_id" OR
                "issue_id" = "issue_id_p"
              )
              ORDER BY "scope" DESC;
          ELSE
            RAISE EXCEPTION 'Either area_id or issue_id or both must be NULL.';
          END IF;
        ELSE
          "output_row"."member_active" := FALSE;
          "output_row"."participation" := FALSE;
          "output_row"."scope_out"     := NULL;
          "delegation_row" := ROW(NULL);
        END IF;
        IF
          "output_row"."member_id" = "member_id_p" AND
          "simulate_trustee_id_p" NOTNULL
        THEN
          "output_row"."scope_out" := CASE
            WHEN "area_id_p" ISNULL  AND "issue_id_p" ISNULL  THEN 'global'
            WHEN "area_id_p" NOTNULL AND "issue_id_p" ISNULL  THEN 'area'
            WHEN "area_id_p" ISNULL  AND "issue_id_p" NOTNULL THEN 'issue'
          END;
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
        EXIT WHEN "output_row" ISNULL;
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
        IF "area_id_p" ISNULL AND "issue_id_p" ISNULL THEN
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
    "area"."id"%TYPE,
    "issue"."id"%TYPE,
    "member"."id"%TYPE )
  IS 'Helper function for frontends to display delegation chains; Not part of internal voting logic';

CREATE FUNCTION "delegation_chain"
  ( "member_id_p" "member"."id"%TYPE,
    "area_id_p"   "area"."id"%TYPE,
    "issue_id_p"  "issue"."id"%TYPE )
  RETURNS SETOF "delegation_chain_row"
  LANGUAGE 'plpgsql' STABLE AS $$
    DECLARE
      "result_row" "delegation_chain_row";
    BEGIN
      FOR "result_row" IN
        SELECT * FROM "delegation_chain"(
          "member_id_p", "area_id_p", "issue_id_p", NULL
        )
      LOOP
        RETURN NEXT "result_row";
      END LOOP;
      RETURN;
    END;
  $$;

COMMENT ON FUNCTION "delegation_chain"
  ( "member"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE )
  IS 'Shortcut for "delegation_chain"(...) function where 4th parameter is null';


-- delete entries of "ignored_issue" table in "delete_member"(...) and "delete_private_data"() functions

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
        DELETE FROM "ignored_issue"
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

CREATE OR REPLACE FUNCTION "delete_member"("member_id_p" "member"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      UPDATE "member" SET
        "last_login"                   = NULL,
        "login"                        = NULL,
        "password"                     = NULL,
        "active"                       = FALSE,
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
        "statement"                    = NULL
        WHERE "id" = "member_id_p";
      -- "text_search_data" is updated by triggers
      DELETE FROM "setting"            WHERE "member_id" = "member_id_p";
      DELETE FROM "setting_map"        WHERE "member_id" = "member_id_p";
      DELETE FROM "member_relation_setting" WHERE "member_id" = "member_id_p";
      DELETE FROM "member_image"       WHERE "member_id" = "member_id_p";
      DELETE FROM "contact"            WHERE "member_id" = "member_id_p";
      DELETE FROM "area_setting"       WHERE "member_id" = "member_id_p";
      DELETE FROM "issue_setting"      WHERE "member_id" = "member_id_p";
      DELETE FROM "initiative_setting" WHERE "member_id" = "member_id_p";
      DELETE FROM "suggestion_setting" WHERE "member_id" = "member_id_p";
      DELETE FROM "membership"         WHERE "member_id" = "member_id_p";
      DELETE FROM "ignored_issue"      WHERE "member_id" = "member_id_p";
      DELETE FROM "delegation"         WHERE "truster_id" = "member_id_p";
      DELETE FROM "direct_voter" USING "issue"
        WHERE "direct_voter"."issue_id" = "issue"."id"
        AND "issue"."closed" ISNULL
        AND "member_id" = "member_id_p";
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
      DELETE FROM "session";
      DELETE FROM "area_setting";
      DELETE FROM "issue_setting";
      DELETE FROM "initiative_setting";
      DELETE FROM "suggestion_setting";
      DELETE FROM "ignored_issue";
      DELETE FROM "direct_voter" USING "issue"
        WHERE "direct_voter"."issue_id" = "issue"."id"
        AND "issue"."closed" ISNULL;
      RETURN;
    END;
  $$;


COMMIT;
