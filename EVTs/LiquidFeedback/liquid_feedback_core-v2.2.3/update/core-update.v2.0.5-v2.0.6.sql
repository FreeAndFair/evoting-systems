BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('2.0.6', 2, 0, 6))
  AS "subquery"("string", "major", "minor", "revision");

-- add column "invite_code_expiry" to table "member":
ALTER TABLE "member" ADD COLUMN "invite_code_expiry" TIMESTAMPTZ;
COMMENT ON COLUMN "member"."invite_code_expiry" IS 'Expiry data/time for "invite_code"';

-- write member history only for activated accounts:
CREATE OR REPLACE FUNCTION "write_member_history_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF
        ( NEW."active" != OLD."active" OR
          NEW."name"   != OLD."name" ) AND
        OLD."activated" NOTNULL
      THEN
        INSERT INTO "member_history"
          ("member_id", "active", "name")
          VALUES (NEW."id", OLD."active", OLD."name");
      END IF;
      RETURN NULL;
    END;
  $$;

-- set "draft_id" in "event" table on event 'initiative_revoked':
CREATE OR REPLACE FUNCTION "write_event_initiative_revoked_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_row"  "issue"%ROWTYPE;
      "draft_id_v" "draft"."id"%TYPE;
    BEGIN
      IF OLD."revoked" ISNULL AND NEW."revoked" NOTNULL THEN
        SELECT * INTO "issue_row" FROM "issue"
          WHERE "id" = NEW."issue_id";
        SELECT "id" INTO "draft_id_v" FROM "current_draft"
          WHERE "initiative_id" = NEW."id";
        INSERT INTO "event" (
            "event", "member_id", "issue_id", "state", "initiative_id", "draft_id"
          ) VALUES (
            'initiative_revoked',
            NEW."revoked_by_member_id",
            NEW."issue_id",
            "issue_row"."state",
            NEW."id",
            "draft_id_v");
      END IF;
      RETURN NULL;
    END;
  $$;

-- delete column "invite_code_expiry" in function "delete_private_data":
CREATE OR REPLACE FUNCTION "delete_private_data"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      DELETE FROM "member" WHERE "activated" ISNULL;
      UPDATE "member" SET
        "invite_code"                  = NULL,
        "invite_code_expiry"           = NULL,
        "admin_comment"                = NULL,
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
      DELETE FROM "setting";
      DELETE FROM "setting_map";
      DELETE FROM "member_relation_setting";
      DELETE FROM "member_image";
      DELETE FROM "contact";
      DELETE FROM "ignored_member";
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

COMMIT;
