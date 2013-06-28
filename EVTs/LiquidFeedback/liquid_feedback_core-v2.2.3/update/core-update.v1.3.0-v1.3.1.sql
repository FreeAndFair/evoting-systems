BEGIN;
 
CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.3.1', 1, 3, 1))
  AS "subquery"("string", "major", "minor", "revision");

CREATE TABLE "system_setting" (
        "member_ttl"            INTERVAL );
CREATE UNIQUE INDEX "system_setting_singleton_idx" ON "system_setting" ((1));

COMMENT ON TABLE "system_setting" IS 'This table contains only one row with different settings in each column.';
COMMENT ON INDEX "system_setting_singleton_idx" IS 'This index ensures that "system_setting" only contains one row maximum.';
COMMENT ON COLUMN "system_setting"."member_ttl" IS 'Time after members get their "active" flag set to FALSE, if they do not login anymore.';

ALTER TABLE "member" ADD COLUMN "last_login_public" DATE;
ALTER TABLE "member" ADD COLUMN "locked" BOOLEAN NOT NULL DEFAULT FALSE;

UPDATE "member" SET "locked" = TRUE WHERE "active" = FALSE;

COMMENT ON COLUMN "member"."last_login"        IS 'Timestamp of last login';
COMMENT ON COLUMN "member"."last_login_public" IS 'Date of last login (time stripped for privacy reasons, updated only after day change)';
COMMENT ON COLUMN "member"."locked"            IS 'Locked members can not log in.';
COMMENT ON COLUMN "member"."active"            IS 'Memberships, support and votes are taken into account when corresponding members are marked as active. When the user does not log in for an extended period of time, this flag may be set to FALSE. If the user is not locked, he/she may reset the active flag by logging in.';

CREATE FUNCTION "check_last_login"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "system_setting_row" "system_setting"%ROWTYPE;
    BEGIN
      SELECT * INTO "system_setting_row" FROM "system_setting";
      LOCK TABLE "member" IN SHARE ROW EXCLUSIVE MODE;
      UPDATE "member" SET "last_login_public" = "last_login"::date
        FROM (
          SELECT DISTINCT "member"."id"
          FROM "member" LEFT JOIN "member_history"
          ON "member"."id" = "member_history"."member_id"
          WHERE "member"."last_login"::date < 'today' OR (
            "member_history"."until"::date >= 'today' AND
            "member_history"."active" = FALSE AND "member"."active" = TRUE
          )
        ) AS "subquery"
        WHERE "member"."id" = "subquery"."id";
      IF "system_setting_row"."member_ttl" NOTNULL THEN
        UPDATE "member" SET "active" = FALSE
          WHERE "active" = TRUE
          AND "last_login"::date < 'today'
          AND "last_login_public" <
            (now() - "system_setting_row"."member_ttl")::date;
      END IF;
      RETURN;
    END;
  $$;

COMMENT ON FUNCTION "check_last_login"() IS 'Updates "last_login_public" field, which contains the date but not the time of the last login, and deactivates members who do not login for the time specified in "system_setting"."member_ttl". For privacy reasons this function does not update "last_login_public", if the last login of a member has been today (except when member was reactivated today).';

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
        FROM "interest" JOIN "member"
        ON "interest"."member_id" = "member"."id"
        WHERE "interest"."issue_id" = "issue_id_p"
        AND "member"."active";
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

CREATE OR REPLACE FUNCTION "check_everything"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    DECLARE
      "issue_id_v" "issue"."id"%TYPE;
    BEGIN
      DELETE FROM "expired_session";
      PERFORM "check_last_login"();
      PERFORM "calculate_member_counts"();
      FOR "issue_id_v" IN SELECT "id" FROM "open_issue" LOOP
        PERFORM "check_issue"("issue_id_v");
      END LOOP;
      FOR "issue_id_v" IN SELECT "id" FROM "issue_with_ranks_missing" LOOP
        PERFORM "calculate_ranks"("issue_id_v");
      END LOOP;
      RETURN;
    END;
  $$;

COMMENT ON FUNCTION "check_everything"() IS 'Amongst other regular tasks this function performs "check_issue" for every open issue, and if possible, automatically calculates ranks. Use this function only for development and debugging purposes, as long transactions with exclusive locking may result. In productive environments you should call the lf_update program instead.';

CREATE OR REPLACE FUNCTION "delete_member"("member_id_p" "member"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      UPDATE "member" SET
        "last_login"                   = NULL,
        "last_login_public"            = NULL,
        "login"                        = NULL,
        "password"                     = NULL,
        "locked"                       = TRUE,
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

COMMIT;
