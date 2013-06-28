BEGIN;

-- update version number:
CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('2.0.4', 2, 0, 4))
  AS "subquery"("string", "major", "minor", "revision");

-- drop NOT NULL constraints on columns "name" and "notify_level"
-- in table "member", and add new constraint for "name":
ALTER TABLE "member" ALTER COLUMN "notify_level" DROP NOT NULL;
ALTER TABLE "member" ALTER COLUMN "name" DROP NOT NULL;
ALTER TABLE "member" ADD CONSTRAINT "name_not_null_if_activated" CHECK ("activated" ISNULL OR "name" NOTNULL);
COMMENT ON COLUMN "member"."notify_level" IS 'Selects which event notifications are to be sent to the "notify_email" mail address, may be NULL if member did not make any selection yet';
COMMENT ON COLUMN "member"."name"         IS 'Distinct name of the member, may be NULL if account has not been activated yet';

-- add table "session":
CREATE TABLE "session" (
        "ident"                 TEXT            PRIMARY KEY,
        "additional_secret"     TEXT,
        "expiry"                TIMESTAMPTZ     NOT NULL DEFAULT now() + '24 hours',
        "member_id"             INT8            REFERENCES "member" ("id") ON DELETE SET NULL,
        "lang"                  TEXT );
CREATE INDEX "session_expiry_idx" ON "session" ("expiry");
COMMENT ON TABLE "session" IS 'Sessions, i.e. for a web-frontend or API layer';
COMMENT ON COLUMN "session"."ident"             IS 'Secret session identifier (i.e. random string)';
COMMENT ON COLUMN "session"."additional_secret" IS 'Additional field to store a secret, which can be used against CSRF attacks';
COMMENT ON COLUMN "session"."member_id"         IS 'Reference to member, who is logged in';
COMMENT ON COLUMN "session"."lang"              IS 'Language code of the selected language';

-- add column "lang" to table "member":
ALTER TABLE "member" ADD COLUMN "lang" TEXT;
COMMENT ON COLUMN "member"."lang" IS 'Language code of the preferred language of the member';

-- drop view "pending_notification":
DROP VIEW "pending_notification";

-- remove column "notify_event_id" of table "member":
ALTER TABLE "member" DROP COLUMN "notify_event_id";

-- add table "notification_sent":
CREATE TABLE "notification_sent" (
        "event_id"              INT8            NOT NULL );
CREATE UNIQUE INDEX "notification_sent_singleton_idx" ON "notification_sent" ((1));
COMMENT ON TABLE "notification_sent" IS 'This table stores one row with the last event_id, for which notifications have been sent out';
COMMENT ON INDEX "notification_sent_singleton_idx" IS 'This index ensures that "notification_sent" only contains one row maximum.';

-- add view "selected_event_seen_by_member":
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

-- delete non-activated members in function "delete_private_data":
CREATE OR REPLACE FUNCTION "delete_private_data"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      DELETE FROM "member" WHERE "activated" ISNULL;
      UPDATE "member" SET
        "invite_code"                  = NULL,
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
