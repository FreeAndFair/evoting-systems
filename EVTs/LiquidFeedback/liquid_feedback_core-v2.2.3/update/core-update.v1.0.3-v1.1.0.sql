BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.1.0', 1, 1, 0))
  AS "subquery"("string", "major", "minor", "revision");

ALTER TABLE "member" ADD COLUMN "notify_email_lock_expiry" TIMESTAMPTZ;
COMMENT ON COLUMN "member"."notify_email_lock_expiry" IS 'Date/time until no further email confirmation mails may be sent (abuse protection)';

ALTER TABLE "direct_population_snapshot" DROP COLUMN "interest_exists";

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
        WHERE "issue"."id" = "issue_id_p"
        AND "member"."active"
        UNION
        SELECT
          "issue_id_p"                 AS "issue_id",
          'periodic'::"snapshot_event" AS "event",
          "member"."id"                AS "member_id"
        FROM "interest" JOIN "member"
        ON "interest"."member_id" = "member"."id"
        WHERE "interest"."issue_id" = "issue_id_p"
        AND "member"."active";
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

COMMENT ON FUNCTION "freeze_after_snapshot"
  ( "issue"."id"%TYPE )
  IS 'This function freezes an issue (fully) and starts voting, but must only be called when "create_snapshot" was called in the same transaction.';

COMMENT ON FUNCTION "manual_freeze"
  ( "issue"."id"%TYPE )
  IS 'Freeze an issue manually (fully) and start voting';

DROP FUNCTION "delete_member_data"("member"."id"%TYPE);

CREATE FUNCTION "delete_member"("member_id_p" "member"."id"%TYPE)
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      UPDATE "member" SET
        "login"                        = NULL,
        "password"                     = NULL,
        "active"                       = FALSE,
        "notify_email"                 = NULL,
        "notify_email_unconfirmed"     = NULL,
        "notify_email_secret"          = NULL,
        "notify_email_secret_expiry"   = NULL,
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
      UPDATE "member_history" SET "login" = NULL
        WHERE "member_id" = "member_id_p";
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
      DELETE FROM "delegation"         WHERE "truster_id" = "member_id_p";
      RETURN;
    END;
  $$;

COMMENT ON FUNCTION "delete_member"("member_id_p" "member"."id"%TYPE) IS 'Clear certain settings and data of a particular member (data protection)';

CREATE OR REPLACE FUNCTION "delete_private_data"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      UPDATE "member" SET
        "login"                        = NULL,
        "password"                     = NULL,
        "notify_email"                 = NULL,
        "notify_email_unconfirmed"     = NULL,
        "notify_email_secret"          = NULL,
        "notify_email_secret_expiry"   = NULL,
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
      UPDATE "member_history" SET "login" = NULL;
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
      DELETE FROM "direct_voter" USING "issue"
        WHERE "direct_voter"."issue_id" = "issue"."id"
        AND "issue"."closed" ISNULL;
      RETURN;
    END;
  $$;

COMMIT;
