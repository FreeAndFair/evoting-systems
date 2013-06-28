BEGIN;

DROP VIEW "liquid_feedback_version";
CREATE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.0.0', 1, 0, 0))
  AS "subquery"("string", "major", "minor", "revision");
 
ALTER TABLE "member" ALTER COLUMN "login" DROP NOT NULL;

ALTER TABLE "member_history" ALTER COLUMN "login" DROP NOT NULL;

CREATE INDEX "member_history_member_id_idx" ON "member_history" ("member_id");

ALTER TABLE "direct_population_snapshot" DROP
  CONSTRAINT "direct_population_snapshot_member_id_fkey";
ALTER TABLE "direct_population_snapshot" ADD
  CONSTRAINT "direct_population_snapshot_member_id_fkey"
  FOREIGN KEY ("member_id")
  REFERENCES "member"("id") ON DELETE RESTRICT ON UPDATE RESTRICT;

ALTER TABLE "delegating_population_snapshot" DROP
  CONSTRAINT "delegating_population_snapshot_member_id_fkey";
ALTER TABLE "delegating_population_snapshot" ADD
  CONSTRAINT "delegating_population_snapshot_member_id_fkey"
  FOREIGN KEY ("member_id")
  REFERENCES "member"("id") ON DELETE RESTRICT ON UPDATE RESTRICT;

ALTER TABLE "direct_interest_snapshot" DROP
  CONSTRAINT "direct_interest_snapshot_member_id_fkey";
ALTER TABLE "direct_interest_snapshot" ADD
  CONSTRAINT "direct_interest_snapshot_member_id_fkey"
  FOREIGN KEY ("member_id")
  REFERENCES "member"("id") ON DELETE RESTRICT ON UPDATE RESTRICT;

ALTER TABLE "delegating_interest_snapshot" DROP
  CONSTRAINT "delegating_interest_snapshot_member_id_fkey";
ALTER TABLE "delegating_interest_snapshot" ADD
  CONSTRAINT "delegating_interest_snapshot_member_id_fkey"
  FOREIGN KEY ("member_id")
  REFERENCES "member"("id") ON DELETE RESTRICT ON UPDATE RESTRICT;

ALTER TABLE "direct_supporter_snapshot" DROP
  CONSTRAINT "direct_supporter_snapshot_member_id_fkey";
ALTER TABLE "direct_supporter_snapshot" ADD
  CONSTRAINT "direct_supporter_snapshot_member_id_fkey"
  FOREIGN KEY ("member_id")
  REFERENCES "member"("id") ON DELETE RESTRICT ON UPDATE RESTRICT;

ALTER TABLE "direct_voter" DROP
  CONSTRAINT "direct_voter_member_id_fkey";
ALTER TABLE "direct_voter" ADD
  CONSTRAINT "direct_voter_member_id_fkey"
  FOREIGN KEY ("member_id")
  REFERENCES "member"("id") ON DELETE RESTRICT ON UPDATE RESTRICT;

ALTER TABLE "delegating_voter" DROP
  CONSTRAINT "delegating_voter_member_id_fkey";
ALTER TABLE "delegating_voter" ADD
  CONSTRAINT "delegating_voter_member_id_fkey"
  FOREIGN KEY ("member_id")
  REFERENCES "member"("id") ON DELETE RESTRICT ON UPDATE RESTRICT;

CREATE OR REPLACE FUNCTION "write_member_history_trigger"()
  RETURNS TRIGGER
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      IF
        ( NEW."login" NOTNULL AND OLD."login" NOTNULL AND
          NEW."login" != OLD."login" ) OR
        ( NEW."login" NOTNULL AND OLD."login" ISNULL ) OR
        ( NEW."login" ISNULL AND OLD."login" NOTNULL ) OR
        NEW."active" != OLD."active" OR
        NEW."name"   != OLD."name"
      THEN
        INSERT INTO "member_history"
          ("member_id", "login", "active", "name")
          VALUES (NEW."id", OLD."login", OLD."active", OLD."name");
      END IF;
      RETURN NULL;
    END;
  $$;

CREATE FUNCTION "delete_member_data"("member_id_p" "member"."id"%TYPE)
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
      RETURN;
    END;
  $$;
COMMENT ON FUNCTION "delete_member_data"("member_id_p" "member"."id"%TYPE) IS 'Clear certain settings and data of a particular member (data protection)';

CREATE OR REPLACE FUNCTION "delete_private_data"()
  RETURNS VOID
  LANGUAGE 'plpgsql' VOLATILE AS $$
    BEGIN
      PERFORM "delete_member_data"("id") FROM "member";
      DELETE FROM "invite_code";
      DELETE FROM "session";
      DELETE FROM "direct_voter" USING "issue"
        WHERE "direct_voter"."issue_id" = "issue"."id"
        AND "issue"."closed" ISNULL;
      RETURN;
    END;
  $$;

COMMIT;
