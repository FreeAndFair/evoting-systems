BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.2.3', 1, 2, 3))
  AS "subquery"("string", "major", "minor", "revision");

CREATE TABLE "rendered_draft" (
        PRIMARY KEY ("draft_id", "format"),
        "draft_id"              INT8            REFERENCES "draft" ("id") ON DELETE CASCADE ON UPDATE CASCADE,
        "format"                TEXT,
        "content"               TEXT            NOT NULL );

COMMENT ON TABLE "rendered_draft" IS 'This table may be used by frontends to cache "rendered" drafts (e.g. HTML output generated from wiki text)';

COMMIT;
