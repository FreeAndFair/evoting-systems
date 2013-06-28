CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('1.4.0', 1, 4, 0))
  AS "subquery"("string", "major", "minor", "revision");
