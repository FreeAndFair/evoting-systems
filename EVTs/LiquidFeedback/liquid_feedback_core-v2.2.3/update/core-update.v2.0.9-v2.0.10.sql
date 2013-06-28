BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('2.0.10', 2, 0, 10))
  AS "subquery"("string", "major", "minor", "revision");

DROP FUNCTION "delegation_info"
  ( "member"."id"%TYPE,
    "unit"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE,
    "member"."id"%TYPE );

DROP TYPE "delegation_info_type";


CREATE TYPE "delegation_info_type" AS (
        "own_participation"           BOOLEAN,
        "own_delegation_scope"        "delegation_scope",
        "first_trustee_id"            INT4,
        "first_trustee_participation" BOOLEAN,
        "first_trustee_ellipsis"      BOOLEAN,
        "other_trustee_id"            INT4,
        "other_trustee_participation" BOOLEAN,
        "other_trustee_ellipsis"      BOOLEAN,
        "delegation_loop"             "delegation_info_loop_type",
        "participating_member_id"     INT4 );

COMMENT ON TYPE "delegation_info_type" IS 'Type of result returned by "delegation_info" function; For meaning of "participation" check comment on "delegation_chain_row" type';

COMMENT ON COLUMN "delegation_info_type"."own_participation"           IS 'Member is directly participating';
COMMENT ON COLUMN "delegation_info_type"."own_delegation_scope"        IS 'Delegation scope of member';
COMMENT ON COLUMN "delegation_info_type"."first_trustee_id"            IS 'Direct trustee of member';
COMMENT ON COLUMN "delegation_info_type"."first_trustee_participation" IS 'Direct trustee of member is participating';
COMMENT ON COLUMN "delegation_info_type"."first_trustee_ellipsis"      IS 'Ellipsis in delegation chain after "first_trustee"';
COMMENT ON COLUMN "delegation_info_type"."other_trustee_id"            IS 'Another relevant trustee (due to participation)';
COMMENT ON COLUMN "delegation_info_type"."other_trustee_participation" IS 'Another trustee is participating (redundant field: if "other_trustee_id" is set, then "other_trustee_participation" is always TRUE, else "other_trustee_participation" is NULL)';
COMMENT ON COLUMN "delegation_info_type"."other_trustee_ellipsis"      IS 'Ellipsis in delegation chain after "other_trustee"';
COMMENT ON COLUMN "delegation_info_type"."delegation_loop"             IS 'Non-NULL value, if delegation chain contains a circle; See comment on "delegation_info_loop_type" for details';
COMMENT ON COLUMN "delegation_info_type"."participating_member_id"     IS 'First participating member in delegation chain';


CREATE FUNCTION "delegation_info"
  ( "member_id_p"           "member"."id"%TYPE,
    "unit_id_p"             "unit"."id"%TYPE,
    "area_id_p"             "area"."id"%TYPE,
    "issue_id_p"            "issue"."id"%TYPE,
    "simulate_trustee_id_p" "member"."id"%TYPE DEFAULT NULL )
  RETURNS "delegation_info_type"
  LANGUAGE 'plpgsql' STABLE AS $$
    DECLARE
      "current_row" "delegation_chain_row";
      "result"      "delegation_info_type";
    BEGIN
      "result"."own_participation" := FALSE;
      FOR "current_row" IN
        SELECT * FROM "delegation_chain"(
          "member_id_p",
          "unit_id_p", "area_id_p", "issue_id_p",
          "simulate_trustee_id_p")
      LOOP
        IF
          "result"."participating_member_id" ISNULL AND
          "current_row"."participation"
        THEN
          "result"."participating_member_id" := "current_row"."member_id";
        END IF;
        IF "current_row"."member_id" = "member_id_p" THEN
          "result"."own_participation"    := "current_row"."participation";
          "result"."own_delegation_scope" := "current_row"."scope_out";
          IF "current_row"."loop" = 'first' THEN
            "result"."delegation_loop" := 'own';
          END IF;
        ELSIF
          "current_row"."member_valid" AND
          ( "current_row"."loop" ISNULL OR
            "current_row"."loop" != 'repetition' )
        THEN
          IF "result"."first_trustee_id" ISNULL THEN
            "result"."first_trustee_id"            := "current_row"."member_id";
            "result"."first_trustee_participation" := "current_row"."participation";
            "result"."first_trustee_ellipsis"      := FALSE;
            IF "current_row"."loop" = 'first' THEN
              "result"."delegation_loop" := 'first';
            END IF;
          ELSIF "result"."other_trustee_id" ISNULL THEN
            IF "current_row"."participation" AND NOT "current_row"."overridden" THEN
              "result"."other_trustee_id"            := "current_row"."member_id";
              "result"."other_trustee_participation" := TRUE;
              "result"."other_trustee_ellipsis"      := FALSE;
              IF "current_row"."loop" = 'first' THEN
                "result"."delegation_loop" := 'other';
              END IF;
            ELSE
              "result"."first_trustee_ellipsis" := TRUE;
              IF "current_row"."loop" = 'first' THEN
                "result"."delegation_loop" := 'first_ellipsis';
              END IF;
            END IF;
          ELSE
            "result"."other_trustee_ellipsis" := TRUE;
            IF "current_row"."loop" = 'first' THEN
              "result"."delegation_loop" := 'other_ellipsis';
            END IF;
          END IF;
        END IF;
      END LOOP;
      RETURN "result";
    END;
  $$;

COMMENT ON FUNCTION "delegation_info"
  ( "member"."id"%TYPE,
    "unit"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE,
    "member"."id"%TYPE )
  IS 'Notable information about a delegation chain for unit, area, or issue; See "delegation_info_type" for more information';


COMMIT;
