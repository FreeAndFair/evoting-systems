BEGIN;

CREATE OR REPLACE VIEW "liquid_feedback_version" AS
  SELECT * FROM (VALUES ('2.0.11', 2, 0, 11))
  AS "subquery"("string", "major", "minor", "revision");

DROP FUNCTION "delegation_info"
  ( "member"."id"%TYPE,
    "unit"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE,
    "member"."id"%TYPE );

DROP FUNCTION "delegation_chain"
  ( "member"."id"%TYPE,
    "unit"."id"%TYPE,
    "area"."id"%TYPE,
    "issue"."id"%TYPE,
    "member"."id"%TYPE );

CREATE FUNCTION "delegation_chain"
  ( "member_id_p"           "member"."id"%TYPE,
    "unit_id_p"             "unit"."id"%TYPE,
    "area_id_p"             "area"."id"%TYPE,
    "issue_id_p"            "issue"."id"%TYPE,
    "simulate_trustee_id_p" "member"."id"%TYPE DEFAULT NULL,
    "simulate_default_p"    BOOLEAN            DEFAULT FALSE )
  RETURNS SETOF "delegation_chain_row"
  LANGUAGE 'plpgsql' STABLE AS $$
    DECLARE
      "scope_v"            "delegation_scope";
      "unit_id_v"          "unit"."id"%TYPE;
      "area_id_v"          "area"."id"%TYPE;
      "issue_row"          "issue"%ROWTYPE;
      "visited_member_ids" INT4[];  -- "member"."id"%TYPE[]
      "loop_member_id_v"   "member"."id"%TYPE;
      "output_row"         "delegation_chain_row";
      "output_rows"        "delegation_chain_row"[];
      "simulate_v"         BOOLEAN;
      "simulate_here_v"    BOOLEAN;
      "delegation_row"     "delegation"%ROWTYPE;
      "row_count"          INT4;
      "i"                  INT4;
      "loop_v"             BOOLEAN;
    BEGIN
      IF "simulate_trustee_id_p" NOTNULL AND "simulate_default_p" THEN
        RAISE EXCEPTION 'Both "simulate_trustee_id_p" is set, and "simulate_default_p" is true';
      END IF;
      IF "simulate_trustee_id_p" NOTNULL OR "simulate_default_p" THEN
        "simulate_v" := TRUE;
      ELSE
        "simulate_v" := FALSE;
      END IF;
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
        SELECT INTO "issue_row" * FROM "issue" WHERE "id" = "issue_id_p";
        IF "issue_row"."id" ISNULL THEN
          RETURN;
        END IF;
        IF "issue_row"."closed" NOTNULL THEN
          IF "simulate_v" THEN
            RAISE EXCEPTION 'Tried to simulate delegation chain for closed issue.';
          END IF;
          FOR "output_row" IN
            SELECT * FROM
            "delegation_chain_for_closed_issue"("member_id_p", "issue_id_p")
          LOOP
            RETURN NEXT "output_row";
          END LOOP;
          RETURN;
        END IF;
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
        IF "output_row"."participation" ISNULL THEN
          "output_row"."overridden" := NULL;
        ELSIF "output_row"."participation" THEN
          "output_row"."overridden" := TRUE;
        END IF;
        "output_row"."scope_in" := "output_row"."scope_out";
        "output_row"."member_valid" := EXISTS (
          SELECT NULL FROM "member" JOIN "privilege"
          ON "privilege"."member_id" = "member"."id"
          AND "privilege"."unit_id" = "unit_id_v"
          WHERE "id" = "output_row"."member_id"
          AND "member"."active" AND "privilege"."voting_right"
        );
        "simulate_here_v" := (
          "simulate_v" AND
          "output_row"."member_id" = "member_id_p"
        );
        "delegation_row" := ROW(NULL);
        IF "output_row"."member_valid" OR "simulate_here_v" THEN
          IF "scope_v" = 'unit' THEN
            IF NOT "simulate_here_v" THEN
              SELECT * INTO "delegation_row" FROM "delegation"
                WHERE "truster_id" = "output_row"."member_id"
                AND "unit_id" = "unit_id_v";
            END IF;
          ELSIF "scope_v" = 'area' THEN
            "output_row"."participation" := EXISTS (
              SELECT NULL FROM "membership"
              WHERE "area_id" = "area_id_p"
              AND "member_id" = "output_row"."member_id"
            );
            IF "simulate_here_v" THEN
              IF "simulate_trustee_id_p" ISNULL THEN
                SELECT * INTO "delegation_row" FROM "delegation"
                  WHERE "truster_id" = "output_row"."member_id"
                  AND "unit_id" = "unit_id_v";
              END IF;
            ELSE
              SELECT * INTO "delegation_row" FROM "delegation"
                WHERE "truster_id" = "output_row"."member_id"
                AND (
                  "unit_id" = "unit_id_v" OR
                  "area_id" = "area_id_v"
                )
                ORDER BY "scope" DESC;
            END IF;
          ELSIF "scope_v" = 'issue' THEN
            IF "issue_row"."fully_frozen" ISNULL THEN
              "output_row"."participation" := EXISTS (
                SELECT NULL FROM "interest"
                WHERE "issue_id" = "issue_id_p"
                AND "member_id" = "output_row"."member_id"
              );
            ELSE
              IF "output_row"."member_id" = "member_id_p" THEN
                "output_row"."participation" := EXISTS (
                  SELECT NULL FROM "direct_voter"
                  WHERE "issue_id" = "issue_id_p"
                  AND "member_id" = "output_row"."member_id"
                );
              ELSE
                "output_row"."participation" := NULL;
              END IF;
            END IF;
            IF "simulate_here_v" THEN
              IF "simulate_trustee_id_p" ISNULL THEN
                SELECT * INTO "delegation_row" FROM "delegation"
                  WHERE "truster_id" = "output_row"."member_id"
                  AND (
                    "unit_id" = "unit_id_v" OR
                    "area_id" = "area_id_v"
                  )
                  ORDER BY "scope" DESC;
              END IF;
            ELSE
              SELECT * INTO "delegation_row" FROM "delegation"
                WHERE "truster_id" = "output_row"."member_id"
                AND (
                  "unit_id" = "unit_id_v" OR
                  "area_id" = "area_id_v" OR
                  "issue_id" = "issue_id_p"
                )
                ORDER BY "scope" DESC;
            END IF;
          END IF;
        ELSE
          "output_row"."participation" := FALSE;
        END IF;
        IF "simulate_here_v" AND "simulate_trustee_id_p" NOTNULL THEN
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
    "member"."id"%TYPE,
    BOOLEAN )
  IS 'Shows a delegation chain for unit, area, or issue; See "delegation_chain_row" type for more information';

CREATE FUNCTION "delegation_info"
  ( "member_id_p"           "member"."id"%TYPE,
    "unit_id_p"             "unit"."id"%TYPE,
    "area_id_p"             "area"."id"%TYPE,
    "issue_id_p"            "issue"."id"%TYPE,
    "simulate_trustee_id_p" "member"."id"%TYPE DEFAULT NULL,
    "simulate_default_p"    BOOLEAN            DEFAULT FALSE )
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
          "simulate_trustee_id_p", "simulate_default_p")
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
    "member"."id"%TYPE,
    BOOLEAN )
  IS 'Notable information about a delegation chain for unit, area, or issue; See "delegation_info_type" for more information';

COMMIT;
