--
-- PostgreSQL database dump
--

SET statement_timeout = 0;
SET client_encoding = 'UTF8';
SET standard_conforming_strings = off;
SET check_function_bodies = false;
SET client_min_messages = warning;
SET escape_string_warning = off;

--
-- Name: plpgsql; Type: PROCEDURAL LANGUAGE; Schema: -; Owner: www-data
--

CREATE PROCEDURAL LANGUAGE plpgsql;


ALTER PROCEDURAL LANGUAGE plpgsql OWNER TO "www-data";

SET search_path = public, pg_catalog;

--
-- Name: application_access_level; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE application_access_level AS ENUM (
    'member',
    'full',
    'pseudonymous',
    'anonymous'
);


ALTER TYPE public.application_access_level OWNER TO "www-data";

--
-- Name: TYPE application_access_level; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE application_access_level IS 'Access privileges for applications using the API';


--
-- Name: delegation_chain_loop_tag; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE delegation_chain_loop_tag AS ENUM (
    'first',
    'intermediate',
    'last',
    'repetition'
);


ALTER TYPE public.delegation_chain_loop_tag OWNER TO "www-data";

--
-- Name: TYPE delegation_chain_loop_tag; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE delegation_chain_loop_tag IS 'Type for loop tags in "delegation_chain_row" type';


--
-- Name: delegation_scope; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE delegation_scope AS ENUM (
    'unit',
    'area',
    'issue'
);


ALTER TYPE public.delegation_scope OWNER TO "www-data";

--
-- Name: TYPE delegation_scope; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE delegation_scope IS 'Scope for delegations: ''unit'', ''area'', or ''issue'' (order is relevant)';


--
-- Name: delegation_chain_row; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE delegation_chain_row AS (
	index integer,
	member_id integer,
	member_valid boolean,
	participation boolean,
	overridden boolean,
	scope_in delegation_scope,
	scope_out delegation_scope,
	disabled_out boolean,
	loop delegation_chain_loop_tag
);


ALTER TYPE public.delegation_chain_row OWNER TO "www-data";

--
-- Name: TYPE delegation_chain_row; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE delegation_chain_row IS 'Type of rows returned by "delegation_chain" function';


--
-- Name: delegation_info_loop_type; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE delegation_info_loop_type AS ENUM (
    'own',
    'first',
    'first_ellipsis',
    'other',
    'other_ellipsis'
);


ALTER TYPE public.delegation_info_loop_type OWNER TO "www-data";

--
-- Name: TYPE delegation_info_loop_type; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE delegation_info_loop_type IS 'Type of "delegation_loop" in "delegation_info_type"; ''own'' means loop to self, ''first'' means loop to first trustee, ''first_ellipsis'' means loop to ellipsis after first trustee, ''other'' means loop to other trustee, ''other_ellipsis'' means loop to ellipsis after other trustee''';


--
-- Name: delegation_info_type; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE delegation_info_type AS (
	own_participation boolean,
	own_delegation_scope delegation_scope,
	first_trustee_id integer,
	first_trustee_participation boolean,
	first_trustee_ellipsis boolean,
	other_trustee_id integer,
	other_trustee_participation boolean,
	other_trustee_ellipsis boolean,
	delegation_loop delegation_info_loop_type,
	participating_member_id integer
);


ALTER TYPE public.delegation_info_type OWNER TO "www-data";

--
-- Name: TYPE delegation_info_type; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE delegation_info_type IS 'Type of result returned by "delegation_info" function; For meaning of "participation" check comment on "delegation_chain_row" type';


--
-- Name: event_type; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE event_type AS ENUM (
    'issue_state_changed',
    'initiative_created_in_new_issue',
    'initiative_created_in_existing_issue',
    'initiative_revoked',
    'new_draft_created',
    'suggestion_created'
);


ALTER TYPE public.event_type OWNER TO "www-data";

--
-- Name: TYPE event_type; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE event_type IS 'Type used for column "event" of table "event"';


--
-- Name: issue_state; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE issue_state AS ENUM (
    'admission',
    'discussion',
    'verification',
    'voting',
    'canceled_revoked_before_accepted',
    'canceled_issue_not_accepted',
    'canceled_after_revocation_during_discussion',
    'canceled_after_revocation_during_verification',
    'calculation',
    'canceled_no_initiative_admitted',
    'finished_without_winner',
    'finished_with_winner'
);


ALTER TYPE public.issue_state OWNER TO "www-data";

--
-- Name: TYPE issue_state; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE issue_state IS 'State of issues';


--
-- Name: member_image_type; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE member_image_type AS ENUM (
    'photo',
    'avatar'
);


ALTER TYPE public.member_image_type OWNER TO "www-data";

--
-- Name: TYPE member_image_type; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE member_image_type IS 'Types of images for a member';


--
-- Name: notify_level; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE notify_level AS ENUM (
    'none',
    'voting',
    'verification',
    'discussion',
    'all'
);


ALTER TYPE public.notify_level OWNER TO "www-data";

--
-- Name: TYPE notify_level; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE notify_level IS 'Level of notification: ''none'' = no notifications, ''voting'' = notifications about finished issues and issues in voting, ''verification'' = notifications about finished issues, issues in voting and verification phase, ''discussion'' = notifications about everything except issues in admission phase, ''all'' = notifications about everything';


--
-- Name: snapshot_event; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE snapshot_event AS ENUM (
    'periodic',
    'end_of_admission',
    'half_freeze',
    'full_freeze'
);


ALTER TYPE public.snapshot_event OWNER TO "www-data";

--
-- Name: TYPE snapshot_event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE snapshot_event IS 'Reason for snapshots: ''periodic'' = due to periodic recalculation, ''end_of_admission'' = saved state at end of admission period, ''half_freeze'' = saved state at end of discussion period, ''full_freeze'' = saved state at end of verification period';


--
-- Name: timeline_event; Type: TYPE; Schema: public; Owner: www-data
--

CREATE TYPE timeline_event AS ENUM (
    'issue_created',
    'issue_canceled',
    'issue_accepted',
    'issue_half_frozen',
    'issue_finished_without_voting',
    'issue_voting_started',
    'issue_finished_after_voting',
    'initiative_created',
    'initiative_revoked',
    'draft_created',
    'suggestion_created'
);


ALTER TYPE public.timeline_event OWNER TO "www-data";

--
-- Name: TYPE timeline_event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TYPE timeline_event IS 'Types of event in timeline tables (DEPRECATED)';


--
-- Name: add_vote_delegations(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION add_vote_delegations(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      FOR "member_id_v" IN
        SELECT "member_id" FROM "direct_voter"
        WHERE "issue_id" = "issue_id_p"
      LOOP
        UPDATE "direct_voter" SET
          "weight" = "weight" + "weight_of_added_vote_delegations"(
            "issue_id_p",
            "member_id_v",
            '{}'
          )
          WHERE "member_id" = "member_id_v"
          AND "issue_id" = "issue_id_p";
      END LOOP;
      RETURN;
    END;
  $$;


ALTER FUNCTION public.add_vote_delegations(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION add_vote_delegations(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION add_vote_delegations(issue_id_p integer) IS 'Helper function for "close_voting" function';


--
-- Name: autocreate_interest_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION autocreate_interest_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NOT EXISTS (
        SELECT NULL FROM "initiative" JOIN "interest"
        ON "initiative"."issue_id" = "interest"."issue_id"
        WHERE "initiative"."id" = NEW."initiative_id"
        AND "interest"."member_id" = NEW."member_id"
      ) THEN
        BEGIN
          INSERT INTO "interest" ("issue_id", "member_id")
            SELECT "issue_id", NEW."member_id"
            FROM "initiative" WHERE "id" = NEW."initiative_id";
        EXCEPTION WHEN unique_violation THEN END;
      END IF;
      RETURN NEW;
    END;
  $$;


ALTER FUNCTION public.autocreate_interest_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION autocreate_interest_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION autocreate_interest_trigger() IS 'Implementation of trigger "autocreate_interest" on table "supporter"';


--
-- Name: autocreate_supporter_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION autocreate_supporter_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NOT EXISTS (
        SELECT NULL FROM "suggestion" JOIN "supporter"
        ON "suggestion"."initiative_id" = "supporter"."initiative_id"
        WHERE "suggestion"."id" = NEW."suggestion_id"
        AND "supporter"."member_id" = NEW."member_id"
      ) THEN
        BEGIN
          INSERT INTO "supporter" ("initiative_id", "member_id")
            SELECT "initiative_id", NEW."member_id"
            FROM "suggestion" WHERE "id" = NEW."suggestion_id";
        EXCEPTION WHEN unique_violation THEN END;
      END IF;
      RETURN NEW;
    END;
  $$;


ALTER FUNCTION public.autocreate_supporter_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION autocreate_supporter_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION autocreate_supporter_trigger() IS 'Implementation of trigger "autocreate_supporter" on table "opinion"';


--
-- Name: autofill_initiative_id_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION autofill_initiative_id_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NEW."initiative_id" ISNULL THEN
        SELECT "initiative_id" INTO NEW."initiative_id"
          FROM "suggestion" WHERE "id" = NEW."suggestion_id";
      END IF;
      RETURN NEW;
    END;
  $$;


ALTER FUNCTION public.autofill_initiative_id_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION autofill_initiative_id_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION autofill_initiative_id_trigger() IS 'Implementation of trigger "autofill_initiative_id" on table "opinion"';


--
-- Name: autofill_issue_id_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION autofill_issue_id_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NEW."issue_id" ISNULL THEN
        SELECT "issue_id" INTO NEW."issue_id"
          FROM "initiative" WHERE "id" = NEW."initiative_id";
      END IF;
      RETURN NEW;
    END;
  $$;


ALTER FUNCTION public.autofill_issue_id_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION autofill_issue_id_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION autofill_issue_id_trigger() IS 'Implementation of triggers "autofill_issue_id" on tables "supporter" and "vote"';


--
-- Name: calculate_member_counts(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION calculate_member_counts() RETURNS void
    LANGUAGE plpgsql
    AS $$
    BEGIN
      LOCK TABLE "member"       IN SHARE MODE;
      LOCK TABLE "member_count" IN EXCLUSIVE MODE;
      LOCK TABLE "unit"         IN EXCLUSIVE MODE;
      LOCK TABLE "area"         IN EXCLUSIVE MODE;
      LOCK TABLE "privilege"    IN SHARE MODE;
      LOCK TABLE "membership"   IN SHARE MODE;
      DELETE FROM "member_count";
      INSERT INTO "member_count" ("total_count")
        SELECT "total_count" FROM "member_count_view";
      UPDATE "unit" SET "member_count" = "view"."member_count"
        FROM "unit_member_count" AS "view"
        WHERE "view"."unit_id" = "unit"."id";
      UPDATE "area" SET
        "direct_member_count" = "view"."direct_member_count",
        "member_weight"       = "view"."member_weight"
        FROM "area_member_count" AS "view"
        WHERE "view"."area_id" = "area"."id";
      RETURN;
    END;
  $$;


ALTER FUNCTION public.calculate_member_counts() OWNER TO "www-data";

--
-- Name: FUNCTION calculate_member_counts(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION calculate_member_counts() IS 'Updates "member_count" table and "member_count" column of table "area" by materializing data from views "member_count_view" and "area_member_count"';


--
-- Name: calculate_ranks(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION calculate_ranks(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_row"         "issue"%ROWTYPE;
      "policy_row"        "policy"%ROWTYPE;
      "dimension_v"       INTEGER;
      "vote_matrix"       INT4[][];  -- absolute votes
      "matrix"            INT8[][];  -- defeat strength / best paths
      "i"                 INTEGER;
      "j"                 INTEGER;
      "k"                 INTEGER;
      "battle_row"        "battle"%ROWTYPE;
      "rank_ary"          INT4[];
      "rank_v"            INT4;
      "done_v"            INTEGER;
      "winners_ary"       INTEGER[];
      "initiative_id_v"   "initiative"."id"%TYPE;
    BEGIN
      SELECT * INTO "issue_row"
        FROM "issue" WHERE "id" = "issue_id_p"
        FOR UPDATE;
      SELECT * INTO "policy_row"
        FROM "policy" WHERE "id" = "issue_row"."policy_id";
      SELECT count(1) INTO "dimension_v"
        FROM "battle_participant" WHERE "issue_id" = "issue_id_p";
      -- Create "vote_matrix" with absolute number of votes in pairwise
      -- comparison:
      "vote_matrix" := array_fill(NULL::INT4, ARRAY["dimension_v", "dimension_v"]);
      "i" := 1;
      "j" := 2;
      FOR "battle_row" IN
        SELECT * FROM "battle" WHERE "issue_id" = "issue_id_p"
        ORDER BY
        "winning_initiative_id" NULLS LAST,
        "losing_initiative_id" NULLS LAST
      LOOP
        "vote_matrix"["i"]["j"] := "battle_row"."count";
        IF "j" = "dimension_v" THEN
          "i" := "i" + 1;
          "j" := 1;
        ELSE
          "j" := "j" + 1;
          IF "j" = "i" THEN
            "j" := "j" + 1;
          END IF;
        END IF;
      END LOOP;
      IF "i" != "dimension_v" OR "j" != "dimension_v" + 1 THEN
        RAISE EXCEPTION 'Wrong battle count (should not happen)';
      END IF;
      -- Store defeat strengths in "matrix" using "defeat_strength"
      -- function:
      "matrix" := array_fill(NULL::INT8, ARRAY["dimension_v", "dimension_v"]);
      "i" := 1;
      LOOP
        "j" := 1;
        LOOP
          IF "i" != "j" THEN
            "matrix"["i"]["j"] := "defeat_strength"(
              "vote_matrix"["i"]["j"],
              "vote_matrix"["j"]["i"]
            );
          END IF;
          EXIT WHEN "j" = "dimension_v";
          "j" := "j" + 1;
        END LOOP;
        EXIT WHEN "i" = "dimension_v";
        "i" := "i" + 1;
      END LOOP;
      -- Find best paths:
      "i" := 1;
      LOOP
        "j" := 1;
        LOOP
          IF "i" != "j" THEN
            "k" := 1;
            LOOP
              IF "i" != "k" AND "j" != "k" THEN
                IF "matrix"["j"]["i"] < "matrix"["i"]["k"] THEN
                  IF "matrix"["j"]["i"] > "matrix"["j"]["k"] THEN
                    "matrix"["j"]["k"] := "matrix"["j"]["i"];
                  END IF;
                ELSE
                  IF "matrix"["i"]["k"] > "matrix"["j"]["k"] THEN
                    "matrix"["j"]["k"] := "matrix"["i"]["k"];
                  END IF;
                END IF;
              END IF;
              EXIT WHEN "k" = "dimension_v";
              "k" := "k" + 1;
            END LOOP;
          END IF;
          EXIT WHEN "j" = "dimension_v";
          "j" := "j" + 1;
        END LOOP;
        EXIT WHEN "i" = "dimension_v";
        "i" := "i" + 1;
      END LOOP;
      -- Determine order of winners:
      "rank_ary" := array_fill(NULL::INT4, ARRAY["dimension_v"]);
      "rank_v" := 1;
      "done_v" := 0;
      LOOP
        "winners_ary" := '{}';
        "i" := 1;
        LOOP
          IF "rank_ary"["i"] ISNULL THEN
            "j" := 1;
            LOOP
              IF
                "i" != "j" AND
                "rank_ary"["j"] ISNULL AND
                "matrix"["j"]["i"] > "matrix"["i"]["j"]
              THEN
                -- someone else is better
                EXIT;
              END IF;
              IF "j" = "dimension_v" THEN
                -- noone is better
                "winners_ary" := "winners_ary" || "i";
                EXIT;
              END IF;
              "j" := "j" + 1;
            END LOOP;
          END IF;
          EXIT WHEN "i" = "dimension_v";
          "i" := "i" + 1;
        END LOOP;
        "i" := 1;
        LOOP
          "rank_ary"["winners_ary"["i"]] := "rank_v";
          "done_v" := "done_v" + 1;
          EXIT WHEN "i" = array_upper("winners_ary", 1);
          "i" := "i" + 1;
        END LOOP;
        EXIT WHEN "done_v" = "dimension_v";
        "rank_v" := "rank_v" + 1;
      END LOOP;
      -- write preliminary results:
      "i" := 1;
      FOR "initiative_id_v" IN
        SELECT "id" FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "admitted"
        ORDER BY "id"
      LOOP
        UPDATE "initiative" SET
          "direct_majority" =
            CASE WHEN "policy_row"."direct_majority_strict" THEN
              "positive_votes" * "policy_row"."direct_majority_den" >
              "policy_row"."direct_majority_num" * ("positive_votes"+"negative_votes")
            ELSE
              "positive_votes" * "policy_row"."direct_majority_den" >=
              "policy_row"."direct_majority_num" * ("positive_votes"+"negative_votes")
            END
            AND "positive_votes" >= "policy_row"."direct_majority_positive"
            AND "issue_row"."voter_count"-"negative_votes" >=
                "policy_row"."direct_majority_non_negative",
            "indirect_majority" =
            CASE WHEN "policy_row"."indirect_majority_strict" THEN
              "positive_votes" * "policy_row"."indirect_majority_den" >
              "policy_row"."indirect_majority_num" * ("positive_votes"+"negative_votes")
            ELSE
              "positive_votes" * "policy_row"."indirect_majority_den" >=
              "policy_row"."indirect_majority_num" * ("positive_votes"+"negative_votes")
            END
            AND "positive_votes" >= "policy_row"."indirect_majority_positive"
            AND "issue_row"."voter_count"-"negative_votes" >=
                "policy_row"."indirect_majority_non_negative",
          "schulze_rank"           = "rank_ary"["i"],
          "better_than_status_quo" = "rank_ary"["i"] < "rank_ary"["dimension_v"],
          "worse_than_status_quo"  = "rank_ary"["i"] > "rank_ary"["dimension_v"],
          "multistage_majority"    = "rank_ary"["i"] >= "rank_ary"["dimension_v"],
          "reverse_beat_path"      = "matrix"["dimension_v"]["i"] >= 0,
          "eligible"               = FALSE,
          "winner"                 = FALSE,
          "rank"                   = NULL  -- NOTE: in cases of manual reset of issue state
          WHERE "id" = "initiative_id_v";
        "i" := "i" + 1;
      END LOOP;
      IF "i" != "dimension_v" THEN
        RAISE EXCEPTION 'Wrong winner count (should not happen)';
      END IF;
      -- take indirect majorities into account:
      LOOP
        UPDATE "initiative" SET "indirect_majority" = TRUE
          FROM (
            SELECT "new_initiative"."id" AS "initiative_id"
            FROM "initiative" "old_initiative"
            JOIN "initiative" "new_initiative"
              ON "new_initiative"."issue_id" = "issue_id_p"
              AND "new_initiative"."indirect_majority" = FALSE
            JOIN "battle" "battle_win"
              ON "battle_win"."issue_id" = "issue_id_p"
              AND "battle_win"."winning_initiative_id" = "new_initiative"."id"
              AND "battle_win"."losing_initiative_id" = "old_initiative"."id"
            JOIN "battle" "battle_lose"
              ON "battle_lose"."issue_id" = "issue_id_p"
              AND "battle_lose"."losing_initiative_id" = "new_initiative"."id"
              AND "battle_lose"."winning_initiative_id" = "old_initiative"."id"
            WHERE "old_initiative"."issue_id" = "issue_id_p"
            AND "old_initiative"."indirect_majority" = TRUE
            AND CASE WHEN "policy_row"."indirect_majority_strict" THEN
              "battle_win"."count" * "policy_row"."indirect_majority_den" >
              "policy_row"."indirect_majority_num" *
              ("battle_win"."count"+"battle_lose"."count")
            ELSE
              "battle_win"."count" * "policy_row"."indirect_majority_den" >=
              "policy_row"."indirect_majority_num" *
              ("battle_win"."count"+"battle_lose"."count")
            END
            AND "battle_win"."count" >= "policy_row"."indirect_majority_positive"
            AND "issue_row"."voter_count"-"battle_lose"."count" >=
                "policy_row"."indirect_majority_non_negative"
          ) AS "subquery"
          WHERE "id" = "subquery"."initiative_id";
        EXIT WHEN NOT FOUND;
      END LOOP;
      -- set "multistage_majority" for remaining matching initiatives:
      UPDATE "initiative" SET "multistage_majority" = TRUE
        FROM (
          SELECT "losing_initiative"."id" AS "initiative_id"
          FROM "initiative" "losing_initiative"
          JOIN "initiative" "winning_initiative"
            ON "winning_initiative"."issue_id" = "issue_id_p"
            AND "winning_initiative"."admitted"
          JOIN "battle" "battle_win"
            ON "battle_win"."issue_id" = "issue_id_p"
            AND "battle_win"."winning_initiative_id" = "winning_initiative"."id"
            AND "battle_win"."losing_initiative_id" = "losing_initiative"."id"
          JOIN "battle" "battle_lose"
            ON "battle_lose"."issue_id" = "issue_id_p"
            AND "battle_lose"."losing_initiative_id" = "winning_initiative"."id"
            AND "battle_lose"."winning_initiative_id" = "losing_initiative"."id"
          WHERE "losing_initiative"."issue_id" = "issue_id_p"
          AND "losing_initiative"."admitted"
          AND "winning_initiative"."schulze_rank" <
              "losing_initiative"."schulze_rank"
          AND "battle_win"."count" > "battle_lose"."count"
          AND (
            "battle_win"."count" > "winning_initiative"."positive_votes" OR
            "battle_lose"."count" < "losing_initiative"."negative_votes" )
        ) AS "subquery"
        WHERE "id" = "subquery"."initiative_id";
      -- mark eligible initiatives:
      UPDATE "initiative" SET "eligible" = TRUE
        WHERE "issue_id" = "issue_id_p"
        AND "initiative"."direct_majority"
        AND "initiative"."indirect_majority"
        AND "initiative"."better_than_status_quo"
        AND (
          "policy_row"."no_multistage_majority" = FALSE OR
          "initiative"."multistage_majority" = FALSE )
        AND (
          "policy_row"."no_reverse_beat_path" = FALSE OR
          "initiative"."reverse_beat_path" = FALSE );
      -- mark final winner:
      UPDATE "initiative" SET "winner" = TRUE
        FROM (
          SELECT "id" AS "initiative_id"
          FROM "initiative"
          WHERE "issue_id" = "issue_id_p" AND "eligible"
          ORDER BY
            "schulze_rank",
            "vote_ratio"("positive_votes", "negative_votes"),
            "id"
          LIMIT 1
        ) AS "subquery"
        WHERE "id" = "subquery"."initiative_id";
      -- write (final) ranks:
      "rank_v" := 1;
      FOR "initiative_id_v" IN
        SELECT "id"
        FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "admitted"
        ORDER BY
          "winner" DESC,
          "eligible" DESC,
          "schulze_rank",
          "vote_ratio"("positive_votes", "negative_votes"),
          "id"
      LOOP
        UPDATE "initiative" SET "rank" = "rank_v"
          WHERE "id" = "initiative_id_v";
        "rank_v" := "rank_v" + 1;
      END LOOP;
      -- set schulze rank of status quo and mark issue as finished:
      UPDATE "issue" SET
        "status_quo_schulze_rank" = "rank_ary"["dimension_v"],
        "state" =
          CASE WHEN EXISTS (
            SELECT NULL FROM "initiative"
            WHERE "issue_id" = "issue_id_p" AND "winner"
          ) THEN
            'finished_with_winner'::"issue_state"
          ELSE
            'finished_without_winner'::"issue_state"
          END,
        "ranks_available" = TRUE
        WHERE "id" = "issue_id_p";
      RETURN;
    END;
  $$;


ALTER FUNCTION public.calculate_ranks(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION calculate_ranks(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION calculate_ranks(issue_id_p integer) IS 'Determine ranking (Votes have to be counted first)';


--
-- Name: check_activity(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION check_activity() RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "system_setting_row" "system_setting"%ROWTYPE;
    BEGIN
      SELECT * INTO "system_setting_row" FROM "system_setting";
      LOCK TABLE "member" IN SHARE ROW EXCLUSIVE MODE;
      IF "system_setting_row"."member_ttl" NOTNULL THEN
        UPDATE "member" SET "active" = FALSE
          WHERE "active" = TRUE
          AND "last_activity" < (now() - "system_setting_row"."member_ttl")::DATE;
      END IF;
      RETURN;
    END;
  $$;


ALTER FUNCTION public.check_activity() OWNER TO "www-data";

--
-- Name: FUNCTION check_activity(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION check_activity() IS 'Deactivates members when "last_activity" is older than "system_setting"."member_ttl".';


--
-- Name: check_everything(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION check_everything() RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_id_v" "issue"."id"%TYPE;
    BEGIN
      DELETE FROM "expired_session";
      PERFORM "check_activity"();
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


ALTER FUNCTION public.check_everything() OWNER TO "www-data";

--
-- Name: FUNCTION check_everything(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION check_everything() IS 'Amongst other regular tasks this function performs "check_issue" for every open issue, and if possible, automatically calculates ranks. Use this function only for development and debugging purposes, as long transactions with exclusive locking may result. In productive environments you should call the lf_update program instead.';


--
-- Name: check_issue(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION check_issue(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_row"         "issue"%ROWTYPE;
      "policy_row"        "policy"%ROWTYPE;
    BEGIN
      PERFORM "lock_issue"("issue_id_p");
      SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
      -- only process open issues:
      IF "issue_row"."closed" ISNULL THEN
        SELECT * INTO "policy_row" FROM "policy"
          WHERE "id" = "issue_row"."policy_id";
        -- create a snapshot, unless issue is already fully frozen:
        IF "issue_row"."fully_frozen" ISNULL THEN
          PERFORM "create_snapshot"("issue_id_p");
          SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
        END IF;
        -- eventually close or accept issues, which have not been accepted:
        IF "issue_row"."accepted" ISNULL THEN
          IF EXISTS (
            SELECT NULL FROM "initiative"
            WHERE "issue_id" = "issue_id_p"
            AND "supporter_count" > 0
            AND "supporter_count" * "policy_row"."issue_quorum_den"
            >= "issue_row"."population" * "policy_row"."issue_quorum_num"
          ) THEN
            -- accept issues, if supporter count is high enough
            PERFORM "set_snapshot_event"("issue_id_p", 'end_of_admission');
            -- NOTE: "issue_row" used later
            "issue_row"."state" := 'discussion';
            "issue_row"."accepted" := now();
            UPDATE "issue" SET
              "state"    = "issue_row"."state",
              "accepted" = "issue_row"."accepted"
              WHERE "id" = "issue_row"."id";
          ELSIF
            now() >= "issue_row"."created" + "issue_row"."admission_time"
          THEN
            -- close issues, if admission time has expired
            PERFORM "set_snapshot_event"("issue_id_p", 'end_of_admission');
            UPDATE "issue" SET
              "state" = 'canceled_issue_not_accepted',
              "closed" = now()
              WHERE "id" = "issue_row"."id";
          END IF;
        END IF;
        -- eventually half freeze issues:
        IF
          -- NOTE: issue can't be closed at this point, if it has been accepted
          "issue_row"."accepted" NOTNULL AND
          "issue_row"."half_frozen" ISNULL
        THEN
          IF
            now() >= "issue_row"."accepted" + "issue_row"."discussion_time"
          THEN
            PERFORM "set_snapshot_event"("issue_id_p", 'half_freeze');
            -- NOTE: "issue_row" used later
            "issue_row"."state" := 'verification';
            "issue_row"."half_frozen" := now();
            UPDATE "issue" SET
              "state"       = "issue_row"."state",
              "half_frozen" = "issue_row"."half_frozen"
              WHERE "id" = "issue_row"."id";
          END IF;
        END IF;
        -- close issues after some time, if all initiatives have been revoked:
        IF
          "issue_row"."closed" ISNULL AND
          NOT EXISTS (
            -- all initiatives are revoked
            SELECT NULL FROM "initiative"
            WHERE "issue_id" = "issue_id_p" AND "revoked" ISNULL
          ) AND (
            -- and issue has not been accepted yet
            "issue_row"."accepted" ISNULL OR
            NOT EXISTS (
              -- or no initiatives have been revoked lately
              SELECT NULL FROM "initiative"
              WHERE "issue_id" = "issue_id_p"
              AND now() < "revoked" + "issue_row"."verification_time"
            ) OR (
              -- or verification time has elapsed
              "issue_row"."half_frozen" NOTNULL AND
              "issue_row"."fully_frozen" ISNULL AND
              now() >= "issue_row"."half_frozen" + "issue_row"."verification_time"
            )
          )
        THEN
          -- NOTE: "issue_row" used later
          IF "issue_row"."accepted" ISNULL THEN
            "issue_row"."state" := 'canceled_revoked_before_accepted';
          ELSIF "issue_row"."half_frozen" ISNULL THEN
            "issue_row"."state" := 'canceled_after_revocation_during_discussion';
          ELSE
            "issue_row"."state" := 'canceled_after_revocation_during_verification';
          END IF;
          "issue_row"."closed" := now();
          UPDATE "issue" SET
            "state"  = "issue_row"."state",
            "closed" = "issue_row"."closed"
            WHERE "id" = "issue_row"."id";
        END IF;
        -- fully freeze issue after verification time:
        IF
          "issue_row"."half_frozen" NOTNULL AND
          "issue_row"."fully_frozen" ISNULL AND
          "issue_row"."closed" ISNULL AND
          now() >= "issue_row"."half_frozen" + "issue_row"."verification_time"
        THEN
          PERFORM "freeze_after_snapshot"("issue_id_p");
          -- NOTE: "issue" might change, thus "issue_row" has to be updated below
        END IF;
        SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
        -- close issue by calling close_voting(...) after voting time:
        IF
          "issue_row"."closed" ISNULL AND
          "issue_row"."fully_frozen" NOTNULL AND
          now() >= "issue_row"."fully_frozen" + "issue_row"."voting_time"
        THEN
          PERFORM "close_voting"("issue_id_p");
          -- calculate ranks will not consume much time and can be done now
          PERFORM "calculate_ranks"("issue_id_p");
        END IF;
      END IF;
      RETURN;
    END;
  $$;


ALTER FUNCTION public.check_issue(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION check_issue(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION check_issue(issue_id_p integer) IS 'Precalculate supporter counts etc. for a given issue, and check, if status change is required; At end of voting the ranking is not calculated by this function, but must be calculated in a seperate transaction using the "calculate_ranks" function.';


--
-- Name: clean_issue(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION clean_issue(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_row" "issue"%ROWTYPE;
    BEGIN
      SELECT * INTO "issue_row"
        FROM "issue" WHERE "id" = "issue_id_p"
        FOR UPDATE;
      IF "issue_row"."cleaned" ISNULL THEN
        UPDATE "issue" SET
          "state"           = 'voting',
          "closed"          = NULL,
          "ranks_available" = FALSE
          WHERE "id" = "issue_id_p";
        DELETE FROM "issue_comment"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "voting_comment"
          WHERE "issue_id" = "issue_id_p";
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
        DELETE FROM "non_voter"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "delegation"
          WHERE "issue_id" = "issue_id_p";
        DELETE FROM "supporter"
          WHERE "issue_id" = "issue_id_p";
        UPDATE "issue" SET
          "state"           = "issue_row"."state",
          "closed"          = "issue_row"."closed",
          "ranks_available" = "issue_row"."ranks_available",
          "cleaned"         = now()
          WHERE "id" = "issue_id_p";
      END IF;
      RETURN;
    END;
  $$;


ALTER FUNCTION public.clean_issue(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION clean_issue(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION clean_issue(issue_id_p integer) IS 'Delete discussion data and votes belonging to an issue';


--
-- Name: close_voting(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION close_voting(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "area_id_v"   "area"."id"%TYPE;
      "unit_id_v"   "unit"."id"%TYPE;
      "member_id_v" "member"."id"%TYPE;
    BEGIN
      PERFORM "lock_issue"("issue_id_p");
      SELECT "area_id" INTO "area_id_v" FROM "issue" WHERE "id" = "issue_id_p";
      SELECT "unit_id" INTO "unit_id_v" FROM "area"  WHERE "id" = "area_id_v";
      -- delete delegating votes (in cases of manual reset of issue state):
      DELETE FROM "delegating_voter"
        WHERE "issue_id" = "issue_id_p";
      -- delete votes from non-privileged voters:
      DELETE FROM "direct_voter"
        USING (
          SELECT
            "direct_voter"."member_id"
          FROM "direct_voter"
          JOIN "member" ON "direct_voter"."member_id" = "member"."id"
          LEFT JOIN "privilege"
          ON "privilege"."unit_id" = "unit_id_v"
          AND "privilege"."member_id" = "direct_voter"."member_id"
          WHERE "direct_voter"."issue_id" = "issue_id_p" AND (
            "member"."active" = FALSE OR
            "privilege"."voting_right" ISNULL OR
            "privilege"."voting_right" = FALSE
          )
        ) AS "subquery"
        WHERE "direct_voter"."issue_id" = "issue_id_p"
        AND "direct_voter"."member_id" = "subquery"."member_id";
      -- consider delegations:
      UPDATE "direct_voter" SET "weight" = 1
        WHERE "issue_id" = "issue_id_p";
      PERFORM "add_vote_delegations"("issue_id_p");
      -- set voter count and mark issue as being calculated:
      UPDATE "issue" SET
        "state"  = 'calculation',
        "closed" = now(),
        "voter_count" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_voter" WHERE "issue_id" = "issue_id_p"
        )
        WHERE "id" = "issue_id_p";
      -- materialize battle_view:
      -- NOTE: "closed" column of issue must be set at this point
      DELETE FROM "battle" WHERE "issue_id" = "issue_id_p";
      INSERT INTO "battle" (
        "issue_id",
        "winning_initiative_id", "losing_initiative_id",
        "count"
      ) SELECT
        "issue_id",
        "winning_initiative_id", "losing_initiative_id",
        "count"
        FROM "battle_view" WHERE "issue_id" = "issue_id_p";
      -- copy "positive_votes" and "negative_votes" from "battle" table:
      UPDATE "initiative" SET
        "positive_votes" = "battle_win"."count",
        "negative_votes" = "battle_lose"."count"
        FROM "battle" AS "battle_win", "battle" AS "battle_lose"
        WHERE
          "battle_win"."issue_id" = "issue_id_p" AND
          "battle_win"."winning_initiative_id" = "initiative"."id" AND
          "battle_win"."losing_initiative_id" ISNULL AND
          "battle_lose"."issue_id" = "issue_id_p" AND
          "battle_lose"."losing_initiative_id" = "initiative"."id" AND
          "battle_lose"."winning_initiative_id" ISNULL;
    END;
  $$;


ALTER FUNCTION public.close_voting(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION close_voting(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION close_voting(issue_id_p integer) IS 'Closes the voting on an issue, and calculates positive and negative votes for each initiative; The ranking is not calculated yet, to keep the (locking) transaction short.';


--
-- Name: copy_timings_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION copy_timings_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "policy_row" "policy"%ROWTYPE;
    BEGIN
      SELECT * INTO "policy_row" FROM "policy"
        WHERE "id" = NEW."policy_id";
      IF NEW."admission_time" ISNULL THEN
        NEW."admission_time" := "policy_row"."admission_time";
      END IF;
      IF NEW."discussion_time" ISNULL THEN
        NEW."discussion_time" := "policy_row"."discussion_time";
      END IF;
      IF NEW."verification_time" ISNULL THEN
        NEW."verification_time" := "policy_row"."verification_time";
      END IF;
      IF NEW."voting_time" ISNULL THEN
        NEW."voting_time" := "policy_row"."voting_time";
      END IF;
      RETURN NEW;
    END;
  $$;


ALTER FUNCTION public.copy_timings_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION copy_timings_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION copy_timings_trigger() IS 'Implementation of trigger "copy_timings" on table "issue"';


--
-- Name: create_interest_snapshot(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION create_interest_snapshot(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
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
        ("issue_id", "event", "member_id")
        SELECT
          "issue_id_p"  AS "issue_id",
          'periodic'    AS "event",
          "member"."id" AS "member_id"
        FROM "issue"
        JOIN "area" ON "issue"."area_id" = "area"."id"
        JOIN "interest" ON "issue"."id" = "interest"."issue_id"
        JOIN "member" ON "interest"."member_id" = "member"."id"
        JOIN "privilege"
          ON "privilege"."unit_id" = "area"."unit_id"
          AND "privilege"."member_id" = "member"."id"
        WHERE "issue"."id" = "issue_id_p"
        AND "member"."active" AND "privilege"."voting_right";
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
          "draft_id", "informed", "satisfied" )
        SELECT
          "issue_id_p"            AS "issue_id",
          "initiative"."id"       AS "initiative_id",
          'periodic'              AS "event",
          "supporter"."member_id" AS "member_id",
          "supporter"."draft_id"  AS "draft_id",
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


ALTER FUNCTION public.create_interest_snapshot(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION create_interest_snapshot(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION create_interest_snapshot(issue_id_p integer) IS 'This function creates a new ''periodic'' interest/supporter snapshot for the given issue. It does neither lock any tables, nor updates precalculated values in other tables.';


--
-- Name: create_population_snapshot(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION create_population_snapshot(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
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
        JOIN "privilege"
          ON "privilege"."unit_id" = "area"."unit_id"
          AND "privilege"."member_id" = "member"."id"
        WHERE "issue"."id" = "issue_id_p"
        AND "member"."active" AND "privilege"."voting_right"
        UNION
        SELECT
          "issue_id_p"                 AS "issue_id",
          'periodic'::"snapshot_event" AS "event",
          "member"."id"                AS "member_id"
        FROM "issue"
        JOIN "area" ON "issue"."area_id" = "area"."id"
        JOIN "interest" ON "issue"."id" = "interest"."issue_id"
        JOIN "member" ON "interest"."member_id" = "member"."id"
        JOIN "privilege"
          ON "privilege"."unit_id" = "area"."unit_id"
          AND "privilege"."member_id" = "member"."id"
        WHERE "issue"."id" = "issue_id_p"
        AND "member"."active" AND "privilege"."voting_right";
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


ALTER FUNCTION public.create_population_snapshot(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION create_population_snapshot(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION create_population_snapshot(issue_id_p integer) IS 'This function creates a new ''periodic'' population snapshot for the given issue. It does neither lock any tables, nor updates precalculated values in other tables.';


--
-- Name: create_snapshot(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION create_snapshot(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "initiative_id_v"    "initiative"."id"%TYPE;
      "suggestion_id_v"    "suggestion"."id"%TYPE;
    BEGIN
      PERFORM "lock_issue"("issue_id_p");
      PERFORM "create_population_snapshot"("issue_id_p");
      PERFORM "create_interest_snapshot"("issue_id_p");
      UPDATE "issue" SET
        "snapshot" = now(),
        "latest_snapshot_event" = 'periodic',
        "population" = (
          SELECT coalesce(sum("weight"), 0)
          FROM "direct_population_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
        )
        WHERE "id" = "issue_id_p";
      FOR "initiative_id_v" IN
        SELECT "id" FROM "initiative" WHERE "issue_id" = "issue_id_p"
      LOOP
        UPDATE "initiative" SET
          "supporter_count" = (
            SELECT coalesce(sum("di"."weight"), 0)
            FROM "direct_interest_snapshot" AS "di"
            JOIN "direct_supporter_snapshot" AS "ds"
            ON "di"."member_id" = "ds"."member_id"
            WHERE "di"."issue_id" = "issue_id_p"
            AND "di"."event" = 'periodic'
            AND "ds"."initiative_id" = "initiative_id_v"
            AND "ds"."event" = 'periodic'
          ),
          "informed_supporter_count" = (
            SELECT coalesce(sum("di"."weight"), 0)
            FROM "direct_interest_snapshot" AS "di"
            JOIN "direct_supporter_snapshot" AS "ds"
            ON "di"."member_id" = "ds"."member_id"
            WHERE "di"."issue_id" = "issue_id_p"
            AND "di"."event" = 'periodic'
            AND "ds"."initiative_id" = "initiative_id_v"
            AND "ds"."event" = 'periodic'
            AND "ds"."informed"
          ),
          "satisfied_supporter_count" = (
            SELECT coalesce(sum("di"."weight"), 0)
            FROM "direct_interest_snapshot" AS "di"
            JOIN "direct_supporter_snapshot" AS "ds"
            ON "di"."member_id" = "ds"."member_id"
            WHERE "di"."issue_id" = "issue_id_p"
            AND "di"."event" = 'periodic'
            AND "ds"."initiative_id" = "initiative_id_v"
            AND "ds"."event" = 'periodic'
            AND "ds"."satisfied"
          ),
          "satisfied_informed_supporter_count" = (
            SELECT coalesce(sum("di"."weight"), 0)
            FROM "direct_interest_snapshot" AS "di"
            JOIN "direct_supporter_snapshot" AS "ds"
            ON "di"."member_id" = "ds"."member_id"
            WHERE "di"."issue_id" = "issue_id_p"
            AND "di"."event" = 'periodic'
            AND "ds"."initiative_id" = "initiative_id_v"
            AND "ds"."event" = 'periodic'
            AND "ds"."informed"
            AND "ds"."satisfied"
          )
          WHERE "id" = "initiative_id_v";
        FOR "suggestion_id_v" IN
          SELECT "id" FROM "suggestion"
          WHERE "initiative_id" = "initiative_id_v"
        LOOP
          UPDATE "suggestion" SET
            "minus2_unfulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = -2
              AND "opinion"."fulfilled" = FALSE
            ),
            "minus2_fulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = -2
              AND "opinion"."fulfilled" = TRUE
            ),
            "minus1_unfulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = -1
              AND "opinion"."fulfilled" = FALSE
            ),
            "minus1_fulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = -1
              AND "opinion"."fulfilled" = TRUE
            ),
            "plus1_unfulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = 1
              AND "opinion"."fulfilled" = FALSE
            ),
            "plus1_fulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = 1
              AND "opinion"."fulfilled" = TRUE
            ),
            "plus2_unfulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = 2
              AND "opinion"."fulfilled" = FALSE
            ),
            "plus2_fulfilled_count" = (
              SELECT coalesce(sum("snapshot"."weight"), 0)
              FROM "issue" CROSS JOIN "opinion"
              JOIN "direct_interest_snapshot" AS "snapshot"
              ON "snapshot"."issue_id" = "issue"."id"
              AND "snapshot"."event" = "issue"."latest_snapshot_event"
              AND "snapshot"."member_id" = "opinion"."member_id"
              WHERE "issue"."id" = "issue_id_p"
              AND "opinion"."suggestion_id" = "suggestion_id_v"
              AND "opinion"."degree" = 2
              AND "opinion"."fulfilled" = TRUE
            )
            WHERE "suggestion"."id" = "suggestion_id_v";
        END LOOP;
      END LOOP;
      RETURN;
    END;
  $$;


ALTER FUNCTION public.create_snapshot(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION create_snapshot(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION create_snapshot(issue_id_p integer) IS 'This function creates a complete new ''periodic'' snapshot of population, interest and support for the given issue. All involved tables are locked, and after completion precalculated values in the source tables are updated.';


--
-- Name: default_for_draft_id_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION default_for_draft_id_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NEW."draft_id" ISNULL THEN
        SELECT "id" INTO NEW."draft_id" FROM "current_draft"
          WHERE "initiative_id" = NEW."initiative_id";
      END IF;
      RETURN NEW;
    END;
  $$;


ALTER FUNCTION public.default_for_draft_id_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION default_for_draft_id_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION default_for_draft_id_trigger() IS 'Implementation of trigger "default_for_draft" on tables "supporter" and "suggestion"';


--
-- Name: defeat_strength(integer, integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION defeat_strength(positive_votes_p integer, negative_votes_p integer) RETURNS bigint
    LANGUAGE plpgsql IMMUTABLE
    AS $$
    BEGIN
      IF "positive_votes_p" > "negative_votes_p" THEN
        RETURN ("positive_votes_p"::INT8 << 31) - "negative_votes_p"::INT8;
      ELSIF "positive_votes_p" = "negative_votes_p" THEN
        RETURN 0;
      ELSE
        RETURN -1;
      END IF;
    END;
  $$;


ALTER FUNCTION public.defeat_strength(positive_votes_p integer, negative_votes_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION defeat_strength(positive_votes_p integer, negative_votes_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION defeat_strength(positive_votes_p integer, negative_votes_p integer) IS 'Calculates defeat strength (INT8!) of a pairwise defeat primarily by the absolute number of votes for the winner and secondarily by the absolute number of votes for the loser';


--
-- Name: delegation_chain(integer, integer, integer, integer, integer, boolean); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION delegation_chain(member_id_p integer, unit_id_p integer, area_id_p integer, issue_id_p integer, simulate_trustee_id_p integer DEFAULT NULL::integer, simulate_default_p boolean DEFAULT false) RETURNS SETOF delegation_chain_row
    LANGUAGE plpgsql STABLE
    AS $$
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


ALTER FUNCTION public.delegation_chain(member_id_p integer, unit_id_p integer, area_id_p integer, issue_id_p integer, simulate_trustee_id_p integer, simulate_default_p boolean) OWNER TO "www-data";

--
-- Name: FUNCTION delegation_chain(member_id_p integer, unit_id_p integer, area_id_p integer, issue_id_p integer, simulate_trustee_id_p integer, simulate_default_p boolean); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION delegation_chain(member_id_p integer, unit_id_p integer, area_id_p integer, issue_id_p integer, simulate_trustee_id_p integer, simulate_default_p boolean) IS 'Shows a delegation chain for unit, area, or issue; See "delegation_chain_row" type for more information';


--
-- Name: delegation_chain_for_closed_issue(integer, integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION delegation_chain_for_closed_issue(member_id_p integer, issue_id_p integer) RETURNS SETOF delegation_chain_row
    LANGUAGE plpgsql STABLE
    AS $$
    DECLARE
      "output_row"           "delegation_chain_row";
      "direct_voter_row"     "direct_voter"%ROWTYPE;
      "delegating_voter_row" "delegating_voter"%ROWTYPE;
    BEGIN
      "output_row"."index"         := 0;
      "output_row"."member_id"     := "member_id_p";
      "output_row"."member_valid"  := TRUE;
      "output_row"."participation" := FALSE;
      "output_row"."overridden"    := FALSE;
      "output_row"."disabled_out"  := FALSE;
      LOOP
        SELECT INTO "direct_voter_row" * FROM "direct_voter"
          WHERE "issue_id" = "issue_id_p"
          AND "member_id" = "output_row"."member_id";
        IF "direct_voter_row"."member_id" NOTNULL THEN
          "output_row"."participation" := TRUE;
          "output_row"."scope_out"     := NULL;
          "output_row"."disabled_out"  := NULL;
          RETURN NEXT "output_row";
          RETURN;
        END IF;
        SELECT INTO "delegating_voter_row" * FROM "delegating_voter"
          WHERE "issue_id" = "issue_id_p"
          AND "member_id" = "output_row"."member_id";
        IF "delegating_voter_row"."member_id" ISNULL THEN
          RETURN;
        END IF;
        "output_row"."scope_out" := "delegating_voter_row"."scope";
        RETURN NEXT "output_row";
        "output_row"."member_id" := "delegating_voter_row"."delegate_member_ids"[1];
        "output_row"."scope_in"  := "output_row"."scope_out";
      END LOOP;
    END;
  $$;


ALTER FUNCTION public.delegation_chain_for_closed_issue(member_id_p integer, issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION delegation_chain_for_closed_issue(member_id_p integer, issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION delegation_chain_for_closed_issue(member_id_p integer, issue_id_p integer) IS 'Helper function for "delegation_chain" function, handling the special case of closed issues after voting';


--
-- Name: delegation_info(integer, integer, integer, integer, integer, boolean); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION delegation_info(member_id_p integer, unit_id_p integer, area_id_p integer, issue_id_p integer, simulate_trustee_id_p integer DEFAULT NULL::integer, simulate_default_p boolean DEFAULT false) RETURNS delegation_info_type
    LANGUAGE plpgsql STABLE
    AS $$
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


ALTER FUNCTION public.delegation_info(member_id_p integer, unit_id_p integer, area_id_p integer, issue_id_p integer, simulate_trustee_id_p integer, simulate_default_p boolean) OWNER TO "www-data";

--
-- Name: FUNCTION delegation_info(member_id_p integer, unit_id_p integer, area_id_p integer, issue_id_p integer, simulate_trustee_id_p integer, simulate_default_p boolean); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION delegation_info(member_id_p integer, unit_id_p integer, area_id_p integer, issue_id_p integer, simulate_trustee_id_p integer, simulate_default_p boolean) IS 'Notable information about a delegation chain for unit, area, or issue; See "delegation_info_type" for more information';


--
-- Name: delete_member(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION delete_member(member_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    BEGIN
      UPDATE "member" SET
        "last_login"                   = NULL,
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
      DELETE FROM "ignored_member"     WHERE "member_id" = "member_id_p";
      DELETE FROM "session"            WHERE "member_id" = "member_id_p";
      DELETE FROM "area_setting"       WHERE "member_id" = "member_id_p";
      DELETE FROM "issue_setting"      WHERE "member_id" = "member_id_p";
      DELETE FROM "ignored_initiative" WHERE "member_id" = "member_id_p";
      DELETE FROM "initiative_setting" WHERE "member_id" = "member_id_p";
      DELETE FROM "suggestion_setting" WHERE "member_id" = "member_id_p";
      DELETE FROM "membership"         WHERE "member_id" = "member_id_p";
      DELETE FROM "delegation"         WHERE "truster_id" = "member_id_p";
      DELETE FROM "non_voter"          WHERE "member_id" = "member_id_p";
      DELETE FROM "direct_voter" USING "issue"
        WHERE "direct_voter"."issue_id" = "issue"."id"
        AND "issue"."closed" ISNULL
        AND "member_id" = "member_id_p";
      RETURN;
    END;
  $$;


ALTER FUNCTION public.delete_member(member_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION delete_member(member_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION delete_member(member_id_p integer) IS 'Deactivate member and clear certain settings and data of this member (data protection)';


--
-- Name: delete_private_data(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION delete_private_data() RETURNS void
    LANGUAGE plpgsql
    AS $$
    BEGIN
      DELETE FROM "member" WHERE "activated" ISNULL;
      UPDATE "member" SET
        "invite_code"                  = NULL,
        "invite_code_expiry"           = NULL,
        "admin_comment"                = NULL,
        "last_login"                   = NULL,
        "login"                        = NULL,
        "password"                     = NULL,
        "lang"                         = NULL,
        "notify_email"                 = NULL,
        "notify_email_unconfirmed"     = NULL,
        "notify_email_secret"          = NULL,
        "notify_email_secret_expiry"   = NULL,
        "notify_email_lock_expiry"     = NULL,
        "notify_level"                 = NULL,
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
        "formatting_engine"            = NULL,
        "statement"                    = NULL;
      -- "text_search_data" is updated by triggers
      DELETE FROM "setting";
      DELETE FROM "setting_map";
      DELETE FROM "member_relation_setting";
      DELETE FROM "member_image";
      DELETE FROM "contact";
      DELETE FROM "ignored_member";
      DELETE FROM "session";
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


ALTER FUNCTION public.delete_private_data() OWNER TO "www-data";

--
-- Name: FUNCTION delete_private_data(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION delete_private_data() IS 'Used by lf_export script. DO NOT USE on productive database, but only on a copy! This function deletes all data which should not be publicly available, and can be used to create a database dump for publication.';


--
-- Name: forbid_changes_on_closed_issue_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION forbid_changes_on_closed_issue_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_id_v" "issue"."id"%TYPE;
      "issue_row"  "issue"%ROWTYPE;
    BEGIN
      IF TG_OP = 'DELETE' THEN
        "issue_id_v" := OLD."issue_id";
      ELSE
        "issue_id_v" := NEW."issue_id";
      END IF;
      SELECT INTO "issue_row" * FROM "issue"
        WHERE "id" = "issue_id_v" FOR SHARE;
      IF "issue_row"."closed" NOTNULL THEN
        RAISE EXCEPTION 'Tried to modify data belonging to a closed issue.';
      END IF;
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.forbid_changes_on_closed_issue_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION forbid_changes_on_closed_issue_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION forbid_changes_on_closed_issue_trigger() IS 'Implementation of triggers "forbid_changes_on_closed_issue" on tables "direct_voter", "delegating_voter" and "vote"';


--
-- Name: freeze_after_snapshot(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION freeze_after_snapshot(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_row"      "issue"%ROWTYPE;
      "policy_row"     "policy"%ROWTYPE;
      "initiative_row" "initiative"%ROWTYPE;
    BEGIN
      SELECT * INTO "issue_row" FROM "issue" WHERE "id" = "issue_id_p";
      SELECT * INTO "policy_row"
        FROM "policy" WHERE "id" = "issue_row"."policy_id";
      PERFORM "set_snapshot_event"("issue_id_p", 'full_freeze');
      FOR "initiative_row" IN
        SELECT * FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "revoked" ISNULL
      LOOP
        IF
          "initiative_row"."satisfied_supporter_count" > 0 AND
          "initiative_row"."satisfied_supporter_count" *
          "policy_row"."initiative_quorum_den" >=
          "issue_row"."population" * "policy_row"."initiative_quorum_num"
        THEN
          UPDATE "initiative" SET "admitted" = TRUE
            WHERE "id" = "initiative_row"."id";
        ELSE
          UPDATE "initiative" SET "admitted" = FALSE
            WHERE "id" = "initiative_row"."id";
        END IF;
      END LOOP;
      IF EXISTS (
        SELECT NULL FROM "initiative"
        WHERE "issue_id" = "issue_id_p" AND "admitted" = TRUE
      ) THEN
        UPDATE "issue" SET
          "state"        = 'voting',
          "accepted"     = coalesce("accepted", now()),
          "half_frozen"  = coalesce("half_frozen", now()),
          "fully_frozen" = now()
          WHERE "id" = "issue_id_p";
      ELSE
        UPDATE "issue" SET
          "state"           = 'canceled_no_initiative_admitted',
          "accepted"        = coalesce("accepted", now()),
          "half_frozen"     = coalesce("half_frozen", now()),
          "fully_frozen"    = now(),
          "closed"          = now(),
          "ranks_available" = TRUE
          WHERE "id" = "issue_id_p";
        -- NOTE: The following DELETE statements have effect only when
        --       issue state has been manipulated
        DELETE FROM "direct_voter"     WHERE "issue_id" = "issue_id_p";
        DELETE FROM "delegating_voter" WHERE "issue_id" = "issue_id_p";
        DELETE FROM "battle"           WHERE "issue_id" = "issue_id_p";
      END IF;
      RETURN;
    END;
  $$;


ALTER FUNCTION public.freeze_after_snapshot(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION freeze_after_snapshot(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION freeze_after_snapshot(issue_id_p integer) IS 'This function freezes an issue (fully) and starts voting, but must only be called when "create_snapshot" was called in the same transaction.';


--
-- Name: highlight(text, text); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION highlight(body_p text, query_text_p text) RETURNS text
    LANGUAGE plpgsql IMMUTABLE
    AS $$
    BEGIN
      RETURN ts_headline(
        'pg_catalog.simple',
        replace(replace("body_p", e'\\', e'\\\\'), '*', e'\\*'),
        "text_search_query"("query_text_p"),
        'StartSel=* StopSel=* HighlightAll=TRUE' );
    END;
  $$;


ALTER FUNCTION public.highlight(body_p text, query_text_p text) OWNER TO "www-data";

--
-- Name: FUNCTION highlight(body_p text, query_text_p text); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION highlight(body_p text, query_text_p text) IS 'For a given a user query this function encapsulates all matches with asterisks. Asterisks and backslashes being already present are preceeded with one extra backslash.';


--
-- Name: initiative_requires_first_draft_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION initiative_requires_first_draft_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NOT EXISTS (
        SELECT NULL FROM "draft" WHERE "initiative_id" = NEW."id"
      ) THEN
        --RAISE 'Cannot create initiative without an initial draft.' USING
        --  ERRCODE = 'integrity_constraint_violation',
        --  HINT    = 'Create issue, initiative and draft within the same transaction.';
        RAISE EXCEPTION 'Cannot create initiative without an initial draft.';
      END IF;
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.initiative_requires_first_draft_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION initiative_requires_first_draft_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION initiative_requires_first_draft_trigger() IS 'Implementation of trigger "initiative_requires_first_draft" on table "initiative"';


--
-- Name: issue_requires_first_initiative_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION issue_requires_first_initiative_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NOT EXISTS (
        SELECT NULL FROM "initiative" WHERE "issue_id" = NEW."id"
      ) THEN
        --RAISE 'Cannot create issue without an initial initiative.' USING
        --  ERRCODE = 'integrity_constraint_violation',
        --  HINT    = 'Create issue, initiative, and draft within the same transaction.';
        RAISE EXCEPTION 'Cannot create issue without an initial initiative.';
      END IF;
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.issue_requires_first_initiative_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION issue_requires_first_initiative_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION issue_requires_first_initiative_trigger() IS 'Implementation of trigger "issue_requires_first_initiative" on table "issue"';


--
-- Name: last_draft_deletes_initiative_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION last_draft_deletes_initiative_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "reference_lost" BOOLEAN;
    BEGIN
      IF TG_OP = 'DELETE' THEN
        "reference_lost" := TRUE;
      ELSE
        "reference_lost" := NEW."initiative_id" != OLD."initiative_id";
      END IF;
      IF
        "reference_lost" AND NOT EXISTS (
          SELECT NULL FROM "draft" WHERE "initiative_id" = OLD."initiative_id"
        )
      THEN
        DELETE FROM "initiative" WHERE "id" = OLD."initiative_id";
      END IF;
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.last_draft_deletes_initiative_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION last_draft_deletes_initiative_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION last_draft_deletes_initiative_trigger() IS 'Implementation of trigger "last_draft_deletes_initiative" on table "draft"';


--
-- Name: last_initiative_deletes_issue_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION last_initiative_deletes_issue_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "reference_lost" BOOLEAN;
    BEGIN
      IF TG_OP = 'DELETE' THEN
        "reference_lost" := TRUE;
      ELSE
        "reference_lost" := NEW."issue_id" != OLD."issue_id";
      END IF;
      IF
        "reference_lost" AND NOT EXISTS (
          SELECT NULL FROM "initiative" WHERE "issue_id" = OLD."issue_id"
        )
      THEN
        DELETE FROM "issue" WHERE "id" = OLD."issue_id";
      END IF;
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.last_initiative_deletes_issue_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION last_initiative_deletes_issue_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION last_initiative_deletes_issue_trigger() IS 'Implementation of trigger "last_initiative_deletes_issue" on table "initiative"';


--
-- Name: last_opinion_deletes_suggestion_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION last_opinion_deletes_suggestion_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "reference_lost" BOOLEAN;
    BEGIN
      IF TG_OP = 'DELETE' THEN
        "reference_lost" := TRUE;
      ELSE
        "reference_lost" := NEW."suggestion_id" != OLD."suggestion_id";
      END IF;
      IF
        "reference_lost" AND NOT EXISTS (
          SELECT NULL FROM "opinion" WHERE "suggestion_id" = OLD."suggestion_id"
        )
      THEN
        DELETE FROM "suggestion" WHERE "id" = OLD."suggestion_id";
      END IF;
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.last_opinion_deletes_suggestion_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION last_opinion_deletes_suggestion_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION last_opinion_deletes_suggestion_trigger() IS 'Implementation of trigger "last_opinion_deletes_suggestion" on table "opinion"';


--
-- Name: lock_issue(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION lock_issue(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    BEGIN
      LOCK TABLE "member"     IN SHARE MODE;
      LOCK TABLE "privilege"  IN SHARE MODE;
      LOCK TABLE "membership" IN SHARE MODE;
      LOCK TABLE "policy"     IN SHARE MODE;
      PERFORM NULL FROM "issue" WHERE "id" = "issue_id_p" FOR UPDATE;
      -- NOTE: The row-level exclusive lock in combination with the
      -- share_row_lock_issue(_via_initiative)_trigger functions (which
      -- acquire a row-level share lock on the issue) ensure that no data
      -- is changed, which could affect calculation of snapshots or
      -- counting of votes. Table "delegation" must be table-level-locked,
      -- as it also contains issue- and global-scope delegations.
      LOCK TABLE "delegation" IN SHARE MODE;
      LOCK TABLE "direct_population_snapshot"     IN EXCLUSIVE MODE;
      LOCK TABLE "delegating_population_snapshot" IN EXCLUSIVE MODE;
      LOCK TABLE "direct_interest_snapshot"       IN EXCLUSIVE MODE;
      LOCK TABLE "delegating_interest_snapshot"   IN EXCLUSIVE MODE;
      LOCK TABLE "direct_supporter_snapshot"      IN EXCLUSIVE MODE;
      RETURN;
    END;
  $$;


ALTER FUNCTION public.lock_issue(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION lock_issue(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION lock_issue(issue_id_p integer) IS 'Locks the issue and all other data which is used for calculating snapshots or counting votes.';


--
-- Name: manual_freeze(integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION manual_freeze(issue_id_p integer) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_row" "issue"%ROWTYPE;
    BEGIN
      PERFORM "create_snapshot"("issue_id_p");
      PERFORM "freeze_after_snapshot"("issue_id_p");
      RETURN;
    END;
  $$;


ALTER FUNCTION public.manual_freeze(issue_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION manual_freeze(issue_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION manual_freeze(issue_id_p integer) IS 'Freeze an issue manually (fully) and start voting';


--
-- Name: membership_weight(integer, integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION membership_weight(area_id_p integer, member_id_p integer) RETURNS integer
    LANGUAGE plpgsql STABLE
    AS $$
    BEGIN
      RETURN "membership_weight_with_skipping"(
        "area_id_p",
        "member_id_p",
        ARRAY["member_id_p"]
      );
    END;
  $$;


ALTER FUNCTION public.membership_weight(area_id_p integer, member_id_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION membership_weight(area_id_p integer, member_id_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION membership_weight(area_id_p integer, member_id_p integer) IS 'Calculates the potential voting weight of a member in a given area';


--
-- Name: membership_weight_with_skipping(integer, integer, integer[]); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION membership_weight_with_skipping(area_id_p integer, member_id_p integer, skip_member_ids_p integer[]) RETURNS integer
    LANGUAGE plpgsql STABLE
    AS $$
    DECLARE
      "sum_v"          INT4;
      "delegation_row" "area_delegation"%ROWTYPE;
    BEGIN
      "sum_v" := 1;
      FOR "delegation_row" IN
        SELECT "area_delegation".*
        FROM "area_delegation" LEFT JOIN "membership"
        ON "membership"."area_id" = "area_id_p"
        AND "membership"."member_id" = "area_delegation"."truster_id"
        WHERE "area_delegation"."area_id" = "area_id_p"
        AND "area_delegation"."trustee_id" = "member_id_p"
        AND "membership"."member_id" ISNULL
      LOOP
        IF NOT
          "skip_member_ids_p" @> ARRAY["delegation_row"."truster_id"]
        THEN
          "sum_v" := "sum_v" + "membership_weight_with_skipping"(
            "area_id_p",
            "delegation_row"."truster_id",
            "skip_member_ids_p" || "delegation_row"."truster_id"
          );
        END IF;
      END LOOP;
      RETURN "sum_v";
    END;
  $$;


ALTER FUNCTION public.membership_weight_with_skipping(area_id_p integer, member_id_p integer, skip_member_ids_p integer[]) OWNER TO "www-data";

--
-- Name: FUNCTION membership_weight_with_skipping(area_id_p integer, member_id_p integer, skip_member_ids_p integer[]); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION membership_weight_with_skipping(area_id_p integer, member_id_p integer, skip_member_ids_p integer[]) IS 'Helper function for "membership_weight" function';


--
-- Name: set_snapshot_event(integer, snapshot_event); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION set_snapshot_event(issue_id_p integer, event_p snapshot_event) RETURNS void
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "event_v" "issue"."latest_snapshot_event"%TYPE;
    BEGIN
      SELECT "latest_snapshot_event" INTO "event_v" FROM "issue"
        WHERE "id" = "issue_id_p" FOR UPDATE;
      UPDATE "issue" SET "latest_snapshot_event" = "event_p"
        WHERE "id" = "issue_id_p";
      UPDATE "direct_population_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      UPDATE "delegating_population_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      UPDATE "direct_interest_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      UPDATE "delegating_interest_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      UPDATE "direct_supporter_snapshot" SET "event" = "event_p"
        WHERE "issue_id" = "issue_id_p" AND "event" = "event_v";
      RETURN;
    END;
  $$;


ALTER FUNCTION public.set_snapshot_event(issue_id_p integer, event_p snapshot_event) OWNER TO "www-data";

--
-- Name: FUNCTION set_snapshot_event(issue_id_p integer, event_p snapshot_event); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION set_snapshot_event(issue_id_p integer, event_p snapshot_event) IS 'Change "event" attribute of the previous ''periodic'' snapshot';


--
-- Name: share_row_lock_issue_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION share_row_lock_issue_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF TG_OP = 'UPDATE' OR TG_OP = 'DELETE' THEN
        PERFORM NULL FROM "issue" WHERE "id" = OLD."issue_id" FOR SHARE;
      END IF;
      IF TG_OP = 'INSERT' OR TG_OP = 'UPDATE' THEN
        PERFORM NULL FROM "issue" WHERE "id" = NEW."issue_id" FOR SHARE;
        RETURN NEW;
      ELSE
        RETURN OLD;
      END IF;
    END;
  $$;


ALTER FUNCTION public.share_row_lock_issue_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION share_row_lock_issue_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION share_row_lock_issue_trigger() IS 'Implementation of trigger "share_row_lock_issue_via_initiative" on table "opinion"';


--
-- Name: share_row_lock_issue_via_initiative_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION share_row_lock_issue_via_initiative_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF TG_OP = 'UPDATE' OR TG_OP = 'DELETE' THEN
        PERFORM NULL FROM "issue"
          JOIN "initiative" ON "issue"."id" = "initiative"."issue_id"
          WHERE "initiative"."id" = OLD."initiative_id"
          FOR SHARE OF "issue";
      END IF;
      IF TG_OP = 'INSERT' OR TG_OP = 'UPDATE' THEN
        PERFORM NULL FROM "issue"
          JOIN "initiative" ON "issue"."id" = "initiative"."issue_id"
          WHERE "initiative"."id" = NEW."initiative_id"
          FOR SHARE OF "issue";
        RETURN NEW;
      ELSE
        RETURN OLD;
      END IF;
    END;
  $$;


ALTER FUNCTION public.share_row_lock_issue_via_initiative_trigger() OWNER TO "www-data";

--
-- Name: suggestion_requires_first_opinion_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION suggestion_requires_first_opinion_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NOT EXISTS (
        SELECT NULL FROM "opinion" WHERE "suggestion_id" = NEW."id"
      ) THEN
        RAISE EXCEPTION 'Cannot create a suggestion without an opinion.';
      END IF;
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.suggestion_requires_first_opinion_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION suggestion_requires_first_opinion_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION suggestion_requires_first_opinion_trigger() IS 'Implementation of trigger "suggestion_requires_first_opinion" on table "suggestion"';


--
-- Name: text_search_query(text); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION text_search_query(query_text_p text) RETURNS tsquery
    LANGUAGE plpgsql IMMUTABLE
    AS $$
    BEGIN
      RETURN plainto_tsquery('pg_catalog.simple', "query_text_p");
    END;
  $$;


ALTER FUNCTION public.text_search_query(query_text_p text) OWNER TO "www-data";

--
-- Name: FUNCTION text_search_query(query_text_p text); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION text_search_query(query_text_p text) IS 'Usage: WHERE "text_search_data" @@ "text_search_query"(''<user query>'')';


--
-- Name: vote_ratio(integer, integer); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION vote_ratio(positive_votes_p integer, negative_votes_p integer) RETURNS double precision
    LANGUAGE plpgsql STABLE
    AS $$
    BEGIN
      IF "positive_votes_p" > 0 AND "negative_votes_p" > 0 THEN
        RETURN
          "positive_votes_p"::FLOAT8 /
          ("positive_votes_p" + "negative_votes_p")::FLOAT8;
      ELSIF "positive_votes_p" > 0 THEN
        RETURN "positive_votes_p";
      ELSIF "negative_votes_p" > 0 THEN
        RETURN 1 - "negative_votes_p";
      ELSE
        RETURN 0.5;
      END IF;
    END;
  $$;


ALTER FUNCTION public.vote_ratio(positive_votes_p integer, negative_votes_p integer) OWNER TO "www-data";

--
-- Name: FUNCTION vote_ratio(positive_votes_p integer, negative_votes_p integer); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION vote_ratio(positive_votes_p integer, negative_votes_p integer) IS 'Returns a number, which can be used for comparison of initiatives based on count of approvals and disapprovals. Greater numbers indicate a better result. This function is NOT injective.';


--
-- Name: weight_of_added_delegations_for_interest_snapshot(integer, integer, integer[]); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION weight_of_added_delegations_for_interest_snapshot(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) RETURNS integer
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_delegation_row"  "issue_delegation"%ROWTYPE;
      "delegate_member_ids_v" "delegating_interest_snapshot"."delegate_member_ids"%TYPE;
      "weight_v"              INT4;
      "sub_weight_v"          INT4;
    BEGIN
      "weight_v" := 0;
      FOR "issue_delegation_row" IN
        SELECT * FROM "issue_delegation"
        WHERE "trustee_id" = "member_id_p"
        AND "issue_id" = "issue_id_p"
      LOOP
        IF NOT EXISTS (
          SELECT NULL FROM "direct_interest_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "issue_delegation_row"."truster_id"
        ) AND NOT EXISTS (
          SELECT NULL FROM "delegating_interest_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "issue_delegation_row"."truster_id"
        ) THEN
          "delegate_member_ids_v" :=
            "member_id_p" || "delegate_member_ids_p";
          INSERT INTO "delegating_interest_snapshot" (
              "issue_id",
              "event",
              "member_id",
              "scope",
              "delegate_member_ids"
            ) VALUES (
              "issue_id_p",
              'periodic',
              "issue_delegation_row"."truster_id",
              "issue_delegation_row"."scope",
              "delegate_member_ids_v"
            );
          "sub_weight_v" := 1 +
            "weight_of_added_delegations_for_interest_snapshot"(
              "issue_id_p",
              "issue_delegation_row"."truster_id",
              "delegate_member_ids_v"
            );
          UPDATE "delegating_interest_snapshot"
            SET "weight" = "sub_weight_v"
            WHERE "issue_id" = "issue_id_p"
            AND "event" = 'periodic'
            AND "member_id" = "issue_delegation_row"."truster_id";
          "weight_v" := "weight_v" + "sub_weight_v";
        END IF;
      END LOOP;
      RETURN "weight_v";
    END;
  $$;


ALTER FUNCTION public.weight_of_added_delegations_for_interest_snapshot(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) OWNER TO "www-data";

--
-- Name: FUNCTION weight_of_added_delegations_for_interest_snapshot(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION weight_of_added_delegations_for_interest_snapshot(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) IS 'Helper function for "create_interest_snapshot" function';


--
-- Name: weight_of_added_delegations_for_population_snapshot(integer, integer, integer[]); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION weight_of_added_delegations_for_population_snapshot(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) RETURNS integer
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_delegation_row"  "issue_delegation"%ROWTYPE;
      "delegate_member_ids_v" "delegating_population_snapshot"."delegate_member_ids"%TYPE;
      "weight_v"              INT4;
      "sub_weight_v"          INT4;
    BEGIN
      "weight_v" := 0;
      FOR "issue_delegation_row" IN
        SELECT * FROM "issue_delegation"
        WHERE "trustee_id" = "member_id_p"
        AND "issue_id" = "issue_id_p"
      LOOP
        IF NOT EXISTS (
          SELECT NULL FROM "direct_population_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "issue_delegation_row"."truster_id"
        ) AND NOT EXISTS (
          SELECT NULL FROM "delegating_population_snapshot"
          WHERE "issue_id" = "issue_id_p"
          AND "event" = 'periodic'
          AND "member_id" = "issue_delegation_row"."truster_id"
        ) THEN
          "delegate_member_ids_v" :=
            "member_id_p" || "delegate_member_ids_p";
          INSERT INTO "delegating_population_snapshot" (
              "issue_id",
              "event",
              "member_id",
              "scope",
              "delegate_member_ids"
            ) VALUES (
              "issue_id_p",
              'periodic',
              "issue_delegation_row"."truster_id",
              "issue_delegation_row"."scope",
              "delegate_member_ids_v"
            );
          "sub_weight_v" := 1 +
            "weight_of_added_delegations_for_population_snapshot"(
              "issue_id_p",
              "issue_delegation_row"."truster_id",
              "delegate_member_ids_v"
            );
          UPDATE "delegating_population_snapshot"
            SET "weight" = "sub_weight_v"
            WHERE "issue_id" = "issue_id_p"
            AND "event" = 'periodic'
            AND "member_id" = "issue_delegation_row"."truster_id";
          "weight_v" := "weight_v" + "sub_weight_v";
        END IF;
      END LOOP;
      RETURN "weight_v";
    END;
  $$;


ALTER FUNCTION public.weight_of_added_delegations_for_population_snapshot(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) OWNER TO "www-data";

--
-- Name: FUNCTION weight_of_added_delegations_for_population_snapshot(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION weight_of_added_delegations_for_population_snapshot(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) IS 'Helper function for "create_population_snapshot" function';


--
-- Name: weight_of_added_vote_delegations(integer, integer, integer[]); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION weight_of_added_vote_delegations(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) RETURNS integer
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "issue_delegation_row"  "issue_delegation"%ROWTYPE;
      "delegate_member_ids_v" "delegating_voter"."delegate_member_ids"%TYPE;
      "weight_v"              INT4;
      "sub_weight_v"          INT4;
    BEGIN
      "weight_v" := 0;
      FOR "issue_delegation_row" IN
        SELECT * FROM "issue_delegation"
        WHERE "trustee_id" = "member_id_p"
        AND "issue_id" = "issue_id_p"
      LOOP
        IF NOT EXISTS (
          SELECT NULL FROM "direct_voter"
          WHERE "member_id" = "issue_delegation_row"."truster_id"
          AND "issue_id" = "issue_id_p"
        ) AND NOT EXISTS (
          SELECT NULL FROM "delegating_voter"
          WHERE "member_id" = "issue_delegation_row"."truster_id"
          AND "issue_id" = "issue_id_p"
        ) THEN
          "delegate_member_ids_v" :=
            "member_id_p" || "delegate_member_ids_p";
          INSERT INTO "delegating_voter" (
              "issue_id",
              "member_id",
              "scope",
              "delegate_member_ids"
            ) VALUES (
              "issue_id_p",
              "issue_delegation_row"."truster_id",
              "issue_delegation_row"."scope",
              "delegate_member_ids_v"
            );
          "sub_weight_v" := 1 +
            "weight_of_added_vote_delegations"(
              "issue_id_p",
              "issue_delegation_row"."truster_id",
              "delegate_member_ids_v"
            );
          UPDATE "delegating_voter"
            SET "weight" = "sub_weight_v"
            WHERE "issue_id" = "issue_id_p"
            AND "member_id" = "issue_delegation_row"."truster_id";
          "weight_v" := "weight_v" + "sub_weight_v";
        END IF;
      END LOOP;
      RETURN "weight_v";
    END;
  $$;


ALTER FUNCTION public.weight_of_added_vote_delegations(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) OWNER TO "www-data";

--
-- Name: FUNCTION weight_of_added_vote_delegations(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION weight_of_added_vote_delegations(issue_id_p integer, member_id_p integer, delegate_member_ids_p integer[]) IS 'Helper function for "add_vote_delegations" function';


--
-- Name: write_event_initiative_or_draft_created_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION write_event_initiative_or_draft_created_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "initiative_row" "initiative"%ROWTYPE;
      "issue_row"      "issue"%ROWTYPE;
      "event_v"        "event_type";
    BEGIN
      SELECT * INTO "initiative_row" FROM "initiative"
        WHERE "id" = NEW."initiative_id";
      SELECT * INTO "issue_row" FROM "issue"
        WHERE "id" = "initiative_row"."issue_id";
      IF EXISTS (
        SELECT NULL FROM "draft"
        WHERE "initiative_id" = NEW."initiative_id"
        AND "id" != NEW."id"
      ) THEN
        "event_v" := 'new_draft_created';
      ELSE
        IF EXISTS (
          SELECT NULL FROM "initiative"
          WHERE "issue_id" = "initiative_row"."issue_id"
          AND "id" != "initiative_row"."id"
        ) THEN
          "event_v" := 'initiative_created_in_existing_issue';
        ELSE
          "event_v" := 'initiative_created_in_new_issue';
        END IF;
      END IF;
      INSERT INTO "event" (
          "event", "member_id",
          "issue_id", "state", "initiative_id", "draft_id"
        ) VALUES (
          "event_v",
          NEW."author_id",
          "initiative_row"."issue_id",
          "issue_row"."state",
          "initiative_row"."id",
          NEW."id" );
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.write_event_initiative_or_draft_created_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION write_event_initiative_or_draft_created_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION write_event_initiative_or_draft_created_trigger() IS 'Implementation of trigger "write_event_initiative_or_draft_created" on table "issue"';


--
-- Name: write_event_initiative_revoked_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION write_event_initiative_revoked_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
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


ALTER FUNCTION public.write_event_initiative_revoked_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION write_event_initiative_revoked_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION write_event_initiative_revoked_trigger() IS 'Implementation of trigger "write_event_initiative_revoked" on table "issue"';


--
-- Name: write_event_issue_state_changed_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION write_event_issue_state_changed_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    BEGIN
      IF NEW."state" != OLD."state" AND NEW."state" != 'calculation' THEN
        INSERT INTO "event" ("event", "issue_id", "state")
          VALUES ('issue_state_changed', NEW."id", NEW."state");
      END IF;
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.write_event_issue_state_changed_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION write_event_issue_state_changed_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION write_event_issue_state_changed_trigger() IS 'Implementation of trigger "write_event_issue_state_changed" on table "issue"';


--
-- Name: write_event_suggestion_created_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION write_event_suggestion_created_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
    DECLARE
      "initiative_row" "initiative"%ROWTYPE;
      "issue_row"      "issue"%ROWTYPE;
    BEGIN
      SELECT * INTO "initiative_row" FROM "initiative"
        WHERE "id" = NEW."initiative_id";
      SELECT * INTO "issue_row" FROM "issue"
        WHERE "id" = "initiative_row"."issue_id";
      INSERT INTO "event" (
          "event", "member_id",
          "issue_id", "state", "initiative_id", "suggestion_id"
        ) VALUES (
          'suggestion_created',
          NEW."author_id",
          "initiative_row"."issue_id",
          "issue_row"."state",
          "initiative_row"."id",
          NEW."id" );
      RETURN NULL;
    END;
  $$;


ALTER FUNCTION public.write_event_suggestion_created_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION write_event_suggestion_created_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION write_event_suggestion_created_trigger() IS 'Implementation of trigger "write_event_suggestion_created" on table "issue"';


--
-- Name: write_member_history_trigger(); Type: FUNCTION; Schema: public; Owner: www-data
--

CREATE FUNCTION write_member_history_trigger() RETURNS trigger
    LANGUAGE plpgsql
    AS $$
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


ALTER FUNCTION public.write_member_history_trigger() OWNER TO "www-data";

--
-- Name: FUNCTION write_member_history_trigger(); Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON FUNCTION write_member_history_trigger() IS 'Implementation of trigger "write_member_history" on table "member"';


SET default_tablespace = '';

SET default_with_oids = false;

--
-- Name: allowed_policy; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE allowed_policy (
    area_id integer NOT NULL,
    policy_id integer NOT NULL,
    default_policy boolean DEFAULT false NOT NULL
);


ALTER TABLE public.allowed_policy OWNER TO "www-data";

--
-- Name: TABLE allowed_policy; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE allowed_policy IS 'Selects which policies can be used in each area';


--
-- Name: COLUMN allowed_policy.default_policy; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN allowed_policy.default_policy IS 'One policy per area can be set as default.';


--
-- Name: area; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE area (
    id integer NOT NULL,
    unit_id integer NOT NULL,
    active boolean DEFAULT true NOT NULL,
    name text NOT NULL,
    description text DEFAULT ''::text NOT NULL,
    direct_member_count integer,
    member_weight integer,
    text_search_data tsvector
);


ALTER TABLE public.area OWNER TO "www-data";

--
-- Name: TABLE area; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE area IS 'Subject areas';


--
-- Name: COLUMN area.active; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN area.active IS 'TRUE means new issues can be created in this area';


--
-- Name: COLUMN area.direct_member_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN area.direct_member_count IS 'Number of active members of that area (ignoring their weight), as calculated from view "area_member_count"';


--
-- Name: COLUMN area.member_weight; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN area.member_weight IS 'Same as "direct_member_count" but respecting delegations';


--
-- Name: delegation; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE delegation (
    id bigint NOT NULL,
    truster_id integer NOT NULL,
    trustee_id integer,
    scope delegation_scope NOT NULL,
    unit_id integer,
    area_id integer,
    issue_id integer,
    CONSTRAINT area_id_and_issue_id_set_according_to_scope CHECK (((((((scope = 'unit'::delegation_scope) AND (unit_id IS NOT NULL)) AND (area_id IS NULL)) AND (issue_id IS NULL)) OR ((((scope = 'area'::delegation_scope) AND (unit_id IS NULL)) AND (area_id IS NOT NULL)) AND (issue_id IS NULL))) OR ((((scope = 'issue'::delegation_scope) AND (unit_id IS NULL)) AND (area_id IS NULL)) AND (issue_id IS NOT NULL)))),
    CONSTRAINT cant_delegate_to_yourself CHECK ((truster_id <> trustee_id)),
    CONSTRAINT no_unit_delegation_to_null CHECK (((trustee_id IS NOT NULL) OR (scope <> 'unit'::delegation_scope)))
);


ALTER TABLE public.delegation OWNER TO "www-data";

--
-- Name: TABLE delegation; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE delegation IS 'Delegation of vote-weight to other members';


--
-- Name: COLUMN delegation.unit_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegation.unit_id IS 'Reference to unit, if delegation is unit-wide, otherwise NULL';


--
-- Name: COLUMN delegation.area_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegation.area_id IS 'Reference to area, if delegation is area-wide, otherwise NULL';


--
-- Name: COLUMN delegation.issue_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegation.issue_id IS 'Reference to issue, if delegation is issue-wide, otherwise NULL';


--
-- Name: member; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE member (
    id integer NOT NULL,
    created timestamp with time zone DEFAULT now() NOT NULL,
    invite_code text,
    invite_code_expiry timestamp with time zone,
    admin_comment text,
    activated timestamp with time zone,
    last_activity date,
    last_login timestamp with time zone,
    login text,
    password text,
    locked boolean DEFAULT false NOT NULL,
    active boolean DEFAULT false NOT NULL,
    admin boolean DEFAULT false NOT NULL,
    lang text,
    notify_email text,
    notify_email_unconfirmed text,
    notify_email_secret text,
    notify_email_secret_expiry timestamp with time zone,
    notify_email_lock_expiry timestamp with time zone,
    notify_level notify_level,
    password_reset_secret text,
    password_reset_secret_expiry timestamp with time zone,
    name text,
    identification text,
    authentication text,
    organizational_unit text,
    internal_posts text,
    realname text,
    birthday date,
    address text,
    email text,
    xmpp_address text,
    website text,
    phone text,
    mobile_phone text,
    profession text,
    external_memberships text,
    external_posts text,
    formatting_engine text,
    statement text,
    text_search_data tsvector,
    CONSTRAINT active_requires_activated_and_last_activity CHECK (((active = false) OR ((activated IS NOT NULL) AND (last_activity IS NOT NULL)))),
    CONSTRAINT name_not_null_if_activated CHECK (((activated IS NULL) OR (name IS NOT NULL)))
);


ALTER TABLE public.member OWNER TO "www-data";

--
-- Name: TABLE member; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE member IS 'Users of the system, e.g. members of an organization';


--
-- Name: COLUMN member.created; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.created IS 'Creation of member record and/or invite code';


--
-- Name: COLUMN member.invite_code; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.invite_code IS 'Optional invite code, to allow a member to initialize his/her account the first time';


--
-- Name: COLUMN member.invite_code_expiry; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.invite_code_expiry IS 'Expiry data/time for "invite_code"';


--
-- Name: COLUMN member.admin_comment; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.admin_comment IS 'Hidden comment for administrative purposes';


--
-- Name: COLUMN member.activated; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.activated IS 'Timestamp of first activation of account (i.e. usage of "invite_code"); required to be set for "active" members';


--
-- Name: COLUMN member.last_activity; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.last_activity IS 'Date of last activity of member; required to be set for "active" members';


--
-- Name: COLUMN member.last_login; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.last_login IS 'Timestamp of last login';


--
-- Name: COLUMN member.login; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.login IS 'Login name';


--
-- Name: COLUMN member.password; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.password IS 'Password (preferably as crypto-hash, depending on the frontend or access layer)';


--
-- Name: COLUMN member.locked; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.locked IS 'Locked members can not log in.';


--
-- Name: COLUMN member.active; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.active IS 'Memberships, support and votes are taken into account when corresponding members are marked as active. Automatically set to FALSE, if "last_activity" is older than "system_setting"."member_ttl".';


--
-- Name: COLUMN member.admin; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.admin IS 'TRUE for admins, which can administrate other users and setup policies and areas';


--
-- Name: COLUMN member.lang; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.lang IS 'Language code of the preferred language of the member';


--
-- Name: COLUMN member.notify_email; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.notify_email IS 'Email address where notifications of the system are sent to';


--
-- Name: COLUMN member.notify_email_unconfirmed; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.notify_email_unconfirmed IS 'Unconfirmed email address provided by the member to be copied into "notify_email" field after verification';


--
-- Name: COLUMN member.notify_email_secret; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.notify_email_secret IS 'Secret sent to the address in "notify_email_unconformed"';


--
-- Name: COLUMN member.notify_email_secret_expiry; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.notify_email_secret_expiry IS 'Expiry date/time for "notify_email_secret"';


--
-- Name: COLUMN member.notify_email_lock_expiry; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.notify_email_lock_expiry IS 'Date/time until no further email confirmation mails may be sent (abuse protection)';


--
-- Name: COLUMN member.notify_level; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.notify_level IS 'Selects which event notifications are to be sent to the "notify_email" mail address, may be NULL if member did not make any selection yet';


--
-- Name: COLUMN member.name; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.name IS 'Distinct name of the member, may be NULL if account has not been activated yet';


--
-- Name: COLUMN member.identification; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.identification IS 'Optional identification number or code of the member';


--
-- Name: COLUMN member.authentication; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.authentication IS 'Information about how this member was authenticated';


--
-- Name: COLUMN member.organizational_unit; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.organizational_unit IS 'Branch or division of the organization the member belongs to';


--
-- Name: COLUMN member.internal_posts; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.internal_posts IS 'Posts (offices) of the member inside the organization';


--
-- Name: COLUMN member.realname; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.realname IS 'Real name of the member, may be identical with "name"';


--
-- Name: COLUMN member.email; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.email IS 'Published email address of the member; not used for system notifications';


--
-- Name: COLUMN member.external_memberships; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.external_memberships IS 'Other organizations the member is involved in';


--
-- Name: COLUMN member.external_posts; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.external_posts IS 'Posts (offices) outside the organization';


--
-- Name: COLUMN member.formatting_engine; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.formatting_engine IS 'Allows different formatting engines (i.e. wiki formats) to be used for "member"."statement"';


--
-- Name: COLUMN member.statement; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member.statement IS 'Freely chosen text of the member for his/her profile';


--
-- Name: privilege; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE privilege (
    unit_id integer NOT NULL,
    member_id integer NOT NULL,
    admin_manager boolean DEFAULT false NOT NULL,
    unit_manager boolean DEFAULT false NOT NULL,
    area_manager boolean DEFAULT false NOT NULL,
    voting_right_manager boolean DEFAULT false NOT NULL,
    voting_right boolean DEFAULT true NOT NULL
);


ALTER TABLE public.privilege OWNER TO "www-data";

--
-- Name: TABLE privilege; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE privilege IS 'Members rights related to each unit';


--
-- Name: COLUMN privilege.admin_manager; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN privilege.admin_manager IS 'Grant/revoke admin privileges to/from other members';


--
-- Name: COLUMN privilege.unit_manager; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN privilege.unit_manager IS 'Create and disable sub units';


--
-- Name: COLUMN privilege.area_manager; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN privilege.area_manager IS 'Create and disable areas and set area parameters';


--
-- Name: COLUMN privilege.voting_right_manager; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN privilege.voting_right_manager IS 'Select which members are allowed to discuss and vote within the unit';


--
-- Name: COLUMN privilege.voting_right; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN privilege.voting_right IS 'Right to discuss and vote';


--
-- Name: area_delegation; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW area_delegation AS
    SELECT DISTINCT ON (area.id, delegation.truster_id) area.id AS area_id, delegation.id, delegation.truster_id, delegation.trustee_id, delegation.scope FROM (((area JOIN delegation ON (((delegation.unit_id = area.unit_id) OR (delegation.area_id = area.id)))) JOIN member ON ((delegation.truster_id = member.id))) JOIN privilege ON (((area.unit_id = privilege.unit_id) AND (delegation.truster_id = privilege.member_id)))) WHERE (member.active AND privilege.voting_right) ORDER BY area.id, delegation.truster_id, delegation.scope DESC;


ALTER TABLE public.area_delegation OWNER TO "www-data";

--
-- Name: VIEW area_delegation; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW area_delegation IS 'Area delegations where trusters are active and have voting right';


--
-- Name: area_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE area_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.area_id_seq OWNER TO "www-data";

--
-- Name: area_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE area_id_seq OWNED BY area.id;


--
-- Name: area_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('area_id_seq', 1, true);


--
-- Name: membership; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE membership (
    area_id integer NOT NULL,
    member_id integer NOT NULL
);


ALTER TABLE public.membership OWNER TO "www-data";

--
-- Name: TABLE membership; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE membership IS 'Interest of members in topic areas';


--
-- Name: area_member_count; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW area_member_count AS
    SELECT area.id AS area_id, count(member.id) AS direct_member_count, COALESCE(sum(CASE WHEN (member.id IS NOT NULL) THEN membership_weight(area.id, member.id) ELSE 0 END)) AS member_weight FROM (((area LEFT JOIN membership ON ((area.id = membership.area_id))) LEFT JOIN privilege ON ((((privilege.unit_id = area.unit_id) AND (privilege.member_id = membership.member_id)) AND privilege.voting_right))) LEFT JOIN member ON (((member.id = privilege.member_id) AND member.active))) GROUP BY area.id;


ALTER TABLE public.area_member_count OWNER TO "www-data";

--
-- Name: VIEW area_member_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW area_member_count IS 'View used to update "direct_member_count" and "member_weight" columns of table "area"';


--
-- Name: area_setting; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE area_setting (
    member_id integer NOT NULL,
    key text NOT NULL,
    area_id integer NOT NULL,
    value text NOT NULL
);


ALTER TABLE public.area_setting OWNER TO "www-data";

--
-- Name: TABLE area_setting; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE area_setting IS 'Place for frontend to store area specific settings of members as strings';


--
-- Name: battle; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE battle (
    issue_id integer NOT NULL,
    winning_initiative_id integer,
    losing_initiative_id integer,
    count integer NOT NULL,
    CONSTRAINT initiative_ids_not_equal CHECK (((winning_initiative_id <> losing_initiative_id) OR (((winning_initiative_id IS NOT NULL) AND (losing_initiative_id IS NULL)) OR ((winning_initiative_id IS NULL) AND (losing_initiative_id IS NOT NULL)))))
);


ALTER TABLE public.battle OWNER TO "www-data";

--
-- Name: TABLE battle; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE battle IS 'Number of members preferring one initiative to another; Filled by "battle_view" when closing an issue; NULL as initiative_id denotes virtual "status-quo" initiative';


--
-- Name: initiative; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE initiative (
    issue_id integer NOT NULL,
    id integer NOT NULL,
    name text NOT NULL,
    discussion_url text,
    created timestamp with time zone DEFAULT now() NOT NULL,
    revoked timestamp with time zone,
    revoked_by_member_id integer,
    suggested_initiative_id integer,
    admitted boolean,
    supporter_count integer,
    informed_supporter_count integer,
    satisfied_supporter_count integer,
    satisfied_informed_supporter_count integer,
    positive_votes integer,
    negative_votes integer,
    direct_majority boolean,
    indirect_majority boolean,
    schulze_rank integer,
    better_than_status_quo boolean,
    worse_than_status_quo boolean,
    reverse_beat_path boolean,
    multistage_majority boolean,
    eligible boolean,
    winner boolean,
    rank integer,
    text_search_data tsvector,
    CONSTRAINT all_or_none_of_revoked_and_revoked_by_member_id_must_be_null CHECK (((revoked IS NOT NULL) = (revoked_by_member_id IS NOT NULL))),
    CONSTRAINT better_excludes_worse CHECK ((NOT (better_than_status_quo AND worse_than_status_quo))),
    CONSTRAINT eligible_at_first_rank_is_winner CHECK ((((eligible = false) OR (rank <> 1)) OR (winner = true))),
    CONSTRAINT minimum_requirement_to_be_eligible CHECK (((eligible = false) OR ((direct_majority AND indirect_majority) AND better_than_status_quo))),
    CONSTRAINT non_admitted_initiatives_cant_contain_voting_results CHECK ((((admitted IS NOT NULL) AND (admitted = true)) OR ((((((((((((positive_votes IS NULL) AND (negative_votes IS NULL)) AND (direct_majority IS NULL)) AND (indirect_majority IS NULL)) AND (schulze_rank IS NULL)) AND (better_than_status_quo IS NULL)) AND (worse_than_status_quo IS NULL)) AND (reverse_beat_path IS NULL)) AND (multistage_majority IS NULL)) AND (eligible IS NULL)) AND (winner IS NULL)) AND (rank IS NULL)))),
    CONSTRAINT non_revoked_initiatives_cant_suggest_other CHECK (((revoked IS NOT NULL) OR (suggested_initiative_id IS NULL))),
    CONSTRAINT revoked_initiatives_cant_be_admitted CHECK (((revoked IS NULL) OR (admitted IS NULL))),
    CONSTRAINT winner_must_be_eligible CHECK (((winner = false) OR (eligible = true))),
    CONSTRAINT winner_must_have_first_rank CHECK (((winner = false) OR (rank = 1)))
);


ALTER TABLE public.initiative OWNER TO "www-data";

--
-- Name: TABLE initiative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE initiative IS 'Group of members publishing drafts for resolutions to be passed; Frontends must ensure that initiatives of half_frozen issues are not revoked, and that initiatives of fully_frozen or closed issues are neither revoked nor created.';


--
-- Name: COLUMN initiative.discussion_url; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.discussion_url IS 'URL pointing to a discussion platform for this initiative';


--
-- Name: COLUMN initiative.revoked; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.revoked IS 'Point in time, when one initiator decided to revoke the initiative';


--
-- Name: COLUMN initiative.revoked_by_member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.revoked_by_member_id IS 'Member, who decided to revoke the initiative';


--
-- Name: COLUMN initiative.admitted; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.admitted IS 'TRUE, if initiative reaches the "initiative_quorum" when freezing the issue';


--
-- Name: COLUMN initiative.supporter_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.supporter_count IS 'Calculated from table "direct_supporter_snapshot"';


--
-- Name: COLUMN initiative.informed_supporter_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.informed_supporter_count IS 'Calculated from table "direct_supporter_snapshot"';


--
-- Name: COLUMN initiative.satisfied_supporter_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.satisfied_supporter_count IS 'Calculated from table "direct_supporter_snapshot"';


--
-- Name: COLUMN initiative.satisfied_informed_supporter_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.satisfied_informed_supporter_count IS 'Calculated from table "direct_supporter_snapshot"';


--
-- Name: COLUMN initiative.positive_votes; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.positive_votes IS 'Calculated from table "direct_voter"';


--
-- Name: COLUMN initiative.negative_votes; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.negative_votes IS 'Calculated from table "direct_voter"';


--
-- Name: COLUMN initiative.direct_majority; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.direct_majority IS 'TRUE, if "positive_votes"/("positive_votes"+"negative_votes") is strictly greater or greater-equal than "direct_majority_num"/"direct_majority_den", and "positive_votes" is greater-equal than "direct_majority_positive", and ("positive_votes"+abstentions) is greater-equal than "direct_majority_non_negative"';


--
-- Name: COLUMN initiative.indirect_majority; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.indirect_majority IS 'Same as "direct_majority", but also considering indirect beat paths';


--
-- Name: COLUMN initiative.schulze_rank; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.schulze_rank IS 'Schulze-Ranking without tie-breaking';


--
-- Name: COLUMN initiative.better_than_status_quo; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.better_than_status_quo IS 'TRUE, if initiative has a schulze-ranking better than the status quo (without tie-breaking)';


--
-- Name: COLUMN initiative.worse_than_status_quo; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.worse_than_status_quo IS 'TRUE, if initiative has a schulze-ranking worse than the status quo (without tie-breaking)';


--
-- Name: COLUMN initiative.reverse_beat_path; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.reverse_beat_path IS 'TRUE, if there is a beat path (may include ties) from this initiative to the status quo';


--
-- Name: COLUMN initiative.multistage_majority; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.multistage_majority IS 'TRUE, if either (a) this initiative has no better rank than the status quo, or (b) there exists a better ranked initiative X, which directly beats this initiative, and either more voters prefer X to this initiative than voters preferring X to the status quo or less voters prefer this initiative to X than voters preferring the status quo to X';


--
-- Name: COLUMN initiative.eligible; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.eligible IS 'Initiative has a "direct_majority" and an "indirect_majority", is "better_than_status_quo" and depending on selected policy the initiative has no "reverse_beat_path" or "multistage_majority"';


--
-- Name: COLUMN initiative.winner; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.winner IS 'Winner is the "eligible" initiative with best "schulze_rank" and in case of ties with lowest "id"';


--
-- Name: COLUMN initiative.rank; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiative.rank IS 'Unique ranking for all "admitted" initiatives per issue; lower rank is better; a winner always has rank 1, but rank 1 does not imply that an initiative is winner; initiatives with "direct_majority" AND "indirect_majority" always have a better (lower) rank than other initiatives';


--
-- Name: issue; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE issue (
    id integer NOT NULL,
    area_id integer NOT NULL,
    policy_id integer NOT NULL,
    state issue_state DEFAULT 'admission'::issue_state NOT NULL,
    created timestamp with time zone DEFAULT now() NOT NULL,
    accepted timestamp with time zone,
    half_frozen timestamp with time zone,
    fully_frozen timestamp with time zone,
    closed timestamp with time zone,
    ranks_available boolean DEFAULT false NOT NULL,
    cleaned timestamp with time zone,
    admission_time interval NOT NULL,
    discussion_time interval NOT NULL,
    verification_time interval NOT NULL,
    voting_time interval NOT NULL,
    snapshot timestamp with time zone,
    latest_snapshot_event snapshot_event,
    population integer,
    voter_count integer,
    status_quo_schulze_rank integer,
    CONSTRAINT freeze_requires_snapshot CHECK (((fully_frozen IS NULL) OR (snapshot IS NOT NULL))),
    CONSTRAINT last_snapshot_on_full_freeze CHECK ((snapshot = fully_frozen)),
    CONSTRAINT only_closed_issues_may_be_cleaned CHECK (((cleaned IS NULL) OR (closed IS NOT NULL))),
    CONSTRAINT set_both_or_none_of_snapshot_and_latest_snapshot_event CHECK (((snapshot IS NOT NULL) = (latest_snapshot_event IS NOT NULL))),
    CONSTRAINT state_change_order CHECK (((((created <= accepted) AND (accepted <= half_frozen)) AND (half_frozen <= fully_frozen)) AND (fully_frozen <= closed))),
    CONSTRAINT valid_state CHECK (((((((((((((((accepted IS NULL) AND (half_frozen IS NULL)) AND (fully_frozen IS NULL)) AND (closed IS NULL)) AND (ranks_available = false)) OR (((((accepted IS NULL) AND (half_frozen IS NULL)) AND (fully_frozen IS NULL)) AND (closed IS NOT NULL)) AND (ranks_available = false))) OR (((((accepted IS NOT NULL) AND (half_frozen IS NULL)) AND (fully_frozen IS NULL)) AND (closed IS NULL)) AND (ranks_available = false))) OR (((((accepted IS NOT NULL) AND (half_frozen IS NULL)) AND (fully_frozen IS NULL)) AND (closed IS NOT NULL)) AND (ranks_available = false))) OR (((((accepted IS NOT NULL) AND (half_frozen IS NOT NULL)) AND (fully_frozen IS NULL)) AND (closed IS NULL)) AND (ranks_available = false))) OR (((((accepted IS NOT NULL) AND (half_frozen IS NOT NULL)) AND (fully_frozen IS NULL)) AND (closed IS NOT NULL)) AND (ranks_available = false))) OR (((((accepted IS NOT NULL) AND (half_frozen IS NOT NULL)) AND (fully_frozen IS NOT NULL)) AND (closed IS NULL)) AND (ranks_available = false))) OR (((((accepted IS NOT NULL) AND (half_frozen IS NOT NULL)) AND (fully_frozen IS NOT NULL)) AND (closed IS NOT NULL)) AND (ranks_available = false))) OR (((((accepted IS NOT NULL) AND (half_frozen IS NOT NULL)) AND (fully_frozen IS NOT NULL)) AND (closed IS NOT NULL)) AND (ranks_available = true))) AND ((((((((((((((state = 'admission'::issue_state) AND (closed IS NULL)) AND (accepted IS NULL)) OR ((((state = 'discussion'::issue_state) AND (closed IS NULL)) AND (accepted IS NOT NULL)) AND (half_frozen IS NULL))) OR ((((state = 'verification'::issue_state) AND (closed IS NULL)) AND (half_frozen IS NOT NULL)) AND (fully_frozen IS NULL))) OR (((state = 'voting'::issue_state) AND (closed IS NULL)) AND (fully_frozen IS NOT NULL))) OR (((state = 'canceled_revoked_before_accepted'::issue_state) AND (closed IS NOT NULL)) AND (accepted IS NULL))) OR (((state = 'canceled_issue_not_accepted'::issue_state) AND (closed IS NOT NULL)) AND (accepted IS NULL))) OR (((state = 'canceled_after_revocation_during_discussion'::issue_state) AND (closed IS NOT NULL)) AND (half_frozen IS NULL))) OR (((state = 'canceled_after_revocation_during_verification'::issue_state) AND (closed IS NOT NULL)) AND (fully_frozen IS NULL))) OR ((((state = 'calculation'::issue_state) AND (closed IS NOT NULL)) AND (fully_frozen IS NOT NULL)) AND (ranks_available = false))) OR ((((state = 'canceled_no_initiative_admitted'::issue_state) AND (closed IS NOT NULL)) AND (fully_frozen IS NOT NULL)) AND (ranks_available = true))) OR ((((state = 'finished_without_winner'::issue_state) AND (closed IS NOT NULL)) AND (fully_frozen IS NOT NULL)) AND (ranks_available = true))) OR ((((state = 'finished_with_winner'::issue_state) AND (closed IS NOT NULL)) AND (fully_frozen IS NOT NULL)) AND (ranks_available = true)))))
);


ALTER TABLE public.issue OWNER TO "www-data";

--
-- Name: TABLE issue; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE issue IS 'Groups of initiatives';


--
-- Name: COLUMN issue.accepted; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.accepted IS 'Point in time, when one initiative of issue reached the "issue_quorum"';


--
-- Name: COLUMN issue.half_frozen; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.half_frozen IS 'Point in time, when "discussion_time" has elapsed; Frontends must ensure that for half_frozen issues a) initiatives are not revoked, b) no new drafts are created, c) no initiators are added or removed.';


--
-- Name: COLUMN issue.fully_frozen; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.fully_frozen IS 'Point in time, when "verification_time" has elapsed and voting has started; Frontends must ensure that for fully_frozen issues additionally to the restrictions for half_frozen issues a) initiatives are not created, b) no interest is created or removed, c) no supporters are added or removed, d) no opinions are created, changed or deleted.';


--
-- Name: COLUMN issue.closed; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.closed IS 'Point in time, when "admission_time" or "voting_time" have elapsed, and issue is no longer active; Frontends must ensure that for closed issues additionally to the restrictions for half_frozen and fully_frozen issues a) no voter is added or removed to/from the direct_voter table, b) no votes are added, modified or removed.';


--
-- Name: COLUMN issue.ranks_available; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.ranks_available IS 'TRUE = ranks have been calculated';


--
-- Name: COLUMN issue.cleaned; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.cleaned IS 'Point in time, when discussion data and votes had been deleted';


--
-- Name: COLUMN issue.admission_time; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.admission_time IS 'Copied from "policy" table at creation of issue';


--
-- Name: COLUMN issue.discussion_time; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.discussion_time IS 'Copied from "policy" table at creation of issue';


--
-- Name: COLUMN issue.verification_time; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.verification_time IS 'Copied from "policy" table at creation of issue';


--
-- Name: COLUMN issue.voting_time; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.voting_time IS 'Copied from "policy" table at creation of issue';


--
-- Name: COLUMN issue.snapshot; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.snapshot IS 'Point in time, when snapshot tables have been updated and "population" and *_count values were precalculated';


--
-- Name: COLUMN issue.latest_snapshot_event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.latest_snapshot_event IS 'Event type of latest snapshot for issue; Can be used to select the latest snapshot data in the snapshot tables';


--
-- Name: COLUMN issue.population; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.population IS 'Sum of "weight" column in table "direct_population_snapshot"';


--
-- Name: COLUMN issue.voter_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.voter_count IS 'Total number of direct and delegating voters; This value is related to the final voting, while "population" is related to snapshots before the final voting';


--
-- Name: COLUMN issue.status_quo_schulze_rank; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue.status_quo_schulze_rank IS 'Schulze rank of status quo, as calculated by "calculate_ranks" function';


--
-- Name: battle_participant; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW battle_participant AS
    SELECT initiative.id, initiative.issue_id FROM (issue JOIN initiative ON ((issue.id = initiative.issue_id))) WHERE initiative.admitted UNION ALL SELECT NULL::unknown AS id, issue.id AS issue_id FROM issue;


ALTER TABLE public.battle_participant OWNER TO "www-data";

--
-- Name: VIEW battle_participant; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW battle_participant IS 'Helper view for "battle_view" containing admitted initiatives plus virtual "status-quo" initiative denoted by NULL reference';


--
-- Name: direct_voter; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE direct_voter (
    issue_id integer NOT NULL,
    member_id integer NOT NULL,
    weight integer
);


ALTER TABLE public.direct_voter OWNER TO "www-data";

--
-- Name: TABLE direct_voter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE direct_voter IS 'Members having directly voted for/against initiatives of an issue; Frontends must ensure that no voters are added or removed to/from this table when the issue has been closed.';


--
-- Name: COLUMN direct_voter.weight; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_voter.weight IS 'Weight of member (1 or higher) according to "delegating_voter" table';


--
-- Name: vote; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE vote (
    issue_id integer NOT NULL,
    initiative_id integer NOT NULL,
    member_id integer NOT NULL,
    grade integer
);


ALTER TABLE public.vote OWNER TO "www-data";

--
-- Name: TABLE vote; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE vote IS 'Manual and delegated votes without abstentions; Frontends must ensure that no votes are added modified or removed when the issue has been closed.';


--
-- Name: COLUMN vote.issue_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN vote.issue_id IS 'WARNING: No index: For selections use column "initiative_id" and join via table "initiative" where neccessary';


--
-- Name: COLUMN vote.grade; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN vote.grade IS 'Values smaller than zero mean reject, values greater than zero mean acceptance, zero or missing row means abstention. Preferences are expressed by different positive or negative numbers.';


--
-- Name: battle_view; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW battle_view AS
    SELECT issue.id AS issue_id, winning_initiative.id AS winning_initiative_id, losing_initiative.id AS losing_initiative_id, sum(CASE WHEN (COALESCE(better_vote.grade, 0) > COALESCE(worse_vote.grade, 0)) THEN direct_voter.weight ELSE 0 END) AS count FROM (((((issue LEFT JOIN direct_voter ON ((issue.id = direct_voter.issue_id))) JOIN battle_participant winning_initiative ON ((issue.id = winning_initiative.issue_id))) JOIN battle_participant losing_initiative ON ((issue.id = losing_initiative.issue_id))) LEFT JOIN vote better_vote ON (((direct_voter.member_id = better_vote.member_id) AND (winning_initiative.id = better_vote.initiative_id)))) LEFT JOIN vote worse_vote ON (((direct_voter.member_id = worse_vote.member_id) AND (losing_initiative.id = worse_vote.initiative_id)))) WHERE (((issue.closed IS NOT NULL) AND (issue.cleaned IS NULL)) AND ((winning_initiative.id <> losing_initiative.id) OR (((winning_initiative.id IS NOT NULL) AND (losing_initiative.id IS NULL)) OR ((winning_initiative.id IS NULL) AND (losing_initiative.id IS NOT NULL))))) GROUP BY issue.id, winning_initiative.id, losing_initiative.id;


ALTER TABLE public.battle_view OWNER TO "www-data";

--
-- Name: VIEW battle_view; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW battle_view IS 'Number of members preferring one initiative (or status-quo) to another initiative (or status-quo); Used to fill "battle" table';


--
-- Name: contact; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE contact (
    member_id integer NOT NULL,
    other_member_id integer NOT NULL,
    public boolean DEFAULT false NOT NULL,
    CONSTRAINT cant_save_yourself_as_contact CHECK ((member_id <> other_member_id))
);


ALTER TABLE public.contact OWNER TO "www-data";

--
-- Name: TABLE contact; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE contact IS 'Contact lists';


--
-- Name: COLUMN contact.member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN contact.member_id IS 'Member having the contact list';


--
-- Name: COLUMN contact.other_member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN contact.other_member_id IS 'Member referenced in the contact list';


--
-- Name: COLUMN contact.public; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN contact.public IS 'TRUE = display contact publically';


--
-- Name: contingent; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE contingent (
    time_frame interval NOT NULL,
    text_entry_limit integer,
    initiative_limit integer
);


ALTER TABLE public.contingent OWNER TO "www-data";

--
-- Name: TABLE contingent; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE contingent IS 'Amount of text entries or initiatives a user may create within a given time frame. Only one row needs to be fulfilled for a member to be allowed to post. This table must not be empty.';


--
-- Name: COLUMN contingent.text_entry_limit; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN contingent.text_entry_limit IS 'Number of new drafts or suggestions to be submitted by each member within the given time frame';


--
-- Name: COLUMN contingent.initiative_limit; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN contingent.initiative_limit IS 'Number of new initiatives to be opened by each member within a given time frame';


--
-- Name: opinion; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE opinion (
    initiative_id integer NOT NULL,
    suggestion_id bigint NOT NULL,
    member_id integer NOT NULL,
    degree smallint NOT NULL,
    fulfilled boolean DEFAULT false NOT NULL,
    CONSTRAINT opinion_degree_check CHECK ((((degree >= (-2)) AND (degree <= 2)) AND (degree <> 0)))
);


ALTER TABLE public.opinion OWNER TO "www-data";

--
-- Name: TABLE opinion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE opinion IS 'Opinion on suggestions (criticism related to initiatives); Frontends must ensure that opinions are not created modified or deleted when related to fully_frozen or closed issues.';


--
-- Name: COLUMN opinion.degree; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN opinion.degree IS '2 = fulfillment required for support; 1 = fulfillment desired; -1 = fulfillment unwanted; -2 = fulfillment cancels support';


--
-- Name: critical_opinion; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW critical_opinion AS
    SELECT opinion.initiative_id, opinion.suggestion_id, opinion.member_id, opinion.degree, opinion.fulfilled FROM opinion WHERE (((opinion.degree = 2) AND (opinion.fulfilled = false)) OR ((opinion.degree = (-2)) AND (opinion.fulfilled = true)));


ALTER TABLE public.critical_opinion OWNER TO "www-data";

--
-- Name: VIEW critical_opinion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW critical_opinion IS 'Opinions currently causing dissatisfaction';


--
-- Name: draft; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE draft (
    initiative_id integer NOT NULL,
    id bigint NOT NULL,
    created timestamp with time zone DEFAULT now() NOT NULL,
    author_id integer NOT NULL,
    formatting_engine text,
    content text NOT NULL,
    text_search_data tsvector
);


ALTER TABLE public.draft OWNER TO "www-data";

--
-- Name: TABLE draft; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE draft IS 'Drafts of initiatives to solve issues; Frontends must ensure that new drafts for initiatives of half_frozen, fully_frozen or closed issues can''t be created.';


--
-- Name: COLUMN draft.formatting_engine; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN draft.formatting_engine IS 'Allows different formatting engines (i.e. wiki formats) to be used';


--
-- Name: COLUMN draft.content; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN draft.content IS 'Text of the draft in a format depending on the field "formatting_engine"';


--
-- Name: current_draft; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW current_draft AS
    SELECT draft.initiative_id, draft.id, draft.created, draft.author_id, draft.formatting_engine, draft.content, draft.text_search_data FROM ((SELECT initiative.id AS initiative_id, max(draft.id) AS draft_id FROM (initiative JOIN draft ON ((initiative.id = draft.initiative_id))) GROUP BY initiative.id) subquery JOIN draft ON ((subquery.draft_id = draft.id)));


ALTER TABLE public.current_draft OWNER TO "www-data";

--
-- Name: VIEW current_draft; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW current_draft IS 'All latest drafts for each initiative';


--
-- Name: delegating_interest_snapshot; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE delegating_interest_snapshot (
    issue_id integer NOT NULL,
    event snapshot_event NOT NULL,
    member_id integer NOT NULL,
    weight integer,
    scope delegation_scope NOT NULL,
    delegate_member_ids integer[] NOT NULL
);


ALTER TABLE public.delegating_interest_snapshot OWNER TO "www-data";

--
-- Name: TABLE delegating_interest_snapshot; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE delegating_interest_snapshot IS 'Delegations increasing the weight of entries in the "direct_interest_snapshot" table';


--
-- Name: COLUMN delegating_interest_snapshot.event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_interest_snapshot.event IS 'Reason for snapshot, see "snapshot_event" type for details';


--
-- Name: COLUMN delegating_interest_snapshot.member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_interest_snapshot.member_id IS 'Delegating member';


--
-- Name: COLUMN delegating_interest_snapshot.weight; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_interest_snapshot.weight IS 'Intermediate weight';


--
-- Name: COLUMN delegating_interest_snapshot.delegate_member_ids; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_interest_snapshot.delegate_member_ids IS 'Chain of members who act as delegates; last entry referes to "member_id" column of table "direct_interest_snapshot"';


--
-- Name: delegating_population_snapshot; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE delegating_population_snapshot (
    issue_id integer NOT NULL,
    event snapshot_event NOT NULL,
    member_id integer NOT NULL,
    weight integer,
    scope delegation_scope NOT NULL,
    delegate_member_ids integer[] NOT NULL
);


ALTER TABLE public.delegating_population_snapshot OWNER TO "www-data";

--
-- Name: COLUMN delegating_population_snapshot.event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_population_snapshot.event IS 'Reason for snapshot, see "snapshot_event" type for details';


--
-- Name: COLUMN delegating_population_snapshot.member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_population_snapshot.member_id IS 'Delegating member';


--
-- Name: COLUMN delegating_population_snapshot.weight; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_population_snapshot.weight IS 'Intermediate weight';


--
-- Name: COLUMN delegating_population_snapshot.delegate_member_ids; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_population_snapshot.delegate_member_ids IS 'Chain of members who act as delegates; last entry referes to "member_id" column of table "direct_population_snapshot"';


--
-- Name: delegating_voter; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE delegating_voter (
    issue_id integer NOT NULL,
    member_id integer NOT NULL,
    weight integer,
    scope delegation_scope NOT NULL,
    delegate_member_ids integer[] NOT NULL
);


ALTER TABLE public.delegating_voter OWNER TO "www-data";

--
-- Name: TABLE delegating_voter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE delegating_voter IS 'Delegations increasing the weight of entries in the "direct_voter" table';


--
-- Name: COLUMN delegating_voter.member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_voter.member_id IS 'Delegating member';


--
-- Name: COLUMN delegating_voter.weight; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_voter.weight IS 'Intermediate weight';


--
-- Name: COLUMN delegating_voter.delegate_member_ids; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN delegating_voter.delegate_member_ids IS 'Chain of members who act as delegates; last entry referes to "member_id" column of table "direct_voter"';


--
-- Name: delegation_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE delegation_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.delegation_id_seq OWNER TO "www-data";

--
-- Name: delegation_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE delegation_id_seq OWNED BY delegation.id;


--
-- Name: delegation_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('delegation_id_seq', 1, true);


--
-- Name: direct_interest_snapshot; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE direct_interest_snapshot (
    issue_id integer NOT NULL,
    event snapshot_event NOT NULL,
    member_id integer NOT NULL,
    weight integer
);


ALTER TABLE public.direct_interest_snapshot OWNER TO "www-data";

--
-- Name: TABLE direct_interest_snapshot; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE direct_interest_snapshot IS 'Snapshot of active members having an "interest" in the "issue"';


--
-- Name: COLUMN direct_interest_snapshot.event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_interest_snapshot.event IS 'Reason for snapshot, see "snapshot_event" type for details';


--
-- Name: COLUMN direct_interest_snapshot.weight; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_interest_snapshot.weight IS 'Weight of member (1 or higher) according to "delegating_interest_snapshot"';


--
-- Name: direct_population_snapshot; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE direct_population_snapshot (
    issue_id integer NOT NULL,
    event snapshot_event NOT NULL,
    member_id integer NOT NULL,
    weight integer
);


ALTER TABLE public.direct_population_snapshot OWNER TO "www-data";

--
-- Name: TABLE direct_population_snapshot; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE direct_population_snapshot IS 'Delegations increasing the weight of entries in the "direct_population_snapshot" table';


--
-- Name: COLUMN direct_population_snapshot.event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_population_snapshot.event IS 'Reason for snapshot, see "snapshot_event" type for details';


--
-- Name: COLUMN direct_population_snapshot.weight; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_population_snapshot.weight IS 'Weight of member (1 or higher) according to "delegating_population_snapshot"';


--
-- Name: direct_supporter_snapshot; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE direct_supporter_snapshot (
    issue_id integer NOT NULL,
    initiative_id integer NOT NULL,
    event snapshot_event NOT NULL,
    member_id integer NOT NULL,
    draft_id bigint NOT NULL,
    informed boolean NOT NULL,
    satisfied boolean NOT NULL
);


ALTER TABLE public.direct_supporter_snapshot OWNER TO "www-data";

--
-- Name: TABLE direct_supporter_snapshot; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE direct_supporter_snapshot IS 'Snapshot of supporters of initiatives (weight is stored in "direct_interest_snapshot")';


--
-- Name: COLUMN direct_supporter_snapshot.issue_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_supporter_snapshot.issue_id IS 'WARNING: No index: For selections use column "initiative_id" and join via table "initiative" where neccessary';


--
-- Name: COLUMN direct_supporter_snapshot.event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_supporter_snapshot.event IS 'Reason for snapshot, see "snapshot_event" type for details';


--
-- Name: COLUMN direct_supporter_snapshot.informed; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_supporter_snapshot.informed IS 'Supporter has seen the latest draft of the initiative';


--
-- Name: COLUMN direct_supporter_snapshot.satisfied; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN direct_supporter_snapshot.satisfied IS 'Supporter has no "critical_opinion"s';


--
-- Name: draft_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE draft_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.draft_id_seq OWNER TO "www-data";

--
-- Name: draft_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE draft_id_seq OWNED BY draft.id;


--
-- Name: draft_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('draft_id_seq', 4, true);


--
-- Name: event; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE event (
    id bigint NOT NULL,
    occurrence timestamp with time zone DEFAULT now() NOT NULL,
    event event_type NOT NULL,
    member_id integer,
    issue_id integer,
    state issue_state,
    initiative_id integer,
    draft_id bigint,
    suggestion_id bigint,
    CONSTRAINT event_state_check CHECK ((state <> 'calculation'::issue_state)),
    CONSTRAINT null_constraints_for_initiative_creation_or_revocation_or_new_d CHECK (((event <> ALL (ARRAY['initiative_created_in_new_issue'::event_type, 'initiative_created_in_existing_issue'::event_type, 'initiative_revoked'::event_type, 'new_draft_created'::event_type])) OR ((((((member_id IS NOT NULL) AND (issue_id IS NOT NULL)) AND (state IS NOT NULL)) AND (initiative_id IS NOT NULL)) AND (draft_id IS NOT NULL)) AND (suggestion_id IS NULL)))),
    CONSTRAINT null_constraints_for_issue_state_changed CHECK (((event <> 'issue_state_changed'::event_type) OR ((((((member_id IS NULL) AND (issue_id IS NOT NULL)) AND (state IS NOT NULL)) AND (initiative_id IS NULL)) AND (draft_id IS NULL)) AND (suggestion_id IS NULL)))),
    CONSTRAINT null_constraints_for_suggestion_creation CHECK (((event <> 'suggestion_created'::event_type) OR ((((((member_id IS NOT NULL) AND (issue_id IS NOT NULL)) AND (state IS NOT NULL)) AND (initiative_id IS NOT NULL)) AND (draft_id IS NULL)) AND (suggestion_id IS NOT NULL))))
);


ALTER TABLE public.event OWNER TO "www-data";

--
-- Name: TABLE event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE event IS 'Event table, automatically filled by triggers';


--
-- Name: COLUMN event.occurrence; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN event.occurrence IS 'Point in time, when event occurred';


--
-- Name: COLUMN event.event; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN event.event IS 'Type of event (see TYPE "event_type")';


--
-- Name: COLUMN event.member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN event.member_id IS 'Member who caused the event, if applicable';


--
-- Name: COLUMN event.state; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN event.state IS 'If issue_id is set: state of affected issue; If state changed: new state';


--
-- Name: event_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE event_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.event_id_seq OWNER TO "www-data";

--
-- Name: event_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE event_id_seq OWNED BY event.id;


--
-- Name: event_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('event_id_seq', 8, true);


--
-- Name: ignored_initiative; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE ignored_initiative (
    initiative_id integer NOT NULL,
    member_id integer NOT NULL
);


ALTER TABLE public.ignored_initiative OWNER TO "www-data";

--
-- Name: TABLE ignored_initiative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE ignored_initiative IS 'Possibility to filter initiatives';


--
-- Name: ignored_member; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE ignored_member (
    member_id integer NOT NULL,
    other_member_id integer NOT NULL
);


ALTER TABLE public.ignored_member OWNER TO "www-data";

--
-- Name: TABLE ignored_member; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE ignored_member IS 'Possibility to filter other members';


--
-- Name: COLUMN ignored_member.member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN ignored_member.member_id IS 'Member ignoring someone';


--
-- Name: COLUMN ignored_member.other_member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN ignored_member.other_member_id IS 'Member being ignored';


--
-- Name: interest; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE interest (
    issue_id integer NOT NULL,
    member_id integer NOT NULL
);


ALTER TABLE public.interest OWNER TO "www-data";

--
-- Name: TABLE interest; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE interest IS 'Interest of members in a particular issue; Frontends must ensure that interest for fully_frozen or closed issues is not added or removed.';


--
-- Name: supporter; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE supporter (
    issue_id integer NOT NULL,
    initiative_id integer NOT NULL,
    member_id integer NOT NULL,
    draft_id bigint NOT NULL
);


ALTER TABLE public.supporter OWNER TO "www-data";

--
-- Name: TABLE supporter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE supporter IS 'Members who support an initiative (conditionally); Frontends must ensure that supporters are not added or removed from fully_frozen or closed initiatives.';


--
-- Name: COLUMN supporter.issue_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN supporter.issue_id IS 'WARNING: No index: For selections use column "initiative_id" and join via table "initiative" where neccessary';


--
-- Name: COLUMN supporter.draft_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN supporter.draft_id IS 'Latest seen draft; should always be set by a frontend, but defaults to current draft of the initiative (implemented by trigger "default_for_draft_id")';


--
-- Name: event_seen_by_member; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW event_seen_by_member AS
    SELECT member.id AS seen_by_member_id, CASE WHEN (event.state = ANY (ARRAY['voting'::issue_state, 'finished_without_winner'::issue_state, 'finished_with_winner'::issue_state])) THEN 'voting'::notify_level ELSE CASE WHEN (event.state = ANY (ARRAY['verification'::issue_state, 'canceled_after_revocation_during_verification'::issue_state, 'canceled_no_initiative_admitted'::issue_state])) THEN 'verification'::notify_level ELSE CASE WHEN (event.state = ANY (ARRAY['discussion'::issue_state, 'canceled_after_revocation_during_discussion'::issue_state])) THEN 'discussion'::notify_level ELSE 'all'::notify_level END END END AS notify_level, event.id, event.occurrence, event.event, event.member_id, event.issue_id, event.state, event.initiative_id, event.draft_id, event.suggestion_id FROM (((((((member CROSS JOIN event) LEFT JOIN issue ON ((event.issue_id = issue.id))) LEFT JOIN membership ON (((member.id = membership.member_id) AND (issue.area_id = membership.area_id)))) LEFT JOIN interest ON (((member.id = interest.member_id) AND (event.issue_id = interest.issue_id)))) LEFT JOIN supporter ON (((member.id = supporter.member_id) AND (event.initiative_id = supporter.initiative_id)))) LEFT JOIN ignored_member ON (((member.id = ignored_member.member_id) AND (event.member_id = ignored_member.other_member_id)))) LEFT JOIN ignored_initiative ON (((member.id = ignored_initiative.member_id) AND (event.initiative_id = ignored_initiative.initiative_id)))) WHERE (((((supporter.member_id IS NOT NULL) OR (interest.member_id IS NOT NULL)) OR ((membership.member_id IS NOT NULL) AND (event.event = ANY (ARRAY['issue_state_changed'::event_type, 'initiative_created_in_new_issue'::event_type, 'initiative_created_in_existing_issue'::event_type, 'initiative_revoked'::event_type])))) AND (ignored_member.member_id IS NULL)) AND (ignored_initiative.member_id IS NULL));


ALTER TABLE public.event_seen_by_member OWNER TO "www-data";

--
-- Name: VIEW event_seen_by_member; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW event_seen_by_member IS 'Events as seen by a member, depending on its memberships, interests and support, but ignoring members "notify_level"';


--
-- Name: session; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE session (
    ident text NOT NULL,
    additional_secret text,
    expiry timestamp with time zone DEFAULT (now() + '24:00:00'::interval) NOT NULL,
    member_id bigint,
    lang text
);


ALTER TABLE public.session OWNER TO "www-data";

--
-- Name: TABLE session; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE session IS 'Sessions, i.e. for a web-frontend or API layer';


--
-- Name: COLUMN session.ident; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN session.ident IS 'Secret session identifier (i.e. random string)';


--
-- Name: COLUMN session.additional_secret; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN session.additional_secret IS 'Additional field to store a secret, which can be used against CSRF attacks';


--
-- Name: COLUMN session.member_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN session.member_id IS 'Reference to member, who is logged in';


--
-- Name: COLUMN session.lang; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN session.lang IS 'Language code of the selected language';


--
-- Name: expired_session; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW expired_session AS
    SELECT session.ident, session.additional_secret, session.expiry, session.member_id, session.lang FROM session WHERE (now() > session.expiry);


ALTER TABLE public.expired_session OWNER TO "www-data";

--
-- Name: VIEW expired_session; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW expired_session IS 'View containing all expired sessions where DELETE is possible';


--
-- Name: initiative_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE initiative_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.initiative_id_seq OWNER TO "www-data";

--
-- Name: initiative_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE initiative_id_seq OWNED BY initiative.id;


--
-- Name: initiative_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('initiative_id_seq', 4, true);


--
-- Name: initiative_setting; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE initiative_setting (
    member_id integer NOT NULL,
    key text NOT NULL,
    initiative_id integer NOT NULL,
    value text NOT NULL
);


ALTER TABLE public.initiative_setting OWNER TO "www-data";

--
-- Name: TABLE initiative_setting; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE initiative_setting IS 'Place for frontend to store initiative specific settings of members as strings';


--
-- Name: initiator; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE initiator (
    initiative_id integer NOT NULL,
    member_id integer NOT NULL,
    accepted boolean
);


ALTER TABLE public.initiator OWNER TO "www-data";

--
-- Name: TABLE initiator; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE initiator IS 'Members who are allowed to post new drafts; Frontends must ensure that initiators are not added or removed from half_frozen, fully_frozen or closed initiatives.';


--
-- Name: COLUMN initiator.accepted; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN initiator.accepted IS 'If "accepted" is NULL, then the member was invited to be a co-initiator, but has not answered yet. If it is TRUE, the member has accepted the invitation, if it is FALSE, the member has rejected the invitation.';


--
-- Name: issue_comment; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE issue_comment (
    issue_id integer NOT NULL,
    member_id integer NOT NULL,
    changed timestamp with time zone DEFAULT now() NOT NULL,
    formatting_engine text,
    content text NOT NULL,
    text_search_data tsvector
);


ALTER TABLE public.issue_comment OWNER TO "www-data";

--
-- Name: TABLE issue_comment; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE issue_comment IS 'Place to store free comments of members related to issues';


--
-- Name: COLUMN issue_comment.changed; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN issue_comment.changed IS 'Time the comment was last changed';


--
-- Name: issue_delegation; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW issue_delegation AS
    SELECT DISTINCT ON (issue.id, delegation.truster_id) issue.id AS issue_id, delegation.id, delegation.truster_id, delegation.trustee_id, delegation.scope FROM ((((issue JOIN area ON ((area.id = issue.area_id))) JOIN delegation ON ((((delegation.unit_id = area.unit_id) OR (delegation.area_id = area.id)) OR (delegation.issue_id = issue.id)))) JOIN member ON ((delegation.truster_id = member.id))) JOIN privilege ON (((area.unit_id = privilege.unit_id) AND (delegation.truster_id = privilege.member_id)))) WHERE (member.active AND privilege.voting_right) ORDER BY issue.id, delegation.truster_id, delegation.scope DESC;


ALTER TABLE public.issue_delegation OWNER TO "www-data";

--
-- Name: VIEW issue_delegation; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW issue_delegation IS 'Issue delegations where trusters are active and have voting right';


--
-- Name: issue_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE issue_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.issue_id_seq OWNER TO "www-data";

--
-- Name: issue_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE issue_id_seq OWNED BY issue.id;


--
-- Name: issue_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('issue_id_seq', 2, true);


--
-- Name: issue_setting; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE issue_setting (
    member_id integer NOT NULL,
    key text NOT NULL,
    issue_id integer NOT NULL,
    value text NOT NULL
);


ALTER TABLE public.issue_setting OWNER TO "www-data";

--
-- Name: TABLE issue_setting; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE issue_setting IS 'Place for frontend to store issue specific settings of members as strings';


--
-- Name: issue_with_ranks_missing; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW issue_with_ranks_missing AS
    SELECT issue.id, issue.area_id, issue.policy_id, issue.state, issue.created, issue.accepted, issue.half_frozen, issue.fully_frozen, issue.closed, issue.ranks_available, issue.cleaned, issue.admission_time, issue.discussion_time, issue.verification_time, issue.voting_time, issue.snapshot, issue.latest_snapshot_event, issue.population, issue.voter_count, issue.status_quo_schulze_rank FROM issue WHERE (((issue.fully_frozen IS NOT NULL) AND (issue.closed IS NOT NULL)) AND (issue.ranks_available = false));


ALTER TABLE public.issue_with_ranks_missing OWNER TO "www-data";

--
-- Name: VIEW issue_with_ranks_missing; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW issue_with_ranks_missing IS 'Issues where voting was finished, but no ranks have been calculated yet';


--
-- Name: liquid_feedback_version; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW liquid_feedback_version AS
    SELECT subquery.string, subquery.major, subquery.minor, subquery.revision FROM (VALUES ('2.0.11'::text,2,0,11)) subquery(string, major, minor, revision);


ALTER TABLE public.liquid_feedback_version OWNER TO "www-data";

--
-- Name: member_application; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE member_application (
    id bigint NOT NULL,
    member_id integer NOT NULL,
    name text NOT NULL,
    comment text,
    access_level application_access_level NOT NULL,
    key text NOT NULL,
    last_usage timestamp with time zone
);


ALTER TABLE public.member_application OWNER TO "www-data";

--
-- Name: TABLE member_application; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE member_application IS 'Registered application being allowed to use the API';


--
-- Name: member_application_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE member_application_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.member_application_id_seq OWNER TO "www-data";

--
-- Name: member_application_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE member_application_id_seq OWNED BY member_application.id;


--
-- Name: member_application_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('member_application_id_seq', 1, false);


--
-- Name: opening_draft; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW opening_draft AS
    SELECT draft.initiative_id, draft.id, draft.created, draft.author_id, draft.formatting_engine, draft.content, draft.text_search_data FROM ((SELECT initiative.id AS initiative_id, min(draft.id) AS draft_id FROM (initiative JOIN draft ON ((initiative.id = draft.initiative_id))) GROUP BY initiative.id) subquery JOIN draft ON ((subquery.draft_id = draft.id)));


ALTER TABLE public.opening_draft OWNER TO "www-data";

--
-- Name: VIEW opening_draft; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW opening_draft IS 'First drafts of all initiatives';


--
-- Name: suggestion; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE suggestion (
    initiative_id integer NOT NULL,
    id bigint NOT NULL,
    draft_id bigint NOT NULL,
    created timestamp with time zone DEFAULT now() NOT NULL,
    author_id integer NOT NULL,
    name text NOT NULL,
    formatting_engine text,
    content text DEFAULT ''::text NOT NULL,
    text_search_data tsvector,
    minus2_unfulfilled_count integer,
    minus2_fulfilled_count integer,
    minus1_unfulfilled_count integer,
    minus1_fulfilled_count integer,
    plus1_unfulfilled_count integer,
    plus1_fulfilled_count integer,
    plus2_unfulfilled_count integer,
    plus2_fulfilled_count integer
);


ALTER TABLE public.suggestion OWNER TO "www-data";

--
-- Name: TABLE suggestion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE suggestion IS 'Suggestions to initiators, to change the current draft; must not be deleted explicitly, as they vanish automatically if the last opinion is deleted';


--
-- Name: COLUMN suggestion.draft_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.draft_id IS 'Draft, which the author has seen when composing the suggestion; should always be set by a frontend, but defaults to current draft of the initiative (implemented by trigger "default_for_draft_id")';


--
-- Name: COLUMN suggestion.minus2_unfulfilled_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.minus2_unfulfilled_count IS 'Calculated from table "direct_supporter_snapshot", not requiring informed supporters';


--
-- Name: COLUMN suggestion.minus2_fulfilled_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.minus2_fulfilled_count IS 'Calculated from table "direct_supporter_snapshot", not requiring informed supporters';


--
-- Name: COLUMN suggestion.minus1_unfulfilled_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.minus1_unfulfilled_count IS 'Calculated from table "direct_supporter_snapshot", not requiring informed supporters';


--
-- Name: COLUMN suggestion.minus1_fulfilled_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.minus1_fulfilled_count IS 'Calculated from table "direct_supporter_snapshot", not requiring informed supporters';


--
-- Name: COLUMN suggestion.plus1_unfulfilled_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.plus1_unfulfilled_count IS 'Calculated from table "direct_supporter_snapshot", not requiring informed supporters';


--
-- Name: COLUMN suggestion.plus1_fulfilled_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.plus1_fulfilled_count IS 'Calculated from table "direct_supporter_snapshot", not requiring informed supporters';


--
-- Name: COLUMN suggestion.plus2_unfulfilled_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.plus2_unfulfilled_count IS 'Calculated from table "direct_supporter_snapshot", not requiring informed supporters';


--
-- Name: COLUMN suggestion.plus2_fulfilled_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN suggestion.plus2_fulfilled_count IS 'Calculated from table "direct_supporter_snapshot", not requiring informed supporters';


--
-- Name: member_contingent; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW member_contingent AS
    SELECT member.id AS member_id, contingent.time_frame, CASE WHEN (contingent.text_entry_limit IS NOT NULL) THEN ((SELECT count(1) AS count FROM draft WHERE ((draft.author_id = member.id) AND (draft.created > (now() - contingent.time_frame)))) + (SELECT count(1) AS count FROM suggestion WHERE ((suggestion.author_id = member.id) AND (suggestion.created > (now() - contingent.time_frame))))) ELSE NULL::bigint END AS text_entry_count, contingent.text_entry_limit, CASE WHEN (contingent.initiative_limit IS NOT NULL) THEN (SELECT count(1) AS count FROM opening_draft WHERE ((opening_draft.author_id = member.id) AND (opening_draft.created > (now() - contingent.time_frame)))) ELSE NULL::bigint END AS initiative_count, contingent.initiative_limit FROM (member CROSS JOIN contingent);


ALTER TABLE public.member_contingent OWNER TO "www-data";

--
-- Name: VIEW member_contingent; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW member_contingent IS 'Actual counts of text entries and initiatives are calculated per member for each limit in the "contingent" table.';


--
-- Name: COLUMN member_contingent.text_entry_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member_contingent.text_entry_count IS 'Only calculated when "text_entry_limit" is not null in the same row';


--
-- Name: COLUMN member_contingent.initiative_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member_contingent.initiative_count IS 'Only calculated when "initiative_limit" is not null in the same row';


--
-- Name: member_contingent_left; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW member_contingent_left AS
    SELECT member_contingent.member_id, max((member_contingent.text_entry_limit - member_contingent.text_entry_count)) AS text_entries_left, max((member_contingent.initiative_limit - member_contingent.initiative_count)) AS initiatives_left FROM member_contingent GROUP BY member_contingent.member_id;


ALTER TABLE public.member_contingent_left OWNER TO "www-data";

--
-- Name: VIEW member_contingent_left; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW member_contingent_left IS 'Amount of text entries or initiatives which can be posted now instantly by a member. This view should be used by a frontend to determine, if the contingent for posting is exhausted.';


--
-- Name: member_count; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE member_count (
    calculated timestamp with time zone DEFAULT now() NOT NULL,
    total_count integer NOT NULL
);


ALTER TABLE public.member_count OWNER TO "www-data";

--
-- Name: TABLE member_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE member_count IS 'Contains one row which contains the total count of active(!) members and a timestamp indicating when the total member count and area member counts were calculated';


--
-- Name: COLUMN member_count.calculated; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member_count.calculated IS 'timestamp indicating when the total member count and area member counts were calculated';


--
-- Name: COLUMN member_count.total_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member_count.total_count IS 'Total count of active(!) members';


--
-- Name: member_count_view; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW member_count_view AS
    SELECT count(1) AS total_count FROM member WHERE member.active;


ALTER TABLE public.member_count_view OWNER TO "www-data";

--
-- Name: VIEW member_count_view; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW member_count_view IS 'View used to update "member_count" table';


--
-- Name: member_history; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE member_history (
    id bigint NOT NULL,
    member_id integer NOT NULL,
    until timestamp with time zone DEFAULT now() NOT NULL,
    active boolean NOT NULL,
    name text NOT NULL
);


ALTER TABLE public.member_history OWNER TO "www-data";

--
-- Name: TABLE member_history; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE member_history IS 'Filled by trigger; keeps information about old names and active flag of members';


--
-- Name: COLUMN member_history.id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member_history.id IS 'Primary key, which can be used to sort entries correctly (and time warp resistant)';


--
-- Name: COLUMN member_history.until; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member_history.until IS 'Timestamp until the data was valid';


--
-- Name: member_history_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE member_history_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.member_history_id_seq OWNER TO "www-data";

--
-- Name: member_history_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE member_history_id_seq OWNED BY member_history.id;


--
-- Name: member_history_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('member_history_id_seq', 1, false);


--
-- Name: member_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE member_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.member_id_seq OWNER TO "www-data";

--
-- Name: member_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE member_id_seq OWNED BY member.id;


--
-- Name: member_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('member_id_seq', 6, true);


--
-- Name: member_image; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE member_image (
    member_id integer NOT NULL,
    image_type member_image_type NOT NULL,
    scaled boolean NOT NULL,
    content_type text,
    data bytea NOT NULL
);


ALTER TABLE public.member_image OWNER TO "www-data";

--
-- Name: TABLE member_image; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE member_image IS 'Images of members';


--
-- Name: COLUMN member_image.scaled; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN member_image.scaled IS 'FALSE for original image, TRUE for scaled version of the image';


--
-- Name: member_relation_setting; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE member_relation_setting (
    member_id integer NOT NULL,
    key text NOT NULL,
    other_member_id integer NOT NULL,
    value text NOT NULL
);


ALTER TABLE public.member_relation_setting OWNER TO "www-data";

--
-- Name: TABLE member_relation_setting; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE member_relation_setting IS 'Place to store a frontend specific setting related to relations between members as a string';


--
-- Name: non_voter; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE non_voter (
    issue_id integer NOT NULL,
    member_id integer NOT NULL
);


ALTER TABLE public.non_voter OWNER TO "www-data";

--
-- Name: TABLE non_voter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE non_voter IS 'Members who decided to not vote directly on an issue';


--
-- Name: notification_sent; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE notification_sent (
    event_id bigint NOT NULL
);


ALTER TABLE public.notification_sent OWNER TO "www-data";

--
-- Name: TABLE notification_sent; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE notification_sent IS 'This table stores one row with the last event_id, for which notifications have been sent out';


--
-- Name: open_issue; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW open_issue AS
    SELECT issue.id, issue.area_id, issue.policy_id, issue.state, issue.created, issue.accepted, issue.half_frozen, issue.fully_frozen, issue.closed, issue.ranks_available, issue.cleaned, issue.admission_time, issue.discussion_time, issue.verification_time, issue.voting_time, issue.snapshot, issue.latest_snapshot_event, issue.population, issue.voter_count, issue.status_quo_schulze_rank FROM issue WHERE (issue.closed IS NULL);


ALTER TABLE public.open_issue OWNER TO "www-data";

--
-- Name: VIEW open_issue; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW open_issue IS 'All open issues';


--
-- Name: policy; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE policy (
    id integer NOT NULL,
    index integer NOT NULL,
    active boolean DEFAULT true NOT NULL,
    name text NOT NULL,
    description text DEFAULT ''::text NOT NULL,
    admission_time interval NOT NULL,
    discussion_time interval NOT NULL,
    verification_time interval NOT NULL,
    voting_time interval NOT NULL,
    issue_quorum_num integer NOT NULL,
    issue_quorum_den integer NOT NULL,
    initiative_quorum_num integer NOT NULL,
    initiative_quorum_den integer NOT NULL,
    direct_majority_num integer DEFAULT 1 NOT NULL,
    direct_majority_den integer DEFAULT 2 NOT NULL,
    direct_majority_strict boolean DEFAULT true NOT NULL,
    direct_majority_positive integer DEFAULT 0 NOT NULL,
    direct_majority_non_negative integer DEFAULT 0 NOT NULL,
    indirect_majority_num integer DEFAULT 1 NOT NULL,
    indirect_majority_den integer DEFAULT 2 NOT NULL,
    indirect_majority_strict boolean DEFAULT true NOT NULL,
    indirect_majority_positive integer DEFAULT 0 NOT NULL,
    indirect_majority_non_negative integer DEFAULT 0 NOT NULL,
    no_reverse_beat_path boolean DEFAULT true NOT NULL,
    no_multistage_majority boolean DEFAULT false NOT NULL
);


ALTER TABLE public.policy OWNER TO "www-data";

--
-- Name: TABLE policy; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE policy IS 'Policies for a particular proceeding type (timelimits, quorum)';


--
-- Name: COLUMN policy.index; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.index IS 'Determines the order in listings';


--
-- Name: COLUMN policy.active; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.active IS 'TRUE = policy can be used for new issues';


--
-- Name: COLUMN policy.admission_time; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.admission_time IS 'Maximum duration of issue state ''admission''; Maximum time an issue stays open without being "accepted"';


--
-- Name: COLUMN policy.discussion_time; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.discussion_time IS 'Duration of issue state ''discussion''; Regular time until an issue is "half_frozen" after being "accepted"';


--
-- Name: COLUMN policy.verification_time; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.verification_time IS 'Duration of issue state ''verification''; Regular time until an issue is "fully_frozen" (e.g. entering issue state ''voting'') after being "half_frozen"';


--
-- Name: COLUMN policy.voting_time; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.voting_time IS 'Duration of issue state ''voting''; Time after an issue is "fully_frozen" but not "closed" (duration of issue state ''voting'')';


--
-- Name: COLUMN policy.issue_quorum_num; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.issue_quorum_num IS 'Numerator of potential supporter quorum to be reached by one initiative of an issue to be "accepted" and enter issue state ''discussion''';


--
-- Name: COLUMN policy.issue_quorum_den; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.issue_quorum_den IS 'Denominator of potential supporter quorum to be reached by one initiative of an issue to be "accepted" and enter issue state ''discussion''';


--
-- Name: COLUMN policy.initiative_quorum_num; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.initiative_quorum_num IS 'Numerator of satisfied supporter quorum  to be reached by an initiative to be "admitted" for voting';


--
-- Name: COLUMN policy.initiative_quorum_den; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.initiative_quorum_den IS 'Denominator of satisfied supporter quorum to be reached by an initiative to be "admitted" for voting';


--
-- Name: COLUMN policy.direct_majority_num; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.direct_majority_num IS 'Numerator of fraction of neccessary direct majority for initiatives to be attainable as winner';


--
-- Name: COLUMN policy.direct_majority_den; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.direct_majority_den IS 'Denominator of fraction of neccessary direct majority for initaitives to be attainable as winner';


--
-- Name: COLUMN policy.direct_majority_strict; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.direct_majority_strict IS 'If TRUE, then the direct majority must be strictly greater than "direct_majority_num"/"direct_majority_den", otherwise it may also be equal.';


--
-- Name: COLUMN policy.direct_majority_positive; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.direct_majority_positive IS 'Absolute number of "positive_votes" neccessary for an initiative to be attainable as winner';


--
-- Name: COLUMN policy.direct_majority_non_negative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.direct_majority_non_negative IS 'Absolute number of sum of "positive_votes" and abstentions neccessary for an initiative to be attainable as winner';


--
-- Name: COLUMN policy.indirect_majority_num; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.indirect_majority_num IS 'Numerator of fraction of neccessary indirect majority (through beat path) for initiatives to be attainable as winner';


--
-- Name: COLUMN policy.indirect_majority_den; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.indirect_majority_den IS 'Denominator of fraction of neccessary indirect majority (through beat path) for initiatives to be attainable as winner';


--
-- Name: COLUMN policy.indirect_majority_strict; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.indirect_majority_strict IS 'If TRUE, then the indirect majority must be strictly greater than "indirect_majority_num"/"indirect_majority_den", otherwise it may also be equal.';


--
-- Name: COLUMN policy.indirect_majority_positive; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.indirect_majority_positive IS 'Absolute number of votes in favor of the winner neccessary in a beat path to the status quo for an initaitive to be attainable as winner';


--
-- Name: COLUMN policy.indirect_majority_non_negative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.indirect_majority_non_negative IS 'Absolute number of sum of votes in favor and abstentions in a beat path to the status quo for an initiative to be attainable as winner';


--
-- Name: COLUMN policy.no_reverse_beat_path; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.no_reverse_beat_path IS 'Causes initiatives with "reverse_beat_path" flag to not be "eligible", thus disallowing them to be winner. See comment on column "initiative"."reverse_beat_path". This option ensures both that a winning initiative is never tied in a (weak) condorcet paradox with the status quo and a winning initiative always beats the status quo directly with a simple majority.';


--
-- Name: COLUMN policy.no_multistage_majority; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN policy.no_multistage_majority IS 'Causes initiatives with "multistage_majority" flag to not be "eligible", thus disallowing them to be winner. See comment on column "initiative"."multistage_majority". This disqualifies initiatives which could cause an instable result. An instable result in this meaning is a result such that repeating the ballot with same preferences but with the winner of the first ballot as status quo would lead to a different winner in the second ballot. If there are no direct majorities required for the winner, or if in direct comparison only simple majorities are required and "no_reverse_beat_path" is true, then results are always stable and this flag does not have any effect on the winner (but still affects the "eligible" flag of an "initiative").';


--
-- Name: policy_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE policy_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.policy_id_seq OWNER TO "www-data";

--
-- Name: policy_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE policy_id_seq OWNED BY policy.id;


--
-- Name: policy_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('policy_id_seq', 2, true);


--
-- Name: rendered_draft; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE rendered_draft (
    draft_id bigint NOT NULL,
    format text NOT NULL,
    content text NOT NULL
);


ALTER TABLE public.rendered_draft OWNER TO "www-data";

--
-- Name: TABLE rendered_draft; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE rendered_draft IS 'This table may be used by frontends to cache "rendered" drafts (e.g. HTML output generated from wiki text)';


--
-- Name: rendered_issue_comment; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE rendered_issue_comment (
    issue_id integer NOT NULL,
    member_id integer NOT NULL,
    format text NOT NULL,
    content text NOT NULL
);


ALTER TABLE public.rendered_issue_comment OWNER TO "www-data";

--
-- Name: TABLE rendered_issue_comment; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE rendered_issue_comment IS 'This table may be used by frontends to cache "rendered" issue comments (e.g. HTML output generated from wiki text)';


--
-- Name: rendered_member_statement; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE rendered_member_statement (
    member_id bigint NOT NULL,
    format text NOT NULL,
    content text NOT NULL
);


ALTER TABLE public.rendered_member_statement OWNER TO "www-data";

--
-- Name: TABLE rendered_member_statement; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE rendered_member_statement IS 'This table may be used by frontends to cache "rendered" member statements (e.g. HTML output generated from wiki text)';


--
-- Name: rendered_suggestion; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE rendered_suggestion (
    suggestion_id bigint NOT NULL,
    format text NOT NULL,
    content text NOT NULL
);


ALTER TABLE public.rendered_suggestion OWNER TO "www-data";

--
-- Name: TABLE rendered_suggestion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE rendered_suggestion IS 'This table may be used by frontends to cache "rendered" drafts (e.g. HTML output generated from wiki text)';


--
-- Name: rendered_voting_comment; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE rendered_voting_comment (
    issue_id integer NOT NULL,
    member_id integer NOT NULL,
    format text NOT NULL,
    content text NOT NULL
);


ALTER TABLE public.rendered_voting_comment OWNER TO "www-data";

--
-- Name: TABLE rendered_voting_comment; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE rendered_voting_comment IS 'This table may be used by frontends to cache "rendered" voting comments (e.g. HTML output generated from wiki text)';


--
-- Name: selected_event_seen_by_member; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW selected_event_seen_by_member AS
    SELECT member.id AS seen_by_member_id, CASE WHEN (event.state = ANY (ARRAY['voting'::issue_state, 'finished_without_winner'::issue_state, 'finished_with_winner'::issue_state])) THEN 'voting'::notify_level ELSE CASE WHEN (event.state = ANY (ARRAY['verification'::issue_state, 'canceled_after_revocation_during_verification'::issue_state, 'canceled_no_initiative_admitted'::issue_state])) THEN 'verification'::notify_level ELSE CASE WHEN (event.state = ANY (ARRAY['discussion'::issue_state, 'canceled_after_revocation_during_discussion'::issue_state])) THEN 'discussion'::notify_level ELSE 'all'::notify_level END END END AS notify_level, event.id, event.occurrence, event.event, event.member_id, event.issue_id, event.state, event.initiative_id, event.draft_id, event.suggestion_id FROM (((((((member CROSS JOIN event) LEFT JOIN issue ON ((event.issue_id = issue.id))) LEFT JOIN membership ON (((member.id = membership.member_id) AND (issue.area_id = membership.area_id)))) LEFT JOIN interest ON (((member.id = interest.member_id) AND (event.issue_id = interest.issue_id)))) LEFT JOIN supporter ON (((member.id = supporter.member_id) AND (event.initiative_id = supporter.initiative_id)))) LEFT JOIN ignored_member ON (((member.id = ignored_member.member_id) AND (event.member_id = ignored_member.other_member_id)))) LEFT JOIN ignored_initiative ON (((member.id = ignored_initiative.member_id) AND (event.initiative_id = ignored_initiative.initiative_id)))) WHERE (((((((member.notify_level >= 'all'::notify_level) OR ((member.notify_level >= 'voting'::notify_level) AND (event.state = ANY (ARRAY['voting'::issue_state, 'finished_without_winner'::issue_state, 'finished_with_winner'::issue_state])))) OR ((member.notify_level >= 'verification'::notify_level) AND (event.state = ANY (ARRAY['verification'::issue_state, 'canceled_after_revocation_during_verification'::issue_state, 'canceled_no_initiative_admitted'::issue_state])))) OR ((member.notify_level >= 'discussion'::notify_level) AND (event.state = ANY (ARRAY['discussion'::issue_state, 'canceled_after_revocation_during_discussion'::issue_state])))) AND (((supporter.member_id IS NOT NULL) OR (interest.member_id IS NOT NULL)) OR ((membership.member_id IS NOT NULL) AND (event.event = ANY (ARRAY['issue_state_changed'::event_type, 'initiative_created_in_new_issue'::event_type, 'initiative_created_in_existing_issue'::event_type, 'initiative_revoked'::event_type]))))) AND (ignored_member.member_id IS NULL)) AND (ignored_initiative.member_id IS NULL));


ALTER TABLE public.selected_event_seen_by_member OWNER TO "www-data";

--
-- Name: VIEW selected_event_seen_by_member; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW selected_event_seen_by_member IS 'Events as seen by a member, depending on its memberships, interests, support and members "notify_level"';


--
-- Name: setting; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE setting (
    member_id integer NOT NULL,
    key text NOT NULL,
    value text NOT NULL
);


ALTER TABLE public.setting OWNER TO "www-data";

--
-- Name: TABLE setting; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE setting IS 'Place to store a frontend specific setting for members as a string';


--
-- Name: COLUMN setting.key; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN setting.key IS 'Name of the setting, preceded by a frontend specific prefix';


--
-- Name: setting_map; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE setting_map (
    member_id integer NOT NULL,
    key text NOT NULL,
    subkey text NOT NULL,
    value text NOT NULL
);


ALTER TABLE public.setting_map OWNER TO "www-data";

--
-- Name: TABLE setting_map; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE setting_map IS 'Place to store a frontend specific setting for members as a map of key value pairs';


--
-- Name: COLUMN setting_map.key; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN setting_map.key IS 'Name of the setting, preceded by a frontend specific prefix';


--
-- Name: COLUMN setting_map.subkey; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN setting_map.subkey IS 'Key of a map entry';


--
-- Name: COLUMN setting_map.value; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN setting_map.value IS 'Value of a map entry';


--
-- Name: suggestion_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE suggestion_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.suggestion_id_seq OWNER TO "www-data";

--
-- Name: suggestion_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE suggestion_id_seq OWNED BY suggestion.id;


--
-- Name: suggestion_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('suggestion_id_seq', 1, true);


--
-- Name: suggestion_setting; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE suggestion_setting (
    member_id integer NOT NULL,
    key text NOT NULL,
    suggestion_id bigint NOT NULL,
    value text NOT NULL
);


ALTER TABLE public.suggestion_setting OWNER TO "www-data";

--
-- Name: TABLE suggestion_setting; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE suggestion_setting IS 'Place for frontend to store suggestion specific settings of members as strings';


--
-- Name: system_setting; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE system_setting (
    member_ttl interval
);


ALTER TABLE public.system_setting OWNER TO "www-data";

--
-- Name: TABLE system_setting; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE system_setting IS 'This table contains only one row with different settings in each column.';


--
-- Name: COLUMN system_setting.member_ttl; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN system_setting.member_ttl IS 'Time after members get their "active" flag set to FALSE, if they do not show any activity.';


--
-- Name: timeline_draft; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW timeline_draft AS
    SELECT draft.created AS occurrence, 'draft_created'::timeline_event AS event, draft.id AS draft_id FROM draft;


ALTER TABLE public.timeline_draft OWNER TO "www-data";

--
-- Name: VIEW timeline_draft; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW timeline_draft IS 'Helper view for "timeline" view (DEPRECATED)';


--
-- Name: timeline_initiative; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW timeline_initiative AS
    SELECT initiative.created AS occurrence, 'initiative_created'::timeline_event AS event, initiative.id AS initiative_id FROM initiative UNION ALL SELECT initiative.revoked AS occurrence, 'initiative_revoked'::timeline_event AS event, initiative.id AS initiative_id FROM initiative WHERE (initiative.revoked IS NOT NULL);


ALTER TABLE public.timeline_initiative OWNER TO "www-data";

--
-- Name: VIEW timeline_initiative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW timeline_initiative IS 'Helper view for "timeline" view (DEPRECATED)';


--
-- Name: timeline_issue; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW timeline_issue AS
    ((((SELECT issue.created AS occurrence, 'issue_created'::timeline_event AS event, issue.id AS issue_id FROM issue UNION ALL SELECT issue.closed AS occurrence, 'issue_canceled'::timeline_event AS event, issue.id AS issue_id FROM issue WHERE ((issue.closed IS NOT NULL) AND (issue.fully_frozen IS NULL))) UNION ALL SELECT issue.accepted AS occurrence, 'issue_accepted'::timeline_event AS event, issue.id AS issue_id FROM issue WHERE (issue.accepted IS NOT NULL)) UNION ALL SELECT issue.half_frozen AS occurrence, 'issue_half_frozen'::timeline_event AS event, issue.id AS issue_id FROM issue WHERE (issue.half_frozen IS NOT NULL)) UNION ALL SELECT issue.fully_frozen AS occurrence, 'issue_voting_started'::timeline_event AS event, issue.id AS issue_id FROM issue WHERE ((issue.fully_frozen IS NOT NULL) AND ((issue.closed IS NULL) OR (issue.closed <> issue.fully_frozen)))) UNION ALL SELECT issue.closed AS occurrence, CASE WHEN (issue.fully_frozen = issue.closed) THEN 'issue_finished_without_voting'::timeline_event ELSE 'issue_finished_after_voting'::timeline_event END AS event, issue.id AS issue_id FROM issue WHERE ((issue.closed IS NOT NULL) AND (issue.fully_frozen IS NOT NULL));


ALTER TABLE public.timeline_issue OWNER TO "www-data";

--
-- Name: VIEW timeline_issue; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW timeline_issue IS 'Helper view for "timeline" view (DEPRECATED)';


--
-- Name: timeline_suggestion; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW timeline_suggestion AS
    SELECT suggestion.created AS occurrence, 'suggestion_created'::timeline_event AS event, suggestion.id AS suggestion_id FROM suggestion;


ALTER TABLE public.timeline_suggestion OWNER TO "www-data";

--
-- Name: VIEW timeline_suggestion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW timeline_suggestion IS 'Helper view for "timeline" view (DEPRECATED)';


--
-- Name: timeline; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW timeline AS
    ((SELECT timeline_issue.occurrence, timeline_issue.event, timeline_issue.issue_id, NULL::unknown AS initiative_id, NULL::bigint AS draft_id, NULL::bigint AS suggestion_id FROM timeline_issue UNION ALL SELECT timeline_initiative.occurrence, timeline_initiative.event, NULL::unknown AS issue_id, timeline_initiative.initiative_id, NULL::unknown AS draft_id, NULL::unknown AS suggestion_id FROM timeline_initiative) UNION ALL SELECT timeline_draft.occurrence, timeline_draft.event, NULL::unknown AS issue_id, NULL::unknown AS initiative_id, timeline_draft.draft_id, NULL::unknown AS suggestion_id FROM timeline_draft) UNION ALL SELECT timeline_suggestion.occurrence, timeline_suggestion.event, NULL::unknown AS issue_id, NULL::unknown AS initiative_id, NULL::unknown AS draft_id, timeline_suggestion.suggestion_id FROM timeline_suggestion;


ALTER TABLE public.timeline OWNER TO "www-data";

--
-- Name: VIEW timeline; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW timeline IS 'Aggregation of different events in the system (DEPRECATED)';


--
-- Name: unit; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE unit (
    id integer NOT NULL,
    parent_id integer,
    active boolean DEFAULT true NOT NULL,
    name text NOT NULL,
    description text DEFAULT ''::text NOT NULL,
    member_count integer,
    text_search_data tsvector
);


ALTER TABLE public.unit OWNER TO "www-data";

--
-- Name: TABLE unit; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE unit IS 'Organizational units organized as trees; Delegations are not inherited through these trees.';


--
-- Name: COLUMN unit.parent_id; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN unit.parent_id IS 'Parent id of tree node; Multiple roots allowed';


--
-- Name: COLUMN unit.active; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN unit.active IS 'TRUE means new issues can be created in areas of this unit';


--
-- Name: COLUMN unit.member_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN unit.member_count IS 'Count of members as determined by column "voting_right" in table "privilege"';


--
-- Name: unit_delegation; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW unit_delegation AS
    SELECT unit.id AS unit_id, delegation.id, delegation.truster_id, delegation.trustee_id, delegation.scope FROM (((unit JOIN delegation ON ((delegation.unit_id = unit.id))) JOIN member ON ((delegation.truster_id = member.id))) JOIN privilege ON (((delegation.unit_id = privilege.unit_id) AND (delegation.truster_id = privilege.member_id)))) WHERE (member.active AND privilege.voting_right);


ALTER TABLE public.unit_delegation OWNER TO "www-data";

--
-- Name: VIEW unit_delegation; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW unit_delegation IS 'Unit delegations where trusters are active and have voting right';


--
-- Name: unit_id_seq; Type: SEQUENCE; Schema: public; Owner: www-data
--

CREATE SEQUENCE unit_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.unit_id_seq OWNER TO "www-data";

--
-- Name: unit_id_seq; Type: SEQUENCE OWNED BY; Schema: public; Owner: www-data
--

ALTER SEQUENCE unit_id_seq OWNED BY unit.id;


--
-- Name: unit_id_seq; Type: SEQUENCE SET; Schema: public; Owner: www-data
--

SELECT pg_catalog.setval('unit_id_seq', 1, true);


--
-- Name: unit_member_count; Type: VIEW; Schema: public; Owner: www-data
--

CREATE VIEW unit_member_count AS
    SELECT unit.id AS unit_id, count(member.id) AS member_count FROM ((unit LEFT JOIN privilege ON (((privilege.unit_id = unit.id) AND privilege.voting_right))) LEFT JOIN member ON (((member.id = privilege.member_id) AND member.active))) GROUP BY unit.id;


ALTER TABLE public.unit_member_count OWNER TO "www-data";

--
-- Name: VIEW unit_member_count; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON VIEW unit_member_count IS 'View used to update "member_count" column of "unit" table';


--
-- Name: unit_setting; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE unit_setting (
    member_id integer NOT NULL,
    key text NOT NULL,
    unit_id integer NOT NULL,
    value text NOT NULL
);


ALTER TABLE public.unit_setting OWNER TO "www-data";

--
-- Name: TABLE unit_setting; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE unit_setting IS 'Place for frontend to store unit specific settings of members as strings';


--
-- Name: voting_comment; Type: TABLE; Schema: public; Owner: www-data; Tablespace: 
--

CREATE TABLE voting_comment (
    issue_id integer NOT NULL,
    member_id integer NOT NULL,
    changed timestamp with time zone,
    formatting_engine text,
    content text NOT NULL,
    text_search_data tsvector
);


ALTER TABLE public.voting_comment OWNER TO "www-data";

--
-- Name: TABLE voting_comment; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TABLE voting_comment IS 'Storage for comments of voters to be published after voting has finished.';


--
-- Name: COLUMN voting_comment.changed; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON COLUMN voting_comment.changed IS 'Is to be set or updated by the frontend, if comment was inserted or updated AFTER the issue has been closed. Otherwise it shall be set to NULL.';


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY area ALTER COLUMN id SET DEFAULT nextval('area_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegation ALTER COLUMN id SET DEFAULT nextval('delegation_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY draft ALTER COLUMN id SET DEFAULT nextval('draft_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY event ALTER COLUMN id SET DEFAULT nextval('event_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY initiative ALTER COLUMN id SET DEFAULT nextval('initiative_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY issue ALTER COLUMN id SET DEFAULT nextval('issue_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY member ALTER COLUMN id SET DEFAULT nextval('member_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY member_application ALTER COLUMN id SET DEFAULT nextval('member_application_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY member_history ALTER COLUMN id SET DEFAULT nextval('member_history_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY policy ALTER COLUMN id SET DEFAULT nextval('policy_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY suggestion ALTER COLUMN id SET DEFAULT nextval('suggestion_id_seq'::regclass);


--
-- Name: id; Type: DEFAULT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY unit ALTER COLUMN id SET DEFAULT nextval('unit_id_seq'::regclass);


--
-- Data for Name: allowed_policy; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY allowed_policy (area_id, policy_id, default_policy) FROM stdin;
1	1	t
1	2	f
\.


--
-- Data for Name: area; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY area (id, unit_id, active, name, description, direct_member_count, member_weight, text_search_data) FROM stdin;
1	1	t	Default area		3	3	'area':2 'default':1
\.


--
-- Data for Name: area_setting; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY area_setting (member_id, key, area_id, value) FROM stdin;
\.


--
-- Data for Name: battle; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY battle (issue_id, winning_initiative_id, losing_initiative_id, count) FROM stdin;
\.


--
-- Data for Name: contact; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY contact (member_id, other_member_id, public) FROM stdin;
1	2	f
2	1	t
\.


--
-- Data for Name: contingent; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY contingent (time_frame, text_entry_limit, initiative_limit) FROM stdin;
01:00:00	20	6
1 day	80	12
\.


--
-- Data for Name: delegating_interest_snapshot; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY delegating_interest_snapshot (issue_id, event, member_id, weight, scope, delegate_member_ids) FROM stdin;
2	periodic	1	1	unit	{2}
2	half_freeze	1	1	unit	{2}
\.


--
-- Data for Name: delegating_population_snapshot; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY delegating_population_snapshot (issue_id, event, member_id, weight, scope, delegate_member_ids) FROM stdin;
\.


--
-- Data for Name: delegating_voter; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY delegating_voter (issue_id, member_id, weight, scope, delegate_member_ids) FROM stdin;
\.


--
-- Data for Name: delegation; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY delegation (id, truster_id, trustee_id, scope, unit_id, area_id, issue_id) FROM stdin;
1	1	2	unit	1	\N	\N
\.


--
-- Data for Name: direct_interest_snapshot; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY direct_interest_snapshot (issue_id, event, member_id, weight) FROM stdin;
1	end_of_admission	1	1
1	end_of_admission	2	1
2	end_of_admission	5	1
1	periodic	1	1
1	periodic	2	1
2	periodic	2	2
2	periodic	5	1
2	half_freeze	2	2
2	half_freeze	5	1
\.


--
-- Data for Name: direct_population_snapshot; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY direct_population_snapshot (issue_id, event, member_id, weight) FROM stdin;
1	end_of_admission	1	1
1	end_of_admission	2	1
2	end_of_admission	1	1
2	end_of_admission	2	1
2	end_of_admission	5	1
1	periodic	1	1
1	periodic	2	1
1	periodic	5	1
2	periodic	1	1
2	periodic	2	1
2	periodic	5	1
2	half_freeze	1	1
2	half_freeze	2	1
2	half_freeze	5	1
\.


--
-- Data for Name: direct_supporter_snapshot; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY direct_supporter_snapshot (issue_id, initiative_id, event, member_id, draft_id, informed, satisfied) FROM stdin;
1	1	end_of_admission	1	1	t	t
1	2	end_of_admission	2	2	t	t
2	3	end_of_admission	5	3	t	t
1	1	periodic	1	1	t	t
1	2	periodic	2	2	t	t
2	3	periodic	5	3	t	t
2	4	periodic	2	4	t	t
2	4	half_freeze	2	4	t	t
2	3	half_freeze	5	3	t	t
\.


--
-- Data for Name: direct_voter; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY direct_voter (issue_id, member_id, weight) FROM stdin;
\.


--
-- Data for Name: draft; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY draft (initiative_id, id, created, author_id, formatting_engine, content, text_search_data) FROM stdin;
1	1	2012-07-29 20:59:17.247226+01	1	rocketwiki	==== Get enough sleep before work tomorrow ====\r\n\r\nI've figured out how to add users now. Now it is time to go to sleep and **not** continue with anything new!	'add':13 'and':24 'anything':28 'before':4 'continue':26 'enough':2 'figured':9 'get':1 'go':21 'how':11 'i':7 'is':18 'it':17 'new':29 'not':25 'now':15,16 'out':10 'sleep':3,23 'time':19 'to':12,20,22 'tomorrow':6 'users':14 've':8 'with':27 'work':5
2	2	2012-07-29 21:11:25.603079+01	2	rocketwiki	==== Relax, have a gocnac, read something ====\r\n\r\nYou can sleep when you're dead. Shut down laptop, take a sandwich and a cognac.	'a':3,18,21 'and':20 'can':8 'cognac':22 'dead':13 'down':15 'gocnac':4 'have':2 'laptop':16 're':12 'read':5 'relax':1 'sandwich':19 'shut':14 'sleep':9 'something':6 'take':17 'when':10 'you':7,11
3	3	2012-08-04 12:49:10.844713+01	5	rocketwiki	==== I want a quickie ====\r\n\r\nThat means, I wan't to test the quickie vote policy.	'a':3 'i':1,7 'means':6 'policy':15 'quickie':4,13 't':9 'test':11 'that':5 'the':12 'to':10 'vote':14 'wan':8 'want':2
4	4	2012-08-04 12:52:11.188393+01	2	rocketwiki	==== A quickie for everyone ====\r\n\r\nI mean, who doesn't like a quickie	'a':1,11 'doesn':8 'everyone':4 'for':3 'i':5 'like':10 'mean':6 'quickie':2,12 't':9 'who':7
\.


--
-- Data for Name: event; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY event (id, occurrence, event, member_id, issue_id, state, initiative_id, draft_id, suggestion_id) FROM stdin;
1	2012-07-29 20:59:17.247226+01	initiative_created_in_new_issue	1	1	admission	1	1	\N
2	2012-07-29 21:11:25.603079+01	initiative_created_in_existing_issue	2	1	admission	2	2	\N
3	2012-07-29 21:13:27.183762+01	issue_state_changed	\N	1	discussion	\N	\N	\N
4	2012-08-04 12:49:10.844713+01	initiative_created_in_new_issue	5	2	admission	3	3	\N
5	2012-08-04 12:49:15.650508+01	issue_state_changed	\N	2	discussion	\N	\N	\N
7	2012-08-04 12:52:11.188393+01	initiative_created_in_existing_issue	2	2	discussion	4	4	\N
8	2012-08-04 13:04:19.879456+01	issue_state_changed	\N	2	verification	\N	\N	\N
\.


--
-- Data for Name: ignored_initiative; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY ignored_initiative (initiative_id, member_id) FROM stdin;
\.


--
-- Data for Name: ignored_member; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY ignored_member (member_id, other_member_id) FROM stdin;
\.


--
-- Data for Name: initiative; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY initiative (issue_id, id, name, discussion_url, created, revoked, revoked_by_member_id, suggested_initiative_id, admitted, supporter_count, informed_supporter_count, satisfied_supporter_count, satisfied_informed_supporter_count, positive_votes, negative_votes, direct_majority, indirect_majority, schulze_rank, better_than_status_quo, worse_than_status_quo, reverse_beat_path, multistage_majority, eligible, winner, rank, text_search_data) FROM stdin;
1	2	Gocnac	http://twitter.com	2012-07-29 21:11:25.603079+01	\N	\N	\N	\N	1	1	1	1	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'gocnac':1 'twitter.com':2
1	1	Sleep	http://facebook.com	2012-07-29 20:59:17.247226+01	\N	\N	\N	\N	1	1	1	1	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'facebook.com':2 'sleep':1
2	3	I want a quickie	http://twitter.com	2012-08-04 12:49:10.844713+01	\N	\N	\N	\N	1	1	1	1	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'a':3 'i':1 'quickie':4 'twitter.com':5 'want':2
2	4	I want a quickie for everyone	http://facebook.com	2012-08-04 12:52:11.188393+01	\N	\N	\N	\N	2	2	2	2	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'a':3 'everyone':6 'facebook.com':7 'for':5 'i':1 'quickie':4 'want':2
\.


--
-- Data for Name: initiative_setting; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY initiative_setting (member_id, key, initiative_id, value) FROM stdin;
\.


--
-- Data for Name: initiator; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY initiator (initiative_id, member_id, accepted) FROM stdin;
1	1	t
2	2	t
3	5	t
4	2	t
\.


--
-- Data for Name: interest; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY interest (issue_id, member_id) FROM stdin;
1	1
1	2
2	5
2	2
\.


--
-- Data for Name: issue; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY issue (id, area_id, policy_id, state, created, accepted, half_frozen, fully_frozen, closed, ranks_available, cleaned, admission_time, discussion_time, verification_time, voting_time, snapshot, latest_snapshot_event, population, voter_count, status_quo_schulze_rank) FROM stdin;
1	1	1	discussion	2012-07-29 20:59:17.247226+01	2012-07-29 21:13:27.183762+01	\N	\N	\N	f	\N	8 days	15 days	8 days	15 days	2012-08-04 13:09:07.198207+01	periodic	3	\N	\N
2	1	2	verification	2012-08-04 12:49:10.844713+01	2012-08-04 12:49:15.650508+01	2012-08-04 13:04:19.879456+01	\N	\N	f	\N	00:05:00	00:15:00	00:05:00	00:10:00	2012-08-04 13:09:07.249832+01	periodic	3	\N	\N
\.


--
-- Data for Name: issue_comment; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY issue_comment (issue_id, member_id, changed, formatting_engine, content, text_search_data) FROM stdin;
\.


--
-- Data for Name: issue_setting; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY issue_setting (member_id, key, issue_id, value) FROM stdin;
\.


--
-- Data for Name: member; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY member (id, created, invite_code, invite_code_expiry, admin_comment, activated, last_activity, last_login, login, password, locked, active, admin, lang, notify_email, notify_email_unconfirmed, notify_email_secret, notify_email_secret_expiry, notify_email_lock_expiry, notify_level, password_reset_secret, password_reset_secret_expiry, name, identification, authentication, organizational_unit, internal_posts, realname, birthday, address, email, xmpp_address, website, phone, mobile_phone, profession, external_memberships, external_posts, formatting_engine, statement, text_search_data) FROM stdin;
4	2012-07-27 15:24:25.185106+01	carolcode	\N	\N	\N	\N	\N	carol	\N	f	f	f	\N	\N	\N	\N	\N	\N	\N	\N	\N	Carol	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'carol':1
6	2012-07-27 15:28:35.129429+01	davecode	\N	\N	\N	\N	\N	dave	\N	f	f	f	\N	\N	\N	\N	\N	\N	\N	\N	\N	Dave	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'dave':1
5	2012-07-27 15:28:16.521801+01	bobcode	\N	\N	2012-08-03 08:08:57.530513+01	2012-08-04	2012-08-04 08:08:44.7617+01	bob	$1$g2MIJZcv$HJ4TfVvFkSVZpL7zVdExm1	f	t	f	\N	bob@lqfb	\N	\N	\N	\N	all	\N	\N	Bob	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'bob':1
1	2012-07-25 22:55:33.216186+01	invitecode	\N	\N	2012-07-25 23:24:41.913597+01	2012-08-04	2012-08-04 12:37:05.577152+01	admin	$1$gGk63TIk$AfES1mx7cIPLYZIz6R889.	f	t	t	en	hingo@lqfb	\N	\N	\N	\N	all	\N	\N	Administrator	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'administrator':1
2	2012-07-27 15:23:56.367107+01	alicecode	\N	\N	2012-07-29 18:37:09.355564+01	2012-08-04	2012-08-04 12:50:01.970199+01	alice	$1$FgX3y4V2$.Xf5fIri/Gsfo/dKrX6vu0	f	t	f	\N	alice@lqfb	\N	\N	\N	\N	\N	\N	\N	Alice	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	\N	'alice':1
\.


--
-- Data for Name: member_application; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY member_application (id, member_id, name, comment, access_level, key, last_usage) FROM stdin;
\.


--
-- Data for Name: member_count; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY member_count (calculated, total_count) FROM stdin;
2012-08-04 13:09:07.180722+01	3
\.


--
-- Data for Name: member_history; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY member_history (id, member_id, until, active, name) FROM stdin;
\.


--
-- Data for Name: member_image; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY member_image (member_id, image_type, scaled, content_type, data) FROM stdin;
\.


--
-- Data for Name: member_relation_setting; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY member_relation_setting (member_id, key, other_member_id, value) FROM stdin;
\.


--
-- Data for Name: membership; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY membership (area_id, member_id) FROM stdin;
1	2
1	1
1	5
\.


--
-- Data for Name: non_voter; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY non_voter (issue_id, member_id) FROM stdin;
\.


--
-- Data for Name: notification_sent; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY notification_sent (event_id) FROM stdin;
8
\.


--
-- Data for Name: opinion; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY opinion (initiative_id, suggestion_id, member_id, degree, fulfilled) FROM stdin;
\.


--
-- Data for Name: policy; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY policy (id, index, active, name, description, admission_time, discussion_time, verification_time, voting_time, issue_quorum_num, issue_quorum_den, initiative_quorum_num, initiative_quorum_den, direct_majority_num, direct_majority_den, direct_majority_strict, direct_majority_positive, direct_majority_non_negative, indirect_majority_num, indirect_majority_den, indirect_majority_strict, indirect_majority_positive, indirect_majority_non_negative, no_reverse_beat_path, no_multistage_majority) FROM stdin;
1	1	t	Month to voting		8 days	15 days	8 days	15 days	10	100	10	100	1	2	t	0	0	1	2	t	0	0	t	f
2	1	t	Quickie		00:05:00	00:15:00	00:05:00	00:10:00	10	100	10	100	1	2	t	0	0	1	2	t	0	0	t	f
\.


--
-- Data for Name: privilege; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY privilege (unit_id, member_id, admin_manager, unit_manager, area_manager, voting_right_manager, voting_right) FROM stdin;
1	1	t	t	t	t	t
1	2	f	f	f	f	t
1	5	f	f	f	f	t
\.


--
-- Data for Name: rendered_draft; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY rendered_draft (draft_id, format, content) FROM stdin;
1	html	<h1>Get enough sleep before work tomorrow </h1>\n<p>I've figured out how to add users now. Now it is time to go to sleep and <b>not</b> continue with anything new!</p>\n
2	html	<h1>Relax, have a gocnac, read something </h1>\n<p>You can sleep when you're dead. Shut down laptop, take a sandwich and a cognac.</p>\n
3	html	<h1>I want a quickie </h1>\n<p>That means, I wan't to test the quickie vote policy.</p>\n
4	html	<h1>A quickie for everyone </h1>\n<p>I mean, who doesn't like a quickie</p>\n
\.


--
-- Data for Name: rendered_issue_comment; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY rendered_issue_comment (issue_id, member_id, format, content) FROM stdin;
\.


--
-- Data for Name: rendered_member_statement; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY rendered_member_statement (member_id, format, content) FROM stdin;
\.


--
-- Data for Name: rendered_suggestion; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY rendered_suggestion (suggestion_id, format, content) FROM stdin;
\.


--
-- Data for Name: rendered_voting_comment; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY rendered_voting_comment (issue_id, member_id, format, content) FROM stdin;
\.


--
-- Data for Name: session; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY session (ident, additional_secret, expiry, member_id, lang) FROM stdin;
Pnd8wiGfwgVXJq7xD0T2Z26dEv6YTtL2	l9tt5ru2cuJfLnbzAseXuCJvfVRLCK1Q	2012-08-05 08:08:31.37985+01	5	\N
R9cKrzM9VpKl7ZGt8u2QUwf0ffqiyeJP	AufbMwwXJk1VG2ykQDhZwyDzCCPzHHd4	2012-08-05 12:36:56.28578+01	1	en
xX31kmfQD86YUMxILsx9ckS2tk6IrtFl	aXnCHpofonQneHemZRVTpkiRxIRJp99n	2012-08-05 12:49:35.34232+01	2	\N
\.


--
-- Data for Name: setting; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY setting (member_id, key, value) FROM stdin;
1	use_terms_checkbox_terms_of_use_v1	accepted at 2012-07-25 23:24:41
2	use_terms_checkbox_terms_of_use_v1	accepted at 2012-07-29 18:37:09
1	liquidfeedback_frontend_hidden_help_index.index	hidden
2	liquidfeedback_frontend_hidden_help_index.index	hidden
1	liquidfeedback_frontend_hidden_help_member.show	hidden
2	liquidfeedback_frontend_hidden_help_member.show	hidden
1	liquidfeedback_frontend_hidden_help_member.edit	hidden
1	liquidfeedback_frontend_hidden_help_contact.list	hidden
2	liquidfeedback_frontend_hidden_help_initiative.show	hidden
1	liquidfeedback_frontend_hidden_help_area.show	hidden
5	use_terms_checkbox_terms_of_use_v1	accepted at 2012-08-03 08:08:57
\.


--
-- Data for Name: setting_map; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY setting_map (member_id, key, subkey, value) FROM stdin;
\.


--
-- Data for Name: suggestion; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY suggestion (initiative_id, id, draft_id, created, author_id, name, formatting_engine, content, text_search_data, minus2_unfulfilled_count, minus2_fulfilled_count, minus1_unfulfilled_count, minus1_fulfilled_count, plus1_unfulfilled_count, plus1_fulfilled_count, plus2_unfulfilled_count, plus2_fulfilled_count) FROM stdin;
\.


--
-- Data for Name: suggestion_setting; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY suggestion_setting (member_id, key, suggestion_id, value) FROM stdin;
\.


--
-- Data for Name: supporter; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY supporter (issue_id, initiative_id, member_id, draft_id) FROM stdin;
1	1	1	1
1	2	2	2
2	3	5	3
2	4	2	4
\.


--
-- Data for Name: system_setting; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY system_setting (member_ttl) FROM stdin;
1 year
\.


--
-- Data for Name: unit; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY unit (id, parent_id, active, name, description, member_count, text_search_data) FROM stdin;
1	\N	t	Our organization		3	'organization':2 'our':1
\.


--
-- Data for Name: unit_setting; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY unit_setting (member_id, key, unit_id, value) FROM stdin;
\.


--
-- Data for Name: vote; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY vote (issue_id, initiative_id, member_id, grade) FROM stdin;
\.


--
-- Data for Name: voting_comment; Type: TABLE DATA; Schema: public; Owner: www-data
--

COPY voting_comment (issue_id, member_id, changed, formatting_engine, content, text_search_data) FROM stdin;
\.


--
-- Name: allowed_policy_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY allowed_policy
    ADD CONSTRAINT allowed_policy_pkey PRIMARY KEY (area_id, policy_id);


--
-- Name: area_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY area
    ADD CONSTRAINT area_pkey PRIMARY KEY (id);


--
-- Name: area_setting_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY area_setting
    ADD CONSTRAINT area_setting_pkey PRIMARY KEY (member_id, key, area_id);


--
-- Name: contact_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY contact
    ADD CONSTRAINT contact_pkey PRIMARY KEY (member_id, other_member_id);


--
-- Name: contingent_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY contingent
    ADD CONSTRAINT contingent_pkey PRIMARY KEY (time_frame);


--
-- Name: delegating_interest_snapshot_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY delegating_interest_snapshot
    ADD CONSTRAINT delegating_interest_snapshot_pkey PRIMARY KEY (issue_id, event, member_id);


--
-- Name: delegating_population_snapshot_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY delegating_population_snapshot
    ADD CONSTRAINT delegating_population_snapshot_pkey PRIMARY KEY (issue_id, event, member_id);


--
-- Name: delegating_voter_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY delegating_voter
    ADD CONSTRAINT delegating_voter_pkey PRIMARY KEY (issue_id, member_id);


--
-- Name: delegation_area_id_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_area_id_key UNIQUE (area_id, truster_id);


--
-- Name: delegation_issue_id_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_issue_id_key UNIQUE (issue_id, truster_id);


--
-- Name: delegation_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_pkey PRIMARY KEY (id);


--
-- Name: delegation_unit_id_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_unit_id_key UNIQUE (unit_id, truster_id);


--
-- Name: direct_interest_snapshot_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY direct_interest_snapshot
    ADD CONSTRAINT direct_interest_snapshot_pkey PRIMARY KEY (issue_id, event, member_id);


--
-- Name: direct_population_snapshot_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY direct_population_snapshot
    ADD CONSTRAINT direct_population_snapshot_pkey PRIMARY KEY (issue_id, event, member_id);


--
-- Name: direct_supporter_snapshot_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY direct_supporter_snapshot
    ADD CONSTRAINT direct_supporter_snapshot_pkey PRIMARY KEY (initiative_id, event, member_id);


--
-- Name: direct_voter_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY direct_voter
    ADD CONSTRAINT direct_voter_pkey PRIMARY KEY (issue_id, member_id);


--
-- Name: draft_initiative_id_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY draft
    ADD CONSTRAINT draft_initiative_id_key UNIQUE (initiative_id, id);


--
-- Name: draft_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY draft
    ADD CONSTRAINT draft_pkey PRIMARY KEY (id);


--
-- Name: event_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY event
    ADD CONSTRAINT event_pkey PRIMARY KEY (id);


--
-- Name: ignored_initiative_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY ignored_initiative
    ADD CONSTRAINT ignored_initiative_pkey PRIMARY KEY (initiative_id, member_id);


--
-- Name: ignored_member_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY ignored_member
    ADD CONSTRAINT ignored_member_pkey PRIMARY KEY (member_id, other_member_id);


--
-- Name: initiative_issue_id_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY initiative
    ADD CONSTRAINT initiative_issue_id_key UNIQUE (issue_id, id);


--
-- Name: initiative_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY initiative
    ADD CONSTRAINT initiative_pkey PRIMARY KEY (id);


--
-- Name: initiative_setting_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY initiative_setting
    ADD CONSTRAINT initiative_setting_pkey PRIMARY KEY (member_id, key, initiative_id);


--
-- Name: initiator_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY initiator
    ADD CONSTRAINT initiator_pkey PRIMARY KEY (initiative_id, member_id);


--
-- Name: interest_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY interest
    ADD CONSTRAINT interest_pkey PRIMARY KEY (issue_id, member_id);


--
-- Name: issue_comment_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY issue_comment
    ADD CONSTRAINT issue_comment_pkey PRIMARY KEY (issue_id, member_id);


--
-- Name: issue_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY issue
    ADD CONSTRAINT issue_pkey PRIMARY KEY (id);


--
-- Name: issue_setting_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY issue_setting
    ADD CONSTRAINT issue_setting_pkey PRIMARY KEY (member_id, key, issue_id);


--
-- Name: member_application_key_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member_application
    ADD CONSTRAINT member_application_key_key UNIQUE (key);


--
-- Name: member_application_member_id_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member_application
    ADD CONSTRAINT member_application_member_id_key UNIQUE (member_id, name);


--
-- Name: member_application_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member_application
    ADD CONSTRAINT member_application_pkey PRIMARY KEY (id);


--
-- Name: member_history_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member_history
    ADD CONSTRAINT member_history_pkey PRIMARY KEY (id);


--
-- Name: member_identification_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member
    ADD CONSTRAINT member_identification_key UNIQUE (identification);


--
-- Name: member_image_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member_image
    ADD CONSTRAINT member_image_pkey PRIMARY KEY (member_id, image_type, scaled);


--
-- Name: member_invite_code_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member
    ADD CONSTRAINT member_invite_code_key UNIQUE (invite_code);


--
-- Name: member_login_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member
    ADD CONSTRAINT member_login_key UNIQUE (login);


--
-- Name: member_name_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member
    ADD CONSTRAINT member_name_key UNIQUE (name);


--
-- Name: member_notify_email_secret_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member
    ADD CONSTRAINT member_notify_email_secret_key UNIQUE (notify_email_secret);


--
-- Name: member_password_reset_secret_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member
    ADD CONSTRAINT member_password_reset_secret_key UNIQUE (password_reset_secret);


--
-- Name: member_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member
    ADD CONSTRAINT member_pkey PRIMARY KEY (id);


--
-- Name: member_relation_setting_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY member_relation_setting
    ADD CONSTRAINT member_relation_setting_pkey PRIMARY KEY (member_id, key, other_member_id);


--
-- Name: membership_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY membership
    ADD CONSTRAINT membership_pkey PRIMARY KEY (area_id, member_id);


--
-- Name: non_voter_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY non_voter
    ADD CONSTRAINT non_voter_pkey PRIMARY KEY (issue_id, member_id);


--
-- Name: opinion_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY opinion
    ADD CONSTRAINT opinion_pkey PRIMARY KEY (suggestion_id, member_id);


--
-- Name: policy_name_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY policy
    ADD CONSTRAINT policy_name_key UNIQUE (name);


--
-- Name: policy_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY policy
    ADD CONSTRAINT policy_pkey PRIMARY KEY (id);


--
-- Name: privilege_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY privilege
    ADD CONSTRAINT privilege_pkey PRIMARY KEY (unit_id, member_id);


--
-- Name: rendered_draft_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY rendered_draft
    ADD CONSTRAINT rendered_draft_pkey PRIMARY KEY (draft_id, format);


--
-- Name: rendered_issue_comment_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY rendered_issue_comment
    ADD CONSTRAINT rendered_issue_comment_pkey PRIMARY KEY (issue_id, member_id, format);


--
-- Name: rendered_member_statement_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY rendered_member_statement
    ADD CONSTRAINT rendered_member_statement_pkey PRIMARY KEY (member_id, format);


--
-- Name: rendered_suggestion_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY rendered_suggestion
    ADD CONSTRAINT rendered_suggestion_pkey PRIMARY KEY (suggestion_id, format);


--
-- Name: rendered_voting_comment_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY rendered_voting_comment
    ADD CONSTRAINT rendered_voting_comment_pkey PRIMARY KEY (issue_id, member_id, format);


--
-- Name: session_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY session
    ADD CONSTRAINT session_pkey PRIMARY KEY (ident);


--
-- Name: setting_map_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY setting_map
    ADD CONSTRAINT setting_map_pkey PRIMARY KEY (member_id, key, subkey);


--
-- Name: setting_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY setting
    ADD CONSTRAINT setting_pkey PRIMARY KEY (member_id, key);


--
-- Name: suggestion_initiative_id_key; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY suggestion
    ADD CONSTRAINT suggestion_initiative_id_key UNIQUE (initiative_id, id);


--
-- Name: suggestion_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY suggestion
    ADD CONSTRAINT suggestion_pkey PRIMARY KEY (id);


--
-- Name: suggestion_setting_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY suggestion_setting
    ADD CONSTRAINT suggestion_setting_pkey PRIMARY KEY (member_id, key, suggestion_id);


--
-- Name: supporter_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY supporter
    ADD CONSTRAINT supporter_pkey PRIMARY KEY (initiative_id, member_id);


--
-- Name: unique_rank_per_issue; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY initiative
    ADD CONSTRAINT unique_rank_per_issue UNIQUE (issue_id, rank);


--
-- Name: unit_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY unit
    ADD CONSTRAINT unit_pkey PRIMARY KEY (id);


--
-- Name: unit_setting_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY unit_setting
    ADD CONSTRAINT unit_setting_pkey PRIMARY KEY (member_id, key, unit_id);


--
-- Name: vote_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY vote
    ADD CONSTRAINT vote_pkey PRIMARY KEY (initiative_id, member_id);


--
-- Name: voting_comment_pkey; Type: CONSTRAINT; Schema: public; Owner: www-data; Tablespace: 
--

ALTER TABLE ONLY voting_comment
    ADD CONSTRAINT voting_comment_pkey PRIMARY KEY (issue_id, member_id);


--
-- Name: allowed_policy_one_default_per_area_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE UNIQUE INDEX allowed_policy_one_default_per_area_idx ON allowed_policy USING btree (area_id) WHERE default_policy;


--
-- Name: area_active_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX area_active_idx ON area USING btree (active);


--
-- Name: area_text_search_data_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX area_text_search_data_idx ON area USING gin (text_search_data);


--
-- Name: area_unit_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX area_unit_id_idx ON area USING btree (unit_id);


--
-- Name: battle_null_losing_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE UNIQUE INDEX battle_null_losing_idx ON battle USING btree (issue_id, losing_initiative_id) WHERE (winning_initiative_id IS NULL);


--
-- Name: battle_winning_losing_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE UNIQUE INDEX battle_winning_losing_idx ON battle USING btree (issue_id, winning_initiative_id, losing_initiative_id);


--
-- Name: battle_winning_null_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE UNIQUE INDEX battle_winning_null_idx ON battle USING btree (issue_id, winning_initiative_id) WHERE (losing_initiative_id IS NULL);


--
-- Name: contact_other_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX contact_other_member_id_idx ON contact USING btree (other_member_id);


--
-- Name: delegating_interest_snapshot_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX delegating_interest_snapshot_member_id_idx ON delegating_interest_snapshot USING btree (member_id);


--
-- Name: delegating_population_snapshot_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX delegating_population_snapshot_member_id_idx ON delegating_population_snapshot USING btree (member_id);


--
-- Name: delegating_voter_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX delegating_voter_member_id_idx ON delegating_voter USING btree (member_id);


--
-- Name: delegation_trustee_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX delegation_trustee_id_idx ON delegation USING btree (trustee_id);


--
-- Name: delegation_truster_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX delegation_truster_id_idx ON delegation USING btree (truster_id);


--
-- Name: direct_interest_snapshot_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX direct_interest_snapshot_member_id_idx ON direct_interest_snapshot USING btree (member_id);


--
-- Name: direct_population_snapshot_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX direct_population_snapshot_member_id_idx ON direct_population_snapshot USING btree (member_id);


--
-- Name: direct_supporter_snapshot_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX direct_supporter_snapshot_member_id_idx ON direct_supporter_snapshot USING btree (member_id);


--
-- Name: direct_voter_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX direct_voter_member_id_idx ON direct_voter USING btree (member_id);


--
-- Name: draft_author_id_created_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX draft_author_id_created_idx ON draft USING btree (author_id, created);


--
-- Name: draft_created_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX draft_created_idx ON draft USING btree (created);


--
-- Name: draft_text_search_data_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX draft_text_search_data_idx ON draft USING gin (text_search_data);


--
-- Name: event_occurrence_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX event_occurrence_idx ON event USING btree (occurrence);


--
-- Name: ignored_initiative_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX ignored_initiative_member_id_idx ON ignored_initiative USING btree (member_id);


--
-- Name: ignored_member_other_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX ignored_member_other_member_id_idx ON ignored_member USING btree (other_member_id);


--
-- Name: initiative_created_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX initiative_created_idx ON initiative USING btree (created);


--
-- Name: initiative_revoked_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX initiative_revoked_idx ON initiative USING btree (revoked);


--
-- Name: initiative_text_search_data_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX initiative_text_search_data_idx ON initiative USING gin (text_search_data);


--
-- Name: initiator_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX initiator_member_id_idx ON initiator USING btree (member_id);


--
-- Name: interest_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX interest_member_id_idx ON interest USING btree (member_id);


--
-- Name: issue_accepted_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_accepted_idx ON issue USING btree (accepted);


--
-- Name: issue_area_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_area_id_idx ON issue USING btree (area_id);


--
-- Name: issue_closed_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_closed_idx ON issue USING btree (closed);


--
-- Name: issue_closed_idx_canceled; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_closed_idx_canceled ON issue USING btree (closed) WHERE (fully_frozen IS NULL);


--
-- Name: issue_comment_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_comment_member_id_idx ON issue_comment USING btree (member_id);


--
-- Name: issue_comment_text_search_data_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_comment_text_search_data_idx ON issue_comment USING gin (text_search_data);


--
-- Name: issue_created_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_created_idx ON issue USING btree (created);


--
-- Name: issue_created_idx_open; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_created_idx_open ON issue USING btree (created) WHERE (closed IS NULL);


--
-- Name: issue_fully_frozen_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_fully_frozen_idx ON issue USING btree (fully_frozen);


--
-- Name: issue_half_frozen_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_half_frozen_idx ON issue USING btree (half_frozen);


--
-- Name: issue_policy_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX issue_policy_id_idx ON issue USING btree (policy_id);


--
-- Name: member_active_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX member_active_idx ON member USING btree (active);


--
-- Name: member_history_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX member_history_member_id_idx ON member_history USING btree (member_id);


--
-- Name: member_text_search_data_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX member_text_search_data_idx ON member USING gin (text_search_data);


--
-- Name: membership_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX membership_member_id_idx ON membership USING btree (member_id);


--
-- Name: non_voter_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX non_voter_member_id_idx ON non_voter USING btree (member_id);


--
-- Name: notification_sent_singleton_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE UNIQUE INDEX notification_sent_singleton_idx ON notification_sent USING btree ((1));


--
-- Name: INDEX notification_sent_singleton_idx; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON INDEX notification_sent_singleton_idx IS 'This index ensures that "notification_sent" only contains one row maximum.';


--
-- Name: opinion_member_id_initiative_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX opinion_member_id_initiative_id_idx ON opinion USING btree (member_id, initiative_id);


--
-- Name: policy_active_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX policy_active_idx ON policy USING btree (active);


--
-- Name: session_expiry_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX session_expiry_idx ON session USING btree (expiry);


--
-- Name: setting_key_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX setting_key_idx ON setting USING btree (key);


--
-- Name: setting_map_key_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX setting_map_key_idx ON setting_map USING btree (key);


--
-- Name: suggestion_author_id_created_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX suggestion_author_id_created_idx ON suggestion USING btree (author_id, created);


--
-- Name: suggestion_created_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX suggestion_created_idx ON suggestion USING btree (created);


--
-- Name: suggestion_text_search_data_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX suggestion_text_search_data_idx ON suggestion USING gin (text_search_data);


--
-- Name: supporter_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX supporter_member_id_idx ON supporter USING btree (member_id);


--
-- Name: system_setting_singleton_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE UNIQUE INDEX system_setting_singleton_idx ON system_setting USING btree ((1));


--
-- Name: INDEX system_setting_singleton_idx; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON INDEX system_setting_singleton_idx IS 'This index ensures that "system_setting" only contains one row maximum.';


--
-- Name: unit_active_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX unit_active_idx ON unit USING btree (active);


--
-- Name: unit_parent_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX unit_parent_id_idx ON unit USING btree (parent_id);


--
-- Name: unit_root_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX unit_root_idx ON unit USING btree (id) WHERE (parent_id IS NULL);


--
-- Name: unit_text_search_data_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX unit_text_search_data_idx ON unit USING gin (text_search_data);


--
-- Name: vote_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX vote_member_id_idx ON vote USING btree (member_id);


--
-- Name: voting_comment_member_id_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX voting_comment_member_id_idx ON voting_comment USING btree (member_id);


--
-- Name: voting_comment_text_search_data_idx; Type: INDEX; Schema: public; Owner: www-data; Tablespace: 
--

CREATE INDEX voting_comment_text_search_data_idx ON voting_comment USING gin (text_search_data);


--
-- Name: delete; Type: RULE; Schema: public; Owner: www-data
--

CREATE RULE delete AS ON DELETE TO expired_session DO INSTEAD DELETE FROM session WHERE (session.ident = old.ident);


--
-- Name: RULE delete ON expired_session; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON RULE delete ON expired_session IS 'Rule allowing DELETE on rows in "expired_session" view, i.e. DELETE FROM "expired_session"';


--
-- Name: autocreate_interest; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER autocreate_interest
    BEFORE INSERT ON supporter
    FOR EACH ROW
    EXECUTE PROCEDURE autocreate_interest_trigger();


--
-- Name: TRIGGER autocreate_interest ON supporter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER autocreate_interest ON supporter IS 'Supporting an initiative implies interest in the issue, thus automatically creates an entry in the "interest" table';


--
-- Name: autocreate_supporter; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER autocreate_supporter
    BEFORE INSERT ON opinion
    FOR EACH ROW
    EXECUTE PROCEDURE autocreate_supporter_trigger();


--
-- Name: TRIGGER autocreate_supporter ON opinion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER autocreate_supporter ON opinion IS 'Opinions can only be added for supported initiatives. This trigger automatrically creates an entry in the "supporter" table, if not existent yet.';


--
-- Name: autofill_initiative_id; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER autofill_initiative_id
    BEFORE INSERT ON opinion
    FOR EACH ROW
    EXECUTE PROCEDURE autofill_initiative_id_trigger();


--
-- Name: TRIGGER autofill_initiative_id ON opinion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER autofill_initiative_id ON opinion IS 'Set "initiative_id" field automatically, if NULL';


--
-- Name: autofill_issue_id; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER autofill_issue_id
    BEFORE INSERT ON supporter
    FOR EACH ROW
    EXECUTE PROCEDURE autofill_issue_id_trigger();


--
-- Name: TRIGGER autofill_issue_id ON supporter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER autofill_issue_id ON supporter IS 'Set "issue_id" field automatically, if NULL';


--
-- Name: autofill_issue_id; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER autofill_issue_id
    BEFORE INSERT ON vote
    FOR EACH ROW
    EXECUTE PROCEDURE autofill_issue_id_trigger();


--
-- Name: TRIGGER autofill_issue_id ON vote; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER autofill_issue_id ON vote IS 'Set "issue_id" field automatically, if NULL';


--
-- Name: copy_timings; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER copy_timings
    BEFORE INSERT OR UPDATE ON issue
    FOR EACH ROW
    EXECUTE PROCEDURE copy_timings_trigger();


--
-- Name: TRIGGER copy_timings ON issue; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER copy_timings ON issue IS 'If timing fields are NULL, copy values from policy.';


--
-- Name: default_for_draft_id; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER default_for_draft_id
    BEFORE INSERT OR UPDATE ON suggestion
    FOR EACH ROW
    EXECUTE PROCEDURE default_for_draft_id_trigger();


--
-- Name: TRIGGER default_for_draft_id ON suggestion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER default_for_draft_id ON suggestion IS 'If "draft_id" is NULL, then use the current draft of the initiative as default';


--
-- Name: default_for_draft_id; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER default_for_draft_id
    BEFORE INSERT OR UPDATE ON supporter
    FOR EACH ROW
    EXECUTE PROCEDURE default_for_draft_id_trigger();


--
-- Name: TRIGGER default_for_draft_id ON supporter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER default_for_draft_id ON supporter IS 'If "draft_id" is NULL, then use the current draft of the initiative as default';


--
-- Name: forbid_changes_on_closed_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER forbid_changes_on_closed_issue
    AFTER INSERT OR DELETE OR UPDATE ON direct_voter
    FOR EACH ROW
    EXECUTE PROCEDURE forbid_changes_on_closed_issue_trigger();


--
-- Name: TRIGGER forbid_changes_on_closed_issue ON direct_voter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER forbid_changes_on_closed_issue ON direct_voter IS 'Ensures that frontends can''t tamper with votings of closed issues, in case of programming errors';


--
-- Name: forbid_changes_on_closed_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER forbid_changes_on_closed_issue
    AFTER INSERT OR DELETE OR UPDATE ON delegating_voter
    FOR EACH ROW
    EXECUTE PROCEDURE forbid_changes_on_closed_issue_trigger();


--
-- Name: TRIGGER forbid_changes_on_closed_issue ON delegating_voter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER forbid_changes_on_closed_issue ON delegating_voter IS 'Ensures that frontends can''t tamper with votings of closed issues, in case of programming errors';


--
-- Name: forbid_changes_on_closed_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER forbid_changes_on_closed_issue
    AFTER INSERT OR DELETE OR UPDATE ON vote
    FOR EACH ROW
    EXECUTE PROCEDURE forbid_changes_on_closed_issue_trigger();


--
-- Name: TRIGGER forbid_changes_on_closed_issue ON vote; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER forbid_changes_on_closed_issue ON vote IS 'Ensures that frontends can''t tamper with votings of closed issues, in case of programming errors';


--
-- Name: initiative_requires_first_draft; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE CONSTRAINT TRIGGER initiative_requires_first_draft
    AFTER INSERT OR UPDATE ON initiative
DEFERRABLE INITIALLY DEFERRED
    FOR EACH ROW
    EXECUTE PROCEDURE initiative_requires_first_draft_trigger();


--
-- Name: TRIGGER initiative_requires_first_draft ON initiative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER initiative_requires_first_draft ON initiative IS 'Ensure that new initiatives have at least one draft';


--
-- Name: issue_requires_first_initiative; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE CONSTRAINT TRIGGER issue_requires_first_initiative
    AFTER INSERT OR UPDATE ON issue
DEFERRABLE INITIALLY DEFERRED
    FOR EACH ROW
    EXECUTE PROCEDURE issue_requires_first_initiative_trigger();


--
-- Name: TRIGGER issue_requires_first_initiative ON issue; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER issue_requires_first_initiative ON issue IS 'Ensure that new issues have at least one initiative';


--
-- Name: last_draft_deletes_initiative; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE CONSTRAINT TRIGGER last_draft_deletes_initiative
    AFTER DELETE OR UPDATE ON draft
DEFERRABLE INITIALLY DEFERRED
    FOR EACH ROW
    EXECUTE PROCEDURE last_draft_deletes_initiative_trigger();


--
-- Name: TRIGGER last_draft_deletes_initiative ON draft; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER last_draft_deletes_initiative ON draft IS 'Removing the last draft of an initiative deletes the initiative';


--
-- Name: last_initiative_deletes_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE CONSTRAINT TRIGGER last_initiative_deletes_issue
    AFTER DELETE OR UPDATE ON initiative
DEFERRABLE INITIALLY DEFERRED
    FOR EACH ROW
    EXECUTE PROCEDURE last_initiative_deletes_issue_trigger();


--
-- Name: TRIGGER last_initiative_deletes_issue ON initiative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER last_initiative_deletes_issue ON initiative IS 'Removing the last initiative of an issue deletes the issue';


--
-- Name: last_opinion_deletes_suggestion; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE CONSTRAINT TRIGGER last_opinion_deletes_suggestion
    AFTER DELETE OR UPDATE ON opinion
DEFERRABLE INITIALLY DEFERRED
    FOR EACH ROW
    EXECUTE PROCEDURE last_opinion_deletes_suggestion_trigger();


--
-- Name: TRIGGER last_opinion_deletes_suggestion ON opinion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER last_opinion_deletes_suggestion ON opinion IS 'Removing the last opinion of a suggestion deletes the suggestion';


--
-- Name: share_row_lock_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER share_row_lock_issue
    BEFORE INSERT OR DELETE OR UPDATE ON initiative
    FOR EACH ROW
    EXECUTE PROCEDURE share_row_lock_issue_trigger();


--
-- Name: TRIGGER share_row_lock_issue ON initiative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER share_row_lock_issue ON initiative IS 'See "lock_issue" function';


--
-- Name: share_row_lock_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER share_row_lock_issue
    BEFORE INSERT OR DELETE OR UPDATE ON interest
    FOR EACH ROW
    EXECUTE PROCEDURE share_row_lock_issue_trigger();


--
-- Name: TRIGGER share_row_lock_issue ON interest; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER share_row_lock_issue ON interest IS 'See "lock_issue" function';


--
-- Name: share_row_lock_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER share_row_lock_issue
    BEFORE INSERT OR DELETE OR UPDATE ON supporter
    FOR EACH ROW
    EXECUTE PROCEDURE share_row_lock_issue_trigger();


--
-- Name: TRIGGER share_row_lock_issue ON supporter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER share_row_lock_issue ON supporter IS 'See "lock_issue" function';


--
-- Name: share_row_lock_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER share_row_lock_issue
    BEFORE INSERT OR DELETE OR UPDATE ON direct_voter
    FOR EACH ROW
    EXECUTE PROCEDURE share_row_lock_issue_trigger();


--
-- Name: TRIGGER share_row_lock_issue ON direct_voter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER share_row_lock_issue ON direct_voter IS 'See "lock_issue" function';


--
-- Name: share_row_lock_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER share_row_lock_issue
    BEFORE INSERT OR DELETE OR UPDATE ON delegating_voter
    FOR EACH ROW
    EXECUTE PROCEDURE share_row_lock_issue_trigger();


--
-- Name: TRIGGER share_row_lock_issue ON delegating_voter; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER share_row_lock_issue ON delegating_voter IS 'See "lock_issue" function';


--
-- Name: share_row_lock_issue; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER share_row_lock_issue
    BEFORE INSERT OR DELETE OR UPDATE ON vote
    FOR EACH ROW
    EXECUTE PROCEDURE share_row_lock_issue_trigger();


--
-- Name: TRIGGER share_row_lock_issue ON vote; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER share_row_lock_issue ON vote IS 'See "lock_issue" function';


--
-- Name: share_row_lock_issue_via_initiative; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER share_row_lock_issue_via_initiative
    BEFORE INSERT OR DELETE OR UPDATE ON opinion
    FOR EACH ROW
    EXECUTE PROCEDURE share_row_lock_issue_via_initiative_trigger();


--
-- Name: TRIGGER share_row_lock_issue_via_initiative ON opinion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER share_row_lock_issue_via_initiative ON opinion IS 'See "lock_issue" function';


--
-- Name: suggestion_requires_first_opinion; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE CONSTRAINT TRIGGER suggestion_requires_first_opinion
    AFTER INSERT OR UPDATE ON suggestion
DEFERRABLE INITIALLY DEFERRED
    FOR EACH ROW
    EXECUTE PROCEDURE suggestion_requires_first_opinion_trigger();


--
-- Name: TRIGGER suggestion_requires_first_opinion ON suggestion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER suggestion_requires_first_opinion ON suggestion IS 'Ensure that new suggestions have at least one opinion';


--
-- Name: update_text_search_data; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER update_text_search_data
    BEFORE INSERT OR UPDATE ON member
    FOR EACH ROW
    EXECUTE PROCEDURE tsvector_update_trigger('text_search_data', 'pg_catalog.simple', 'name', 'identification', 'organizational_unit', 'internal_posts', 'realname', 'external_memberships', 'external_posts', 'statement');


--
-- Name: update_text_search_data; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER update_text_search_data
    BEFORE INSERT OR UPDATE ON unit
    FOR EACH ROW
    EXECUTE PROCEDURE tsvector_update_trigger('text_search_data', 'pg_catalog.simple', 'name', 'description');


--
-- Name: update_text_search_data; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER update_text_search_data
    BEFORE INSERT OR UPDATE ON area
    FOR EACH ROW
    EXECUTE PROCEDURE tsvector_update_trigger('text_search_data', 'pg_catalog.simple', 'name', 'description');


--
-- Name: update_text_search_data; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER update_text_search_data
    BEFORE INSERT OR UPDATE ON initiative
    FOR EACH ROW
    EXECUTE PROCEDURE tsvector_update_trigger('text_search_data', 'pg_catalog.simple', 'name', 'discussion_url');


--
-- Name: update_text_search_data; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER update_text_search_data
    BEFORE INSERT OR UPDATE ON draft
    FOR EACH ROW
    EXECUTE PROCEDURE tsvector_update_trigger('text_search_data', 'pg_catalog.simple', 'content');


--
-- Name: update_text_search_data; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER update_text_search_data
    BEFORE INSERT OR UPDATE ON suggestion
    FOR EACH ROW
    EXECUTE PROCEDURE tsvector_update_trigger('text_search_data', 'pg_catalog.simple', 'name', 'content');


--
-- Name: update_text_search_data; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER update_text_search_data
    BEFORE INSERT OR UPDATE ON issue_comment
    FOR EACH ROW
    EXECUTE PROCEDURE tsvector_update_trigger('text_search_data', 'pg_catalog.simple', 'content');


--
-- Name: update_text_search_data; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER update_text_search_data
    BEFORE INSERT OR UPDATE ON voting_comment
    FOR EACH ROW
    EXECUTE PROCEDURE tsvector_update_trigger('text_search_data', 'pg_catalog.simple', 'content');


--
-- Name: write_event_initiative_or_draft_created; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER write_event_initiative_or_draft_created
    AFTER INSERT ON draft
    FOR EACH ROW
    EXECUTE PROCEDURE write_event_initiative_or_draft_created_trigger();


--
-- Name: TRIGGER write_event_initiative_or_draft_created ON draft; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER write_event_initiative_or_draft_created ON draft IS 'Create entry in "event" table on draft creation';


--
-- Name: write_event_initiative_revoked; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER write_event_initiative_revoked
    AFTER UPDATE ON initiative
    FOR EACH ROW
    EXECUTE PROCEDURE write_event_initiative_revoked_trigger();


--
-- Name: TRIGGER write_event_initiative_revoked ON initiative; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER write_event_initiative_revoked ON initiative IS 'Create entry in "event" table, when an initiative is revoked';


--
-- Name: write_event_issue_state_changed; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER write_event_issue_state_changed
    AFTER UPDATE ON issue
    FOR EACH ROW
    EXECUTE PROCEDURE write_event_issue_state_changed_trigger();


--
-- Name: TRIGGER write_event_issue_state_changed ON issue; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER write_event_issue_state_changed ON issue IS 'Create entry in "event" table on "state" change';


--
-- Name: write_event_suggestion_created; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER write_event_suggestion_created
    AFTER INSERT ON suggestion
    FOR EACH ROW
    EXECUTE PROCEDURE write_event_suggestion_created_trigger();


--
-- Name: TRIGGER write_event_suggestion_created ON suggestion; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER write_event_suggestion_created ON suggestion IS 'Create entry in "event" table on suggestion creation';


--
-- Name: write_member_history; Type: TRIGGER; Schema: public; Owner: www-data
--

CREATE TRIGGER write_member_history
    AFTER UPDATE ON member
    FOR EACH ROW
    EXECUTE PROCEDURE write_member_history_trigger();


--
-- Name: TRIGGER write_member_history ON member; Type: COMMENT; Schema: public; Owner: www-data
--

COMMENT ON TRIGGER write_member_history ON member IS 'When changing certain fields of a member, create a history entry in "member_history" table';


--
-- Name: allowed_policy_area_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY allowed_policy
    ADD CONSTRAINT allowed_policy_area_id_fkey FOREIGN KEY (area_id) REFERENCES area(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: allowed_policy_policy_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY allowed_policy
    ADD CONSTRAINT allowed_policy_policy_id_fkey FOREIGN KEY (policy_id) REFERENCES policy(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: area_setting_area_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY area_setting
    ADD CONSTRAINT area_setting_area_id_fkey FOREIGN KEY (area_id) REFERENCES area(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: area_setting_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY area_setting
    ADD CONSTRAINT area_setting_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: area_unit_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY area
    ADD CONSTRAINT area_unit_id_fkey FOREIGN KEY (unit_id) REFERENCES unit(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: battle_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY battle
    ADD CONSTRAINT battle_issue_id_fkey FOREIGN KEY (issue_id, winning_initiative_id) REFERENCES initiative(issue_id, id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: battle_issue_id_fkey1; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY battle
    ADD CONSTRAINT battle_issue_id_fkey1 FOREIGN KEY (issue_id, losing_initiative_id) REFERENCES initiative(issue_id, id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: contact_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY contact
    ADD CONSTRAINT contact_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: contact_other_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY contact
    ADD CONSTRAINT contact_other_member_id_fkey FOREIGN KEY (other_member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: delegating_interest_snapshot_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegating_interest_snapshot
    ADD CONSTRAINT delegating_interest_snapshot_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: delegating_interest_snapshot_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegating_interest_snapshot
    ADD CONSTRAINT delegating_interest_snapshot_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE RESTRICT ON DELETE RESTRICT;


--
-- Name: delegating_population_snapshot_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegating_population_snapshot
    ADD CONSTRAINT delegating_population_snapshot_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: delegating_population_snapshot_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegating_population_snapshot
    ADD CONSTRAINT delegating_population_snapshot_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE RESTRICT ON DELETE RESTRICT;


--
-- Name: delegating_voter_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegating_voter
    ADD CONSTRAINT delegating_voter_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: delegating_voter_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegating_voter
    ADD CONSTRAINT delegating_voter_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE RESTRICT ON DELETE RESTRICT;


--
-- Name: delegation_area_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_area_id_fkey FOREIGN KEY (area_id) REFERENCES area(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: delegation_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: delegation_trustee_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_trustee_id_fkey FOREIGN KEY (trustee_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: delegation_truster_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_truster_id_fkey FOREIGN KEY (truster_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: delegation_unit_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY delegation
    ADD CONSTRAINT delegation_unit_id_fkey FOREIGN KEY (unit_id) REFERENCES unit(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: direct_interest_snapshot_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_interest_snapshot
    ADD CONSTRAINT direct_interest_snapshot_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: direct_interest_snapshot_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_interest_snapshot
    ADD CONSTRAINT direct_interest_snapshot_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE RESTRICT ON DELETE RESTRICT;


--
-- Name: direct_population_snapshot_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_population_snapshot
    ADD CONSTRAINT direct_population_snapshot_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: direct_population_snapshot_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_population_snapshot
    ADD CONSTRAINT direct_population_snapshot_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE RESTRICT ON DELETE RESTRICT;


--
-- Name: direct_supporter_snapshot_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_supporter_snapshot
    ADD CONSTRAINT direct_supporter_snapshot_initiative_id_fkey FOREIGN KEY (initiative_id, draft_id) REFERENCES draft(initiative_id, id) ON UPDATE CASCADE;


--
-- Name: direct_supporter_snapshot_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_supporter_snapshot
    ADD CONSTRAINT direct_supporter_snapshot_issue_id_fkey FOREIGN KEY (issue_id, initiative_id) REFERENCES initiative(issue_id, id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: direct_supporter_snapshot_issue_id_fkey1; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_supporter_snapshot
    ADD CONSTRAINT direct_supporter_snapshot_issue_id_fkey1 FOREIGN KEY (issue_id, event, member_id) REFERENCES direct_interest_snapshot(issue_id, event, member_id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: direct_supporter_snapshot_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_supporter_snapshot
    ADD CONSTRAINT direct_supporter_snapshot_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE RESTRICT ON DELETE RESTRICT;


--
-- Name: direct_voter_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_voter
    ADD CONSTRAINT direct_voter_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: direct_voter_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY direct_voter
    ADD CONSTRAINT direct_voter_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE RESTRICT ON DELETE RESTRICT;


--
-- Name: draft_author_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY draft
    ADD CONSTRAINT draft_author_id_fkey FOREIGN KEY (author_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE RESTRICT;


--
-- Name: draft_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY draft
    ADD CONSTRAINT draft_initiative_id_fkey FOREIGN KEY (initiative_id) REFERENCES initiative(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: event_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY event
    ADD CONSTRAINT event_initiative_id_fkey FOREIGN KEY (initiative_id, draft_id) REFERENCES draft(initiative_id, id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: event_initiative_id_fkey1; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY event
    ADD CONSTRAINT event_initiative_id_fkey1 FOREIGN KEY (initiative_id, suggestion_id) REFERENCES suggestion(initiative_id, id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: event_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY event
    ADD CONSTRAINT event_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: event_issue_id_fkey1; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY event
    ADD CONSTRAINT event_issue_id_fkey1 FOREIGN KEY (issue_id, initiative_id) REFERENCES initiative(issue_id, id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: event_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY event
    ADD CONSTRAINT event_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE RESTRICT;


--
-- Name: ignored_initiative_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY ignored_initiative
    ADD CONSTRAINT ignored_initiative_initiative_id_fkey FOREIGN KEY (initiative_id) REFERENCES initiative(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: ignored_initiative_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY ignored_initiative
    ADD CONSTRAINT ignored_initiative_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: ignored_member_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY ignored_member
    ADD CONSTRAINT ignored_member_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: ignored_member_other_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY ignored_member
    ADD CONSTRAINT ignored_member_other_member_id_fkey FOREIGN KEY (other_member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: initiative_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY initiative
    ADD CONSTRAINT initiative_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: initiative_revoked_by_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY initiative
    ADD CONSTRAINT initiative_revoked_by_member_id_fkey FOREIGN KEY (revoked_by_member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE RESTRICT;


--
-- Name: initiative_setting_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY initiative_setting
    ADD CONSTRAINT initiative_setting_initiative_id_fkey FOREIGN KEY (initiative_id) REFERENCES initiative(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: initiative_setting_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY initiative_setting
    ADD CONSTRAINT initiative_setting_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: initiative_suggested_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY initiative
    ADD CONSTRAINT initiative_suggested_initiative_id_fkey FOREIGN KEY (suggested_initiative_id) REFERENCES initiative(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: initiator_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY initiator
    ADD CONSTRAINT initiator_initiative_id_fkey FOREIGN KEY (initiative_id) REFERENCES initiative(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: initiator_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY initiator
    ADD CONSTRAINT initiator_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: interest_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY interest
    ADD CONSTRAINT interest_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: interest_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY interest
    ADD CONSTRAINT interest_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: issue_area_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY issue
    ADD CONSTRAINT issue_area_id_fkey FOREIGN KEY (area_id) REFERENCES area(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: issue_comment_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY issue_comment
    ADD CONSTRAINT issue_comment_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: issue_comment_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY issue_comment
    ADD CONSTRAINT issue_comment_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: issue_policy_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY issue
    ADD CONSTRAINT issue_policy_id_fkey FOREIGN KEY (policy_id) REFERENCES policy(id) ON UPDATE CASCADE ON DELETE RESTRICT;


--
-- Name: issue_setting_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY issue_setting
    ADD CONSTRAINT issue_setting_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: issue_setting_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY issue_setting
    ADD CONSTRAINT issue_setting_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: member_application_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY member_application
    ADD CONSTRAINT member_application_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: member_history_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY member_history
    ADD CONSTRAINT member_history_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: member_image_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY member_image
    ADD CONSTRAINT member_image_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: member_relation_setting_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY member_relation_setting
    ADD CONSTRAINT member_relation_setting_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: member_relation_setting_other_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY member_relation_setting
    ADD CONSTRAINT member_relation_setting_other_member_id_fkey FOREIGN KEY (other_member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: membership_area_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY membership
    ADD CONSTRAINT membership_area_id_fkey FOREIGN KEY (area_id) REFERENCES area(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: membership_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY membership
    ADD CONSTRAINT membership_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: non_voter_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY non_voter
    ADD CONSTRAINT non_voter_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: non_voter_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY non_voter
    ADD CONSTRAINT non_voter_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: opinion_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY opinion
    ADD CONSTRAINT opinion_initiative_id_fkey FOREIGN KEY (initiative_id, suggestion_id) REFERENCES suggestion(initiative_id, id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: opinion_initiative_id_fkey1; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY opinion
    ADD CONSTRAINT opinion_initiative_id_fkey1 FOREIGN KEY (initiative_id, member_id) REFERENCES supporter(initiative_id, member_id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: privilege_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY privilege
    ADD CONSTRAINT privilege_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: privilege_unit_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY privilege
    ADD CONSTRAINT privilege_unit_id_fkey FOREIGN KEY (unit_id) REFERENCES unit(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: rendered_draft_draft_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY rendered_draft
    ADD CONSTRAINT rendered_draft_draft_id_fkey FOREIGN KEY (draft_id) REFERENCES draft(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: rendered_issue_comment_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY rendered_issue_comment
    ADD CONSTRAINT rendered_issue_comment_issue_id_fkey FOREIGN KEY (issue_id, member_id) REFERENCES issue_comment(issue_id, member_id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: rendered_member_statement_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY rendered_member_statement
    ADD CONSTRAINT rendered_member_statement_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: rendered_suggestion_suggestion_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY rendered_suggestion
    ADD CONSTRAINT rendered_suggestion_suggestion_id_fkey FOREIGN KEY (suggestion_id) REFERENCES suggestion(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: rendered_voting_comment_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY rendered_voting_comment
    ADD CONSTRAINT rendered_voting_comment_issue_id_fkey FOREIGN KEY (issue_id, member_id) REFERENCES voting_comment(issue_id, member_id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: session_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY session
    ADD CONSTRAINT session_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON DELETE SET NULL;


--
-- Name: setting_map_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY setting_map
    ADD CONSTRAINT setting_map_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: setting_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY setting
    ADD CONSTRAINT setting_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: suggestion_author_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY suggestion
    ADD CONSTRAINT suggestion_author_id_fkey FOREIGN KEY (author_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE RESTRICT;


--
-- Name: suggestion_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY suggestion
    ADD CONSTRAINT suggestion_initiative_id_fkey FOREIGN KEY (initiative_id) REFERENCES initiative(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: suggestion_initiative_id_fkey1; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY suggestion
    ADD CONSTRAINT suggestion_initiative_id_fkey1 FOREIGN KEY (initiative_id, draft_id) REFERENCES draft(initiative_id, id) ON UPDATE CASCADE;


--
-- Name: suggestion_setting_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY suggestion_setting
    ADD CONSTRAINT suggestion_setting_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: suggestion_setting_suggestion_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY suggestion_setting
    ADD CONSTRAINT suggestion_setting_suggestion_id_fkey FOREIGN KEY (suggestion_id) REFERENCES suggestion(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: supporter_initiative_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY supporter
    ADD CONSTRAINT supporter_initiative_id_fkey FOREIGN KEY (initiative_id, draft_id) REFERENCES draft(initiative_id, id) ON UPDATE CASCADE;


--
-- Name: supporter_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY supporter
    ADD CONSTRAINT supporter_issue_id_fkey FOREIGN KEY (issue_id, member_id) REFERENCES interest(issue_id, member_id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: unit_parent_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY unit
    ADD CONSTRAINT unit_parent_id_fkey FOREIGN KEY (parent_id) REFERENCES unit(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: unit_setting_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY unit_setting
    ADD CONSTRAINT unit_setting_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: unit_setting_unit_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY unit_setting
    ADD CONSTRAINT unit_setting_unit_id_fkey FOREIGN KEY (unit_id) REFERENCES unit(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: vote_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY vote
    ADD CONSTRAINT vote_issue_id_fkey FOREIGN KEY (issue_id, initiative_id) REFERENCES initiative(issue_id, id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: vote_issue_id_fkey1; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY vote
    ADD CONSTRAINT vote_issue_id_fkey1 FOREIGN KEY (issue_id, member_id) REFERENCES direct_voter(issue_id, member_id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: voting_comment_issue_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY voting_comment
    ADD CONSTRAINT voting_comment_issue_id_fkey FOREIGN KEY (issue_id) REFERENCES issue(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: voting_comment_member_id_fkey; Type: FK CONSTRAINT; Schema: public; Owner: www-data
--

ALTER TABLE ONLY voting_comment
    ADD CONSTRAINT voting_comment_member_id_fkey FOREIGN KEY (member_id) REFERENCES member(id) ON UPDATE CASCADE ON DELETE CASCADE;


--
-- Name: public; Type: ACL; Schema: -; Owner: postgres
--

REVOKE ALL ON SCHEMA public FROM PUBLIC;
REVOKE ALL ON SCHEMA public FROM postgres;
GRANT ALL ON SCHEMA public TO postgres;
GRANT ALL ON SCHEMA public TO PUBLIC;


--
-- PostgreSQL database dump complete
--

