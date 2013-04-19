/*
    Copyright 2012, Henrik Ingo

    This file is part of Solon Voting.

    Solon is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Solon is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Solon.  If not, see <http://www.gnu.org/licenses/>.
*/

CREATE TYPE issue_state AS ENUM (
    'voting',
    'public_voting_closed',
    'private_voting_closed',
    'closed'
);


CREATE TABLE issues (
    id integer PRIMARY KEY,
    data text,
    state issue_state DEFAULT 'voting'::issue_state NOT NULL
);

CREATE TABLE last_event_id (
    id integer,
    state issue_state
);

-- This is like vote table in lqfb
CREATE TABLE "direct_private_votes" (
        "issue_id"              INT4            NOT NULL,
        PRIMARY KEY ("initiative_id", "member_id"),
        "initiative_id"         INT4,
        "member_id"             INT4,
        "grade"                 INT4 
        );
CREATE INDEX "direct_private_votes_issue_member_idx" ON "direct_private_votes" ("issue_id", "member_id");

-- This table stores those who voted for a person, not an initiative. Ie. they delegated their vote.
-- Trustee is the other member you delegate to: member_id delegates to trustee_member_id
CREATE TABLE "delegated_private_votes" (
        "issue_id"              INT4            NOT NULL,
        PRIMARY KEY ("issue_id", "member_id"),
        "member_id"             INT4,
        "trustee_member_id"     INT4
        );
CREATE INDEX "delegated_private_votes_issue_member_idx" ON "delegated_private_votes" ("trustee_member_id");


-- Just like direct_private_votes
CREATE TABLE "public_votes" (
        "issue_id"              INT4            NOT NULL,
        PRIMARY KEY ("initiative_id", "member_id"),
        "initiative_id"         INT4,
        "member_id"             INT4,
        "grade"                 INT4 
        );
CREATE INDEX "public_votes_issue_member_idx" ON "public_votes" ("issue_id", "member_id");


-- Helper view which JOINs delegated_private_votes with public_votes in such a way 
-- that the outcome is identical to if the user had voted in direct_private_votes
CREATE OR REPLACE VIEW "delegated_private_votes_outcome" 
        AS 
        SELECT "p"."issue_id", "p"."initiative_id", "d"."member_id", "p"."grade"
        FROM "public_votes" "p"
        JOIN "delegated_private_votes" "d" 
        ON "p"."member_id" = "d"."trustee_member_id" AND "p"."issue_id" = "d"."issue_id";



-- This is the total tally of both direct and delegated private votes combined
CREATE OR REPLACE VIEW "all_private_votes_outcome"
       AS
       SELECT * 
       FROM "direct_private_votes"
       UNION
       SELECT *
       FROM "delegated_private_votes_outcome";

CREATE OR REPLACE VIEW "all_private_votes_statusquo"
       AS
         SELECT "issue_id", "initiative_id", "member_id", "grade" FROM "all_private_votes_outcome"
       UNION
         SELECT "issue_id", NULL "initiative_id", "member_id", 0 "grade" 
         FROM "all_private_votes_outcome" 
         GROUP BY "issue_id", "member_id";


CREATE OR REPLACE VIEW "private_votes_pairs"
       AS
       SELECT "better_vote"."issue_id", "better_vote"."member_id",
       "better_vote"."initiative_id" "better_initiative_id", "worse_vote"."initiative_id" "worse_initiative_id",
       coalesce (
         CASE WHEN
           coalesce("better_vote"."grade", 0) >
           coalesce("worse_vote"."grade", 0)
         THEN 1 ELSE 0 END
       ) AS "count"
       FROM "all_private_votes_statusquo" "better_vote"
       JOIN "all_private_votes_statusquo" "worse_vote"
       ON "better_vote"."issue_id" = "worse_vote"."issue_id" AND "better_vote"."member_id" = "worse_vote"."member_id" AND (
             "better_vote"."initiative_id" != "worse_vote"."initiative_id" OR 
            ("better_vote"."initiative_id" ISNULL AND "worse_vote"."initiative_id" NOTNULL) OR
            ("better_vote"."initiative_id" NOTNULL AND "worse_vote"."initiative_id" ISNULL) ); 

CREATE OR REPLACE VIEW "battle_view"
       AS
       SELECT "issue_id", "better_initiative_id" "winning_initiative_id", 
              "worse_initiative_id" "losing_initiative_id", SUM("count") "count" 
       FROM "private_votes_pairs" 
       GROUP BY "issue_id", "winning_initiative_id", "losing_initiative_id" 
       ORDER BY "issue_id", "winning_initiative_id", "losing_initiative_id";
