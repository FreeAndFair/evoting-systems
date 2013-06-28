-- create table ballotformaudits_web;
CREATE TABLE `ballotformaudits_web` (
`ballotform_serialno` int( 11 ) NOT NULL ,
`teller_id` int( 10 ) unsigned NOT NULL ,
`teller_batch` tinyint( 1 ) unsigned NOT NULL ,
`audit_germ` blob NOT NULL ,
`audit_onion` blob NOT NULL ,
`audit_permutation` blob NOT NULL ,
PRIMARY KEY ( `ballotform_serialno` , `teller_id` , `teller_batch` ) ,
KEY `teller_id` ( `teller_id` )
);

-- create table ballotformpapers_web;
CREATE TABLE `ballotformpapers_web` (
`ballotformpaper_id` int( 11 ) NOT NULL ,
`ballotformpaper_hash` blob NOT NULL ,
`ballotformpaper_status` varchar( 20 ) COLLATE latin1_general_ci NOT NULL ,
`ballotformpaper_statuschangedate` datetime default NULL ,
`vote_object` blob,
`receipt_object` blob,
PRIMARY KEY ( `ballotformpaper_id` )
);
ALTER TABLE `ballotformpapers_web` ADD `ballotformpaper_prettyhash` TEXT NOT NULL ;
ALTER TABLE `ballotformpapers_web` ADD `ballotformpaper_vote` TEXT NOT NULL ;

-- create table receipts_web;
CREATE TABLE `receipts_web` (
`receipt_id` int( 30 ) unsigned NOT NULL AUTO_INCREMENT ,
`election_id` int( 10 ) unsigned NOT NULL ,
`race_id` int( 10 ) unsigned NOT NULL ,
`teller_id` int( 10 ) unsigned NOT NULL ,
`teller_batch` tinyint( 1 ) unsigned NOT NULL ,
`receipt_partialform` blob NOT NULL ,
PRIMARY KEY ( `receipt_id` ) ,
KEY `race_id` ( `election_id` , `race_id` ) ,
KEY `teller_id` ( `teller_id` )
);

ALTER TABLE `receipts_web` ADD `partialform_permstring` TEXT NOT NULL ;