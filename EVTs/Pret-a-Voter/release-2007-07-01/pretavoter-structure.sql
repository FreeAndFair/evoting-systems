-- MySQL dump 10.10
--
-- Host: localhost    Database: pretavoter
-- ------------------------------------------------------
-- Server version	5.0.27-community-nt

/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8 */;
/*!40103 SET @OLD_TIME_ZONE=@@TIME_ZONE */;
/*!40103 SET TIME_ZONE='+00:00' */;
/*!40014 SET @OLD_UNIQUE_CHECKS=@@UNIQUE_CHECKS, UNIQUE_CHECKS=0 */;
/*!40014 SET @OLD_FOREIGN_KEY_CHECKS=@@FOREIGN_KEY_CHECKS, FOREIGN_KEY_CHECKS=0 */;
/*!40101 SET @OLD_SQL_MODE=@@SQL_MODE, SQL_MODE='NO_AUTO_VALUE_ON_ZERO' */;
/*!40111 SET @OLD_SQL_NOTES=@@SQL_NOTES, SQL_NOTES=0 */;

--
-- Table structure for table `auditmachines`
--

DROP TABLE IF EXISTS `auditmachines`;
CREATE TABLE `auditmachines` (
  `auditmachine_id` int(10) unsigned NOT NULL default '0',
  `auditmachine_name` varchar(255) collate latin1_general_ci default NULL,
  `auditmachine_publickey` blob,
  PRIMARY KEY  (`auditmachine_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `ballotformaudits`
--

DROP TABLE IF EXISTS `ballotformaudits`;
CREATE TABLE `ballotformaudits` (
  `ballotform_serialno` int(11) NOT NULL,
  `teller_id` int(10) unsigned NOT NULL,
  `teller_batch` tinyint(1) unsigned NOT NULL,
  `audit_germ` blob NOT NULL,
  `audit_onion` blob NOT NULL,
  `audit_permutation` blob NOT NULL,
  `audit_plaintext_permutation` varchar(255) collate latin1_general_ci NOT NULL,
  PRIMARY KEY  (`ballotform_serialno`,`teller_id`,`teller_batch`),
  KEY `teller_id` (`teller_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `ballotformpapers`
--

DROP TABLE IF EXISTS `ballotformpapers`;
CREATE TABLE `ballotformpapers` (
  `ballotformpaper_id` int(11) NOT NULL,
  `ballotformpaper_hash` blob NOT NULL,
  `ballotformpaper_plaintext_hash` varchar(255) collate latin1_general_ci NOT NULL,
  `ballotformpaper_status` varchar(20) collate latin1_general_ci NOT NULL,
  `ballotformpaper_statuschangedate` datetime default NULL,
  `vote_object` blob,
  `receipt_object` blob,
  PRIMARY KEY  (`ballotformpaper_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `ballotformpaperstatuschangelogs`
--

DROP TABLE IF EXISTS `ballotformpaperstatuschangelogs`;
CREATE TABLE `ballotformpaperstatuschangelogs` (
  `bfpscl_id` int(11) unsigned NOT NULL auto_increment,
  `ballotformpaper_id` int(11) unsigned NOT NULL,
  `ballotformpaper_oldstatus` varchar(255) collate latin1_general_ci NOT NULL,
  `bfpscl_date` datetime NOT NULL,
  PRIMARY KEY  (`bfpscl_id`),
  KEY `ballotformpaper_id` (`ballotformpaper_id`)
) ENGINE=MyISAM AUTO_INCREMENT=8 DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `ballotforms`
--

DROP TABLE IF EXISTS `ballotforms`;
CREATE TABLE `ballotforms` (
  `ballotform_serialno` int(11) NOT NULL,
  `ballotform_status` varchar(20) collate latin1_general_ci NOT NULL default '',
  `election_id` int(10) unsigned NOT NULL,
  `race_id` int(10) unsigned NOT NULL,
  `booth_id` int(12) default NULL,
  `ballotform_object` blob NOT NULL,
  `ballotform_plaintext_vote` varchar(255) collate latin1_general_ci default NULL,
  `ballotform_statuschangedate` datetime default NULL,
  PRIMARY KEY  (`ballotform_serialno`),
  KEY `election_id` (`election_id`),
  KEY `race_id` (`race_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `ballotformsinpapers`
--

DROP TABLE IF EXISTS `ballotformsinpapers`;
CREATE TABLE `ballotformsinpapers` (
  `ballotformpaper_id` int(11) NOT NULL,
  `ballotform_id` int(11) NOT NULL,
  `position` int(11) NOT NULL,
  PRIMARY KEY  (`ballotformpaper_id`,`ballotform_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `booths`
--

DROP TABLE IF EXISTS `booths`;
CREATE TABLE `booths` (
  `booth_id` int(10) unsigned NOT NULL,
  `booth_name` varchar(255) collate latin1_general_ci default NULL,
  `booth_publickey` blob,
  PRIMARY KEY  (`booth_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `candidateraces`
--

DROP TABLE IF EXISTS `candidateraces`;
CREATE TABLE `candidateraces` (
  `election_id` int(10) unsigned NOT NULL,
  `race_id` int(10) unsigned NOT NULL,
  `candidate_id` int(10) unsigned NOT NULL,
  PRIMARY KEY  (`election_id`,`race_id`,`candidate_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `candidates`
--

DROP TABLE IF EXISTS `candidates`;
CREATE TABLE `candidates` (
  `candidate_id` int(10) unsigned NOT NULL,
  `candidate_name` varchar(255) collate latin1_general_ci NOT NULL,
  PRIMARY KEY  (`candidate_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `commitments`
--

DROP TABLE IF EXISTS `commitments`;
CREATE TABLE `commitments` (
  `election_id` int(11) unsigned NOT NULL,
  `race_id` int(11) unsigned NOT NULL,
  `teller_id` int(11) unsigned NOT NULL,
  `commitment_bulletinboard_nonce` blob NOT NULL,
  `commitment_commitment` blob NOT NULL,
  `commitment_teller_nonce` blob,
  `commitment_bitmap` blob,
  `commitment_received` datetime default NULL,
  PRIMARY KEY  (`election_id`,`race_id`,`teller_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `elections`
--

DROP TABLE IF EXISTS `elections`;
CREATE TABLE `elections` (
  `election_id` int(10) unsigned NOT NULL,
  `election_name` varchar(255) collate latin1_general_ci NOT NULL,
  `election_startdate` date NOT NULL,
  `election_enddate` date NOT NULL,
  PRIMARY KEY  (`election_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `races`
--

DROP TABLE IF EXISTS `races`;
CREATE TABLE `races` (
  `election_id` int(10) unsigned NOT NULL,
  `race_id` int(10) unsigned NOT NULL,
  `race_name` varchar(255) collate latin1_general_ci NOT NULL,
  PRIMARY KEY  (`election_id`,`race_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `receiptaudits`
--

DROP TABLE IF EXISTS `receiptaudits`;
CREATE TABLE `receiptaudits` (
  `receiptaudit_counter` int(12) unsigned NOT NULL auto_increment,
  `election_id` int(12) NOT NULL,
  `race_id` int(12) NOT NULL,
  `teller_id` int(12) NOT NULL,
  `left_receipt_position` int(20) NOT NULL default '0',
  `right_receipt_position` int(20) NOT NULL default '0',
  `audit_germ` blob,
  PRIMARY KEY  (`receiptaudit_counter`)
) ENGINE=MyISAM AUTO_INCREMENT=341 DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `receipts`
--

DROP TABLE IF EXISTS `receipts`;
CREATE TABLE `receipts` (
  `receipt_id` int(30) unsigned NOT NULL auto_increment,
  `election_id` int(10) unsigned NOT NULL,
  `race_id` int(10) unsigned NOT NULL,
  `teller_id` int(10) unsigned NOT NULL,
  `teller_batch` tinyint(1) unsigned NOT NULL,
  `receipt_partialform` blob NOT NULL,
  `receipt_plaintext_vote` varchar(255) collate latin1_general_ci default NULL,
  PRIMARY KEY  (`receipt_id`),
  KEY `race_id` (`election_id`,`race_id`),
  KEY `teller_id` (`teller_id`)
) ENGINE=MyISAM AUTO_INCREMENT=136595 DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `tallies`
--

DROP TABLE IF EXISTS `tallies`;
CREATE TABLE `tallies` (
  `election_id` int(12) NOT NULL,
  `race_id` int(12) NOT NULL,
  `tally_round` int(12) NOT NULL,
  `candidate_id` int(12) NOT NULL,
  `tally_votes` int(12) NOT NULL,
  PRIMARY KEY  (`election_id`,`race_id`,`tally_round`,`candidate_id`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

--
-- Table structure for table `tellers`
--

DROP TABLE IF EXISTS `tellers`;
CREATE TABLE `tellers` (
  `teller_id` int(10) unsigned NOT NULL,
  `teller_name` varchar(255) collate latin1_general_ci default NULL,
  `teller_ipaddress` varchar(15) collate latin1_general_ci default NULL,
  `teller_servername` varchar(255) collate latin1_general_ci default NULL,
  `teller_publickey` blob,
  `teller_sequencenumber` tinyint(3) default NULL,
  PRIMARY KEY  (`teller_id`),
  KEY `teller_sequencenumber` (`teller_sequencenumber`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `voterballotformpapers`
--

DROP TABLE IF EXISTS `voterballotformpapers`;
CREATE TABLE `voterballotformpapers` (
  `vbfp_id` int(11) NOT NULL auto_increment,
  `voter_id` int(11) NOT NULL,
  `ballotformpaper_id` int(11) NOT NULL,
  `vbfp_current` tinyint(1) NOT NULL default '1',
  `vbfp_date` datetime NOT NULL,
  PRIMARY KEY  (`vbfp_id`),
  KEY `voter_id` (`voter_id`,`ballotformpaper_id`)
) ENGINE=MyISAM AUTO_INCREMENT=2 DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;

--
-- Table structure for table `voters`
--

DROP TABLE IF EXISTS `voters`;
CREATE TABLE `voters` (
  `voter_id` int(11) NOT NULL,
  `voter_urn` varchar(10) collate latin1_general_ci NOT NULL,
  `voter_name` varchar(255) collate latin1_general_ci NOT NULL,
  `voter_dob` date NOT NULL,
  `voter_type` varchar(1) collate latin1_general_ci NOT NULL,
  PRIMARY KEY  (`voter_id`),
  KEY `voter_urn` (`voter_urn`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_ci;
/*!40103 SET TIME_ZONE=@OLD_TIME_ZONE */;

/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40014 SET UNIQUE_CHECKS=@OLD_UNIQUE_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;

-- Dump completed on 2007-05-30 11:22:20
