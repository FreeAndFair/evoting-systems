-- MySQL dump 10.10
--
-- Host: localhost    Database: pavteller
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
-- Table structure for table `batches`
--

DROP TABLE IF EXISTS `batches`;
CREATE TABLE `batches` (
  `batch_internal_id` int(12) unsigned NOT NULL auto_increment,
  `election_id` int(12) unsigned NOT NULL,
  `race_id` int(12) unsigned NOT NULL,
  `batch_id` int(12) unsigned NOT NULL,
  `batch_column` tinyint(1) NOT NULL,
  `batch_date` datetime NOT NULL,
  PRIMARY KEY  (`batch_internal_id`)
) ENGINE=MyISAM AUTO_INCREMENT=181 DEFAULT CHARSET=utf8;

--
-- Table structure for table `commitments`
--

DROP TABLE IF EXISTS `commitments`;
CREATE TABLE `commitments` (
  `election_id` int(12) unsigned NOT NULL,
  `race_id` int(12) unsigned NOT NULL,
  `commitment_bulletinboard_nonce` blob NOT NULL,
  `commitment_commitment` blob NOT NULL,
  `commitment_teller_nonce` blob NOT NULL,
  `commitment_bitmap` blob NOT NULL,
  `commitment_received` datetime NOT NULL,
  PRIMARY KEY  (`election_id`,`race_id`)
) ENGINE=MyISAM DEFAULT CHARSET=utf8;

--
-- Table structure for table `onionlayers`
--

DROP TABLE IF EXISTS `onionlayers`;
CREATE TABLE `onionlayers` (
  `top_onion_id` int(12) unsigned NOT NULL,
  `bottom_onion_id` int(12) unsigned NOT NULL,
  `layer_permutation` blob NOT NULL,
  `layer_random` blob NOT NULL,
  PRIMARY KEY  (`top_onion_id`,`bottom_onion_id`)
) ENGINE=MyISAM DEFAULT CHARSET=utf8;

--
-- Table structure for table `onions`
--

DROP TABLE IF EXISTS `onions`;
CREATE TABLE `onions` (
  `onion_id` int(12) unsigned NOT NULL auto_increment,
  `onion_hash` text NOT NULL,
  `onion_random` blob,
  `onion_date` datetime NOT NULL,
  `batch_id` int(12) unsigned,
  `batch_place` int(12) unsigned,
  `batch_sorted_place` int(12),
  PRIMARY KEY  (`onion_id`),
  KEY `batch_id` (`batch_id`)
) ENGINE=MyISAM AUTO_INCREMENT=1561 DEFAULT CHARSET=utf8;
/*!40103 SET TIME_ZONE=@OLD_TIME_ZONE */;

/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40014 SET UNIQUE_CHECKS=@OLD_UNIQUE_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;

-- Dump completed on 2007-05-15 16:11:06
