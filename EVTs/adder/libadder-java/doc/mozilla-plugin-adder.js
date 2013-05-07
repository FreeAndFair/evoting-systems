/* -*- Mode: JavaScript; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */
/*
 * Adder plugin for Mozilla
 * Copyright (C) 2004 The Adder Team
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 */

var adderName = "Adder Plugin";
var adderMimeType = "application/adder;version=0.0.1";

var adderHaveSignedXPI = false;

var ADDER_SUCCESS = 0;
var ADDER_ERROR_INSTALL_TRIGGER_DISABLED = -1;
var ADDER_ERROR_SIGNED_XPI_UNSAFE = -2;

/**
 * Find the Adder plugin if it exists.
 *
 * @return the plugin object if available, or null otherwise
 */
function adderFindPlugin() {
    if (!navigator.mimeTypes) {
        return null;
    }

    var mimeType = navigator.mimeTypes[adderMimeType];

    if (mimeType) {
        var plugin = mimeType.enabledPlugin;

        if (plugin) {
            return plugin;
        }
    }

    return null;
}

/**
 * Returns whether or not we are running an IE browser.
 *
 * @return true if we are running IE, or false otherwise
 */
function adderIsIE() {
    return (navigator.userAgent.indexOf("MSIE") != -1
            && navigator.userAgent.indexOf("Win") != -1);
}

/**
 * Returns whether or not we are running a Mozilla browser.
 *
 * @return true if we are running Mozilla, or false otherwise
 */
function adderIsMozilla() {
    return ("product" in navigator && navigator.product == "Gecko");
}

/**
 * Gets the IE version into an array.
 *
 * @return an array representing major, minor, version, build
 */ 
function adderGetIEVersion() {
    var ieVersion = new Array(2);

    var msie;

    var major;
    var minor;

    msie = navigator.userAgent.match(/MSIE (\d+)\.(\d+)/);

    if (msie) {
        major = msie[1];
        minor = msie[2];

        ieVersion[0] = major;
        ieVersion[1] = minor;

        return ieVersion;
    }

    return null;
}

/**
 * Gets the Mozilla version into an array.
 *
 * @return an array representing major, minor, version, build
 */ 
function adderGetMozillaVersion() {
    var mozillaVersion = new Array(4);

    var rv;

    var major;
    var minor;
    var micro;
    var build;

    rv = navigator.userAgent.match(/rv:(\d+)\.(\d+)(\.(\d+))?(\w*)/);

    if (rv) {
        major = rv[1];
        minor = rv[2];
        micro = rv[4];
        build = rv[5];

        mozillaVersion[0] = major;
        mozillaVersion[1] = minor;
        mozillaVersion[2] = micro;
        mozillaVersion[3] = build;

        return mozillaVersion;
    }

    return null;
}

/**
 * Returns whether or not it is safe to install a signed XPI.
 *
 * @return true if it's safe to install a signed XPI, or false otherwise
 */
function adderSafeToInstallSignedXPI() {
    if (!adderIsMozilla()) {
        return false;
    }

    var mozillaVersion =  adderGetMozillaVersion();
    var major = mozillaVersion[0];
    var minor = mozillaVersion[1];

    return (major > 1 || (major == 1 && minor >= 7));
}

/**
 * Check the integrity of the plugin's scripting capabilities.
 *
 * @return true if all scripting functions available, or false otherwise
 */
function adderCheckIntegrity(obj) {
    var type = "function";
    var EXPECTED_COUNT = 12;
    var count = -1;

    if (obj && (typeof(obj) == "object" || typeof(obj) == "function")) {
        count++; // 0
    }

    if (adderIsIE()) {
        /* MSIE returns ``unknown'', which isn't even a documented type! */
        type = "unknown";

        /* 
         * MSIE can't handle the rest of the code, and this always returns
         * true.
         */
        return (count == 0);
    }

    if ("encryptVote"      in obj && typeof(obj.encryptVote)      == type) {
        count++; // 1
    }

    if ("createKeyPair"    in obj && typeof(obj.createKeyPair)    == type) {
        count++; // 2
    }

    if ("decryptSum"       in obj && typeof(obj.decryptSum)       == type) {
        count++; // 3
    }

    if ("readPubKey"       in obj && typeof(obj.readPubKey)       == type) {
        count++; // 4
    }

    if ("readPrivKey"      in obj && typeof(obj.readPrivKey)      == type) {
        count++; // 5
    }

    if ("writePrivKey"     in obj && typeof(obj.writePrivKey)     == type) {
        count++; // 6
    }

    if ("readPrivKey2"     in obj && typeof(obj.readPrivKey2)     == type) {
        count++; // 7
    }

    if ("writePrivKey2"    in obj && typeof(obj.writePrivKey2)    == type) {
        count++; // 8
    }

    if ("computeSecretKey" in obj && typeof(obj.computeSecretKey) == type) {
        count++; // 9
    }

    if ("encryptPoly"      in obj && typeof(obj.encryptPoly)      == type) {
        count++; // 10
    }

    if ("encryptGValue"    in obj && typeof(obj.encryptGValue)    == type) {
        count++; // 11
    }

    if ("shortHash"    in obj && typeof(obj.shortHash)            == type) {
        count++; // 12
    }

    return (count == EXPECTED_COUNT);
}

/**
 * Returns whether we can install the plugin.
 *
 * @return ADDER_SUCCESS if we can install the plugin, or less than zero otherwise
 */
function adderCanInstallPlugin() {
    if (!adderIsMozilla()) {
        return ADDER_SUCESS; // XXX
    }

    if (!InstallTrigger.enabled()) {
        return ADDER_ERROR_INSTALL_TRIGGER_DISABLED;
    } else if (adderHaveSignedXPI) {
        if (!adderSafeToInstallSignedXPI()) {
            return ADDER_ERROR_SIGNED_XPI_UNSAFE;
        }
    }

    return ADDER_SUCCESS;
}
