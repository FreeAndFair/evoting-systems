/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package votebox.middle.driver;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;

import votebox.middle.IBallotVars;

/**
 * This class encapsulates the behavior our primitive IGlobalVars deserializer.
 * Global variables are stored in a new-line delineated format, in the following
 * order: root ballot path, ballot file, ballot file schema, layout file, layout
 * file schema. "Root path" means the path to the directory which contanis all
 * ballot xml files and a directory named "media" where all media files are
 * located. Both schemas and the ballot file should be in a fully qualified
 * path+filename format. For the layout file entry, include a fully qualified
 * path+prefix, where prefix follows the layout xml convention: prefix_<size>_<language>.
 * 
 * @author Kyle
 * 
 */
public class GlobalVarsReader {
    private final URL BallotSchema = getClass().getResource(
        "/votebox/middle/schema/ballot_schema.xsd" );

    private final URL LayoutSchema = getClass().getResource(
        "/votebox/middle/schema/layout_schema.xsd" );

    private final String Filename = "ballotbox.cfg";

    private String _rootPath;

    /**
     * This is the public constructor for GlobalVarsReader.
     * 
     * @param rootpath
     *            This is the path to the root of the media package.
     */
    public GlobalVarsReader(String rootpath) {
        _rootPath = rootpath;
    }

    /**
     * Call this method to read enough information off the decorated stream so
     * that one IGlobalVars object can be constructed with the information from
     * the stream.
     * 
     * @return This method returns an IGlobalVars object that reflects the data
     *         on the decorated stream.
     * @throws IOException
     *             This method throws if there are problems reading from the
     *             stream.
     */
    public IBallotVars parse() throws IOException {
        BufferedReader b = new BufferedReader( new InputStreamReader(
                new FileInputStream( _rootPath + File.separatorChar + Filename ) ) );

        final String ballotstring = b.readLine();
        final String layoutstring = b.readLine();

        return new IBallotVars() {

            public String getBallotPath() {
                return _rootPath;
            }

            public String getBallotFile() {
                return _rootPath + ballotstring;
            }

            public URL getBallotSchema() {
                return BallotSchema;
            }

            public String getLayoutFile() {
                return _rootPath + layoutstring;
            }

            public URL getLayoutSchema() {
                return LayoutSchema;
            }
        };
    }
}
