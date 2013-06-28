/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.io.*;

/**
 * A file filter.
 *
 * @version $Id: FileNameFilter.java,v 1.4 2004/05/29 17:39:57 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class FileNameFilter extends javax.swing.filechooser.FileFilter
{
   /** Allowed extension of files accepted by this filter. */
   String extension; //@ in objectState;

   /** Description of files accepted by this filter. */
   String description; //@ in objectState;

   /**
    * Constructs a filter which accepts files with extension
    * <code>extension</code>. These files are described by
    * <code>description</code>.
    *
    * @param extension file extension.
    * @param description file description.
    */
   /*@ pure @*/ public FileNameFilter(String extension, String description) {
      this.extension = extension;
      this.description = description;
   }

   /**
    * Whether this filter accepts <code>file</code>.
    *
    * @return a boolean indicating whether this filter accepts
    *    <code>file</code>.
    */
   /*@ pure @*/ public boolean accept(File file) {
      String filename = file.getName();
      return (file.isDirectory() || filename.endsWith(extension));
   }

   /**
    * Description of files accepted by this filter.
    *
    * @return a description of files accepted by this filter.
    */
   /*@ pure @*/ public String getDescription() {
      return description;
   }
}

