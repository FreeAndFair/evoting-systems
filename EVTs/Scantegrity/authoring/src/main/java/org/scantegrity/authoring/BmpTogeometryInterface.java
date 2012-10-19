package org.scantegrity.authoring;

import java.awt.image.BufferedImage;
import java.util.Vector;

import org.scantegrity.common.Cluster;

public interface BmpTogeometryInterface {

	/** 
	 * @param bi - the image to be scanned
	 * @param dpi - the dpi of the image (it cannot be infered from the image since
	 * some images do not have a dpi)
	 * @param noCols - the number of columns the contests are arranged in
	 * @param geometryFile - where to write the geometry file
	 * @param electionSpecFile - where to write the default Election Specification
	 * @throws Exception - an exception is thrown if the number of bullets is different
	 *  from the number of dunots for one contest (or for the serial number)  
	 */
	public void createGeometry(BufferedImage bi, float dpi, int noCols,String geometryFile,String electionSpecFile) throws Exception;
	
	/**
	 * @return - all the Colors that the image is scanned for
	 */
	public Vector<Cluster> getAllColors();
}
