package org.scantegrity.common;
import java.awt.Point;
import java.io.IOException;

import org.junit.Test;
import org.scantegrity.common.SquareSpiralPattern;

/**
 * 
 */

/**
 * @author carback1
 *
 */
public class SquareSpiralTest {

	static int c_size = 12;
	
	/**
	 * @param args
	 */
	@Test
	public void TestSquareSpiral() throws IOException {
		char l_grid[][] = new char[c_size][c_size];
		
		for (int i = 0; i < c_size; i++) {
			for (int j = 0; j < c_size; j++)
			{
				l_grid[i][j] = '*';
			}
		}
		
		
		int l_startx = (c_size)/2-1;
		int l_starty = (c_size)/2-1;

		SquareSpiralPattern s = new SquareSpiralPattern(c_size);
		
		while (!s.isEmpty()) {
			Point next = s.next();
			//System.out.println(l_startx+next.x + ", " + (l_starty+next.y));
			//System.out.println(next.x + ", " + (next.y));			
			if (l_startx+next.x >= 0 && l_startx+next.x < c_size
					&& l_starty+next.y >= 0 && l_starty+next.y < c_size) {
				l_grid[l_startx+next.x][l_starty+next.y] = 'X';
				//printGrid(l_grid);
			}
			//System.in.read();
		}
		
		
		/*
		for (int l_r = 0; l_r < l_iters; l_r++) {
			//Take x to the right as far as possible
			while (l_x < l_max && l_x+l_startx < c_size && l_y+l_starty >= 0) {
				l_grid[l_x+l_startx][l_y+l_starty] = 'X';
				printGrid(l_grid);
				System.in.read();
				l_x++;
			}
			System.out.println(l_min + ", " + l_max);
			//Take y down as far as possible
			while (l_y < l_max && l_y+l_starty < c_size && l_x+l_startx < c_size) {
				l_grid[l_x+l_startx][l_y+l_starty] = 'X';
				printGrid(l_grid);
				System.in.read();
				l_y++;
			}
			System.out.println(l_min + ", " + l_max);
			//Take x to the left as far as possible
			while (l_x > l_min && l_x+l_startx >= 0 && l_y+l_starty < c_size) {
				l_grid[l_x+l_startx][l_y+l_starty] = 'X';
				printGrid(l_grid);
				System.in.read();
				l_x--;
			}
			System.out.println(l_min + ", " + l_max);
			
			//Take y up as far as possible
			while (l_y > l_min && l_y+l_starty >= 0 && l_x+l_startx >= 0) {
				l_grid[l_x+l_startx][l_y+l_starty] = 'X';
				printGrid(l_grid);
				System.in.read();
				l_y--;
			}			
			
			
			l_min--;
			l_max++;
			System.out.println(l_min + ", " + l_max);
		}
		System.out.println(l_min + ", " + l_max);
		System.out.println(l_startx+l_min + ", " + l_startx+l_max);
		System.out.println(l_starty+l_min + ", " + l_starty+l_max);
		*/
	}
	
	static void printGrid(char p_grid[][]) {
		for (int i = 0; i < c_size; i++) {
			for (int j = 0; j < c_size; j++)
			{
				System.out.print(p_grid[j][i] + " ");
			}
			System.out.print("\n");
		}
	}

}
