// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   Constants.java

package org.scantegrity.common.ballotstandards;

import java.io.Serializable;

public class Constants
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = 3724459003196530723L;
	
	public Constants()
    {
    }

    public static String TAG_RESULTS = "results";
    public static String TAG_FILLED_IN_BALLOT = "filledInBallot";
    public static String TAG_EMPTY_BALLOT = "emptyBallot";
    public static String TAG_ELECTION_SPECIFICATION = "electionSpecification";
    public static String TAG_ANSWER = "answer";
    public static String TAG_QUESTION = "question";
    public static String TAG_DEPENDS = "depends";
    public static String TAG_TEXT = "text";
    public static String TAG_ELECTIONINFO = "electionInfo";
    public static String TAG_SECTION = "section";
    public static String TAG_AUDIO = "audio";
    public static String TAG_IMAGE = "image";
    public static String TAG_LOCATION = "location";
    public static String TAG_SECTIONS = "sections";
    public static String TAG_QUESTIONS = "questions";
    public static String TAG_ANSWERS = "answers";
    public static String TAG_TEXTS = "texts";
    public static String TAG_AUDIOS = "audios";
    public static String TAG_IMAGES = "images";
    public static String ATTRIBUTE_TYPE_OF_ANSWER = "typeOfAnswerChoice";
    public static String ATTRIBUTE_MAX_ANSWERS = "max_number_of_answers_selected";
    public static String ATTRIBUTE_MIN_ANSWERS = "min_number_of_answers_selected";
    public static String ATTRIBUTE_TYPE = "type";
    public static String ATTRIBUTE_ID = "id";
    public static String ATTRIBUTE_POSSITION = "possition";
    public static String ATTRIBUTE_POINTS = "points";
    public static String ONE_ANSWER = "one_answer";
    public static String MULTIPLE_ANSWERS = "multiple_answers";
    public static String DISTRIBUTE_POINTS = "distribute_points";
    public static String RANK = "rank";
    public static String WRITEIN = "_writein";
    public static String OVERVOTE = "_overvote";
    public static String UNDERVOTE = "_undervote";

}
