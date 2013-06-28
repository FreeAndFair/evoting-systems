/*  */
/* This material is subject to the VoteHere Source Code Evaluation */
/* License Agreement ("Agreement").  Possession and/or use of this */
/* material indicates your acceptance of this Agreement in its entirety. */
/* Copies of the Agreement may be found at www.votehere.net. */
/*  */
/* Copyright 2004 VoteHere, Inc.  All Rights Reserved */
/*  */
/* You may not download this Software if you are located in any country */
/* (or are a national of a country) subject to a general U.S. or */
/* U.N. embargo or are deemed to be a terrorist country (i.e., Cuba, */
/* Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States */
/* (each a "Prohibited Country") or are otherwise denied export */
/* privileges from the United States or Canada ("Denied Person"). */
/* Further, you may not transfer or re-export the Software to any such */
/* country or Denied Person without a license or authorization from the */
/* U.S. government.  By downloading the Software, you represent and */
/* warrant that you are not a Denied Person, are not located in or a */
/* national of a Prohibited Country, and will not export or re-export to */
/* any Prohibited Country or Denied Party. */
#ifndef CU_TEST_H
#define CU_TEST_H

#include <setjmp.h>
#include <stdarg.h>

/* CuString */

char* CuStrAlloc(int size);
char* CuStrCopy(char* old);

#define CU_ALLOC(TYPE)		((TYPE*) malloc(sizeof(TYPE)))

#define HUGE_STRING_LEN	8192
#define STRING_MAX		256
#define STRING_INC		256

typedef struct
{
	int length;
	int size;
	char* buffer;
} CuString;

void CuStringInit(CuString* str);
CuString* CuStringNew(void);
void CuStringRead(CuString* str, char* path);
void CuStringAppend(CuString* str, char* text);
void CuStringAppendChar(CuString* str, char ch);
void CuStringAppendFormat(CuString* str, char* format, ...);
void CuStringResize(CuString* str, int newSize);

/* CuTest */

typedef struct CuTest CuTest;

typedef void (*TestFunction)(CuTest *);

struct CuTest
{
	char* name;
	TestFunction function;
	int failed;
	int ran;
	char* message;
	jmp_buf *jumpBuf;
};

void CuTestInit(CuTest* t, char* name, TestFunction function);
CuTest* CuTestNew(char* name, TestFunction function);
void CuFail(CuTest* tc, char* message);
void CuAssert(CuTest* tc, char* message, int condition);
void CuAssertTrue(CuTest* tc, int condition);
void CuAssertStrEquals(CuTest* tc, char* expected, char* actual);
void CuAssertIntEquals(CuTest* tc, int expected, int actual);
void CuAssertPtrEquals(CuTest* tc, void* expected, void* actual);
void CuAssertPtrNotNull(CuTest* tc, void* pointer);
void CuTestRun(CuTest* tc);

/* CuSuite */

#define MAX_TEST_CASES	1024	

#define SUITE_ADD_TEST(SUITE,TEST)	CuSuiteAdd(SUITE, CuTestNew(#TEST, TEST))

typedef struct
{
	int count;
	CuTest* list[MAX_TEST_CASES]; 
	int failCount;

} CuSuite;


void CuSuiteInit(CuSuite* testSuite);
CuSuite* CuSuiteNew();
void CuSuiteAdd(CuSuite* testSuite, CuTest *testCase);
void CuSuiteAddSuite(CuSuite* testSuite, CuSuite* testSuite2);
void CuSuiteRun(CuSuite* testSuite);
void CuSuiteSummary(CuSuite* testSuite, CuString* summary);
void CuSuiteDetails(CuSuite* testSuite, CuString* details);

#endif /* CU_TEST_H */
