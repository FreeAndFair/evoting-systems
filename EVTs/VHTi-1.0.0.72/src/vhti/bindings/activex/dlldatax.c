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
// wrapper for dlldata.c

#ifdef _MERGE_PROXYSTUB // merge proxy stub DLL

#define REGISTER_PROXY_DLL //DllRegisterServer, etc.

#define _WIN32_WINNT 0x0400	//for WinNT 4.0 or Win95 with DCOM
#define USE_STUBLESS_PROXY	//defined only with MIDL switch /Oicf

#pragma comment(lib, "rpcndr.lib")
#pragma comment(lib, "rpcns4.lib")
#pragma comment(lib, "rpcrt4.lib")

#define DllMain				PrxDllMain
#define DllRegisterServer	PrxDllRegisterServer
#define DllUnregisterServer PrxDllUnregisterServer
#define DllGetClassObject   PrxDllGetClassObject
#define DllCanUnloadNow     PrxDllCanUnloadNow

#include "dlldata.c"
#include "vhti_activex_p.c"

#ifdef _NOPROXY //no midl generated dlldata.c

#define STRICT 1
#include <ole2.h>

BOOL WINAPI PrxDllMain(HINSTANCE hInstance, DWORD dwReason, LPVOID lpReserved)
{return TRUE;}

STDAPI PrxDllCanUnloadNow(void){return S_OK;}

STDAPI PrxDllGetClassObject(REFCLSID rclsid, REFIID riid, LPVOID* ppv)
{return CLASS_E_CLASSNOTAVAILABLE;}

STDAPI PrxDllRegisterServer(void){return S_OK;}

STDAPI PrxDllUnregisterServer(void){return S_OK;}

#endif //!PROXY_DELEGATION

#endif //_MERGE_PROXYSTUB
