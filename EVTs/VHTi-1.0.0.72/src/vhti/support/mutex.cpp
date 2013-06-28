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
// Copyright 2003 VoteHere Inc. All Rights Reserved.

#include "mutex.h"
#include "misc/vh_excpt.h"

#if defined(__linux__)
#include "pch.hpp"
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/shm.h>

#include <cerrno>
#endif

namespace VHUtil{

Mutex::Mutex(int key)
{
#if defined(__linux__)
        bool setSemVal=true;

        m_semid=::semget(key,1,IPC_CREAT|IPC_EXCL|0666);

        if ( -1==m_semid && EEXIST==errno )
        {
                m_semid=::semget(key,1,IPC_CREAT|0666);
                setSemVal=false;
        }

        if ( -1 == m_semid )
        {
                        throw VHUtil::Exception(__FILE__,__LINE__,errno);
        }

        int arg=1;

        if ( setSemVal )
        {
                int rv=::semctl(m_semid,0,SETVAL,arg);
                if ( rv==-1 )
                        throw VHUtil::Exception(__FILE__,__LINE__,errno);
        }
#endif

#if defined(_WIN32)
        hMutex = CreateMutex(
           NULL,  // No security attributes
           FALSE, // Initially not owned
           "MutexToProtectAllSortsOfGlobalThingsIncludingButNotRestrictedToFixedModularExponentiation"); // Name of mutex
        
        if (hMutex == NULL)
        {
           throw VHUtil::Exception(__FILE__,__LINE__,"CREATE_MUTEX");
        }
#endif
}

void Mutex::Lock(void)
{
#if defined(__linux__)

        struct ::sembuf sop;
        sop.sem_num=0;
        sop.sem_op=-1;
        sop.sem_flg=0;
        int rv=::semop(m_semid,&sop,1);
        if ( rv==-1 )
                throw VHUtil::Exception(__FILE__,__LINE__,errno);
#endif

#if defined(_WIN32)
        
        DWORD dwWaitResult; 
        
        // Request ownership of mutex.
        // Don't care about return value in this implementation.
        dwWaitResult = WaitForSingleObject( 
           hMutex,   // handle to mutex
           INFINITE);   // five-second time-out interval
        
#endif
}

void Mutex::UnLock(void)
{
#if defined(__linux__)
        struct ::sembuf sop;
        sop.sem_num=0;
        sop.sem_op=1;
        sop.sem_flg=0;
        int rv=::semop(m_semid,&sop,1);
        if ( rv==-1 )
                throw VHUtil::Exception(__FILE__,__LINE__,errno);
#endif

#if defined(_WIN32)
        int win_rv = ReleaseMutex(hMutex);
        if (win_rv == 0)
           throw VHUtil::Exception(__FILE__,__LINE__,"RELEASE_MUTEX");

#endif

}

void Mutex::Remove(void)
{
#if defined(__linux__)
        int rv=::semctl(m_semid,0,IPC_RMID,0);
        if ( rv==-1 )
                throw VHUtil::Exception(__FILE__,__LINE__,errno);
#endif
#if defined(_WIN32)
        if (0 == CloseHandle(hMutex))
           throw VHUtil::Exception(__FILE__,__LINE__,"CLOSE_HANDLE_ON_MUTEX");
#endif
}

Mutex::~Mutex(void)
{
}

AutoMutex::AutoMutex(Mutex& mutex) : m_mutex(mutex)
{
        m_mutex.Lock();
}

AutoMutex::~AutoMutex(void)
{
        m_mutex.UnLock();
}

} // namespace VHUtil


