# Microsoft Developer Studio Project File - Name="keyshare" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** DO NOT EDIT **

# TARGTYPE "Win32 (x86) Static Library" 0x0104

CFG=keyshare - Win32 Debug
!MESSAGE This is not a valid makefile. To build this project using NMAKE,
!MESSAGE use the Export Makefile command and run
!MESSAGE 
!MESSAGE NMAKE /f "keyshare.mak".
!MESSAGE 
!MESSAGE You can specify a configuration when running NMAKE
!MESSAGE by defining the macro CFG on the command line. For example:
!MESSAGE 
!MESSAGE NMAKE /f "keyshare.mak" CFG="keyshare - Win32 Debug"
!MESSAGE 
!MESSAGE Possible choices for configuration are:
!MESSAGE 
!MESSAGE "keyshare - Win32 Release" (based on "Win32 (x86) Static Library")
!MESSAGE "keyshare - Win32 Debug" (based on "Win32 (x86) Static Library")
!MESSAGE 

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
RSC=rc.exe

!IF  "$(CFG)" == "keyshare - Win32 Release"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 0
# PROP BASE Output_Dir "Release"
# PROP BASE Intermediate_Dir "Release"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 0
# PROP Output_Dir "Release"
# PROP Intermediate_Dir "Release"
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_MBCS" /D "_LIB" /YX /FD /c
# ADD CPP /nologo /MD /W3 /GX /O2 /I "../../include" /I "../" /D "WIN32" /D "NDEBUG" /D "_MBCS" /D "_LIB" /FD /c
# SUBTRACT CPP /YX
# ADD BASE RSC /l 0x409 /d "NDEBUG"
# ADD RSC /l 0x409 /d "NDEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LIB32=link.exe -lib
# ADD BASE LIB32 /nologo
# ADD LIB32 /nologo /out:"..\lib\keyshare.lib"

!ELSEIF  "$(CFG)" == "keyshare - Win32 Debug"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "Debug"
# PROP BASE Intermediate_Dir "Debug"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "Debug"
# PROP Intermediate_Dir "Debug"
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_MBCS" /D "_LIB" /YX /FD /GZ /c
# ADD CPP /nologo /MDd /W3 /Gm /GX /ZI /Od /I "../../include" /I "../" /D "WIN32" /D "_DEBUG" /D "_MBCS" /D "_LIB" /FAs /FR /FD /GZ /c
# SUBTRACT CPP /YX
# ADD BASE RSC /l 0x409 /d "_DEBUG"
# ADD RSC /l 0x409 /d "_DEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LIB32=link.exe -lib
# ADD BASE LIB32 /nologo
# ADD LIB32 /nologo /out:"..\lib\keyshare_a.lib"

!ENDIF 

# Begin Target

# Name "keyshare - Win32 Release"
# Name "keyshare - Win32 Debug"
# Begin Group "Source Files"

# PROP Default_Filter "cpp;c;cxx;rc;def;r;odl;idl;hpj;bat"
# Begin Source File

SOURCE=.\check_comm.cpp
# End Source File
# Begin Source File

SOURCE=.\gen_broadcast.cpp
# End Source File
# Begin Source File

SOURCE=.\gen_comm.cpp
# End Source File
# Begin Source File

SOURCE=.\gen_pubkey.cpp
# End Source File
# Begin Source File

SOURCE=.\gen_seccoeff.cpp
# End Source File
# Begin Source File

SOURCE=.\gen_secrets.cpp
# End Source File
# Begin Source File

SOURCE=.\keyshare_internal.cpp
# End Source File
# Begin Source File

SOURCE=.\keyshare_util.cpp
# End Source File
# End Group
# Begin Group "Header Files"

# PROP Default_Filter "h;hpp;hxx;hm;inl"
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\check_comm.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\gen_broadcast.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\gen_comm.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\gen_pubkey.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\gen_seccoeff.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\gen_secrets.h
# End Source File
# Begin Source File

SOURCE=.\keyshare_internal.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\keyshare_util.h
# End Source File
# End Group
# End Target
# End Project
