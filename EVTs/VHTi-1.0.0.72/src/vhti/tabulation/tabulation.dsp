# Microsoft Developer Studio Project File - Name="tabulation" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** DO NOT EDIT **

# TARGTYPE "Win32 (x86) Static Library" 0x0104

CFG=tabulation - Win32 Debug
!MESSAGE This is not a valid makefile. To build this project using NMAKE,
!MESSAGE use the Export Makefile command and run
!MESSAGE 
!MESSAGE NMAKE /f "tabulation.mak".
!MESSAGE 
!MESSAGE You can specify a configuration when running NMAKE
!MESSAGE by defining the macro CFG on the command line. For example:
!MESSAGE 
!MESSAGE NMAKE /f "tabulation.mak" CFG="tabulation - Win32 Debug"
!MESSAGE 
!MESSAGE Possible choices for configuration are:
!MESSAGE 
!MESSAGE "tabulation - Win32 Release" (based on "Win32 (x86) Static Library")
!MESSAGE "tabulation - Win32 Debug" (based on "Win32 (x86) Static Library")
!MESSAGE 

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
RSC=rc.exe

!IF  "$(CFG)" == "tabulation - Win32 Release"

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
# ADD LIB32 /nologo /out:"..\lib\tabulation.lib"

!ELSEIF  "$(CFG)" == "tabulation - Win32 Debug"

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
# ADD LIB32 /nologo /out:"..\lib\tabulation_a.lib"

!ENDIF 

# Begin Target

# Name "tabulation - Win32 Release"
# Name "tabulation - Win32 Debug"
# Begin Group "Source Files"

# PROP Default_Filter "cpp;c;cxx;rc;def;r;odl;idl;hpj;bat"
# Begin Source File

SOURCE=.\auth.cpp
# End Source File
# Begin Source File

SOURCE=.\check_dictionary_secrets.cpp
# End Source File
# Begin Source File

SOURCE=.\check_internal.cpp
# End Source File
# Begin Source File

SOURCE=.\check_partial_decrypt.cpp
# End Source File
# Begin Source File

SOURCE=.\check_partial_decrypts_and_combine.cpp
# End Source File
# Begin Source File

SOURCE=.\check_shuffle.cpp
# End Source File
# Begin Source File

SOURCE=.\check_vc_partial_decrypts_and_combine.cpp
# End Source File
# Begin Source File

SOURCE=.\combine_dictionary_secrets.cpp
# End Source File
# Begin Source File

SOURCE=.\gen_dictionary_secrets.cpp
# End Source File
# Begin Source File

SOURCE=.\gen_partial_verification_results.cpp
# End Source File
# Begin Source File

SOURCE=.\gen_pre_verification_results.cpp
# End Source File
# Begin Source File

SOURCE=.\partial_decrypt.cpp
# End Source File
# Begin Source File

SOURCE=.\shuffle.cpp
# End Source File
# Begin Source File

SOURCE=.\shuffle_internal.cpp
# End Source File
# Begin Source File

SOURCE=.\tabulation_internal.cpp
# End Source File
# End Group
# Begin Group "Header Files"

# PROP Default_Filter "h;hpp;hxx;hm;inl"
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\auth.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\check_dictionary_secrets.h
# End Source File
# Begin Source File

SOURCE=.\check_internal.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\check_partial_decrypt.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\check_partial_decrypts_and_combine.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\check_shuffle.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\check_shuffle_decrypt.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\check_vc_partial_decrypts_and_combine.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\combine_dictionary_secrets.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\gen_dictionary_secrets.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\gen_partial_verification_results.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\gen_pre_verification_results.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\partial_decrypt.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\publish.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\shuffle.h
# End Source File
# Begin Source File

SOURCE=..\..\..\vhti\include\vhti\shuffle_decrypt.h
# End Source File
# Begin Source File

SOURCE=.\shuffle_internal.h
# End Source File
# Begin Source File

SOURCE=.\tabulation_internal.h
# End Source File
# End Group
# End Target
# End Project
