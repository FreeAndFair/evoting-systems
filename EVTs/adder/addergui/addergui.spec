%define name	addergui
%define version	0.1.0
%define release	1
%define qtdir	%{_prefix}/lib/qt4
%define icon	images/addericon.png

Summary:	Adder Private Summary Register GUI
Name:		%{name}
Version:	%{version}
Release:	%mkrel %{release}
Epoch:		0
URL:		http://www.cse.uconn.edu/~adder/
Source0:	%{name}-%{version}.tar.bz2
License:	GPL
Group:		Networking/Other
Requires:	qca2-plugin-openssl-%{_lib}
Requires(post):	desktop-file-utils
Requires(postun): desktop-file-utils
BuildRequires:	boost-devel
BuildRequires:	ImageMagick
BuildRequires:	libadder-devel
BuildRequires:	qca2-devel
BuildRequires:	qconf
BuildRequires:	qt4-devel
Buildroot:	%{_tmppath}/%{name}-%{version}-%{release}-root

%description
Adder Private Summary Register GUI

%prep
%setup -q -n %{name}

%build
%{_bindir}/qconf
./configure --prefix=%{_prefix} \
            --bindir=%{_bindir} \
            --qtdir=%{qtdir}
%{__make}

%install
%{__rm} -rf %{buildroot}
%{__make} INSTALL_ROOT=%{buildroot} install

%{__mkdir_p} %{buildroot}%{_menudir}
%{__cat} > %{buildroot}%{_menudir}/%{name} << EOF
?package(%{name}): \\
command="%{_bindir}/%{name}" \\
needs="X11" \\
icon="%{name}.png" \\
section="Internet/Other" \\
title="Adder" \\
longtitle="Voting client"
EOF

%{__mkdir_p} %{buildroot}{%{_liconsdir},%{_iconsdir},%{_miconsdir}}
%{__mkdir_p} %{buildroot}%{_datadir}/icons/hicolor/{64x64,128x128}/apps
%{_bindir}/convert %{icon} -resize 48x48 %{buildroot}%{_liconsdir}/%{name}.png
%{_bindir}/convert %{icon} -resize 32x32 %{buildroot}%{_iconsdir}/%{name}.png
%{_bindir}/convert %{icon} -resize 16x16 %{buildroot}%{_miconsdir}/%{name}.png
%{_bindir}/convert %{icon} -resize 128x128 %{buildroot}%{_datadir}/icons/hicolor/128x128/apps/%{name}.png
%{_bindir}/convert %{icon} -resize 64x64 %{buildroot}%{_datadir}/icons/hicolor/64x64/apps/%{name}.png

%clean
%{__rm} -rf %{buildroot}

%post
%{update_menus}
%{_bindir}/update-desktop-database %{_datadir}/applications
if [ -x %{_bindir}/gtk-update-icon-cache ]; then
 %{_bindir}/gtk-update-icon-cache --force --quiet %{_datadir}/icons/hicolor
fi

%postun
%{clean_menus}
%{_bindir}/update-desktop-database %{_datadir}/applications
if [ "$1" = "0" -a -x %{_bindir}/gtk-update-icon-cache ]; then
  %{_bindir}/gtk-update-icon-cache --force --quiet %{_datadir}/icons/hicolor
fi

%files
%defattr(-,root,root)
%doc COPYING AUTHORS README TODO
%{_bindir}/%{name}
%{_menudir}/%{name}
%{_miconsdir}/%{name}.png
%{_iconsdir}/%{name}.png
%{_liconsdir}/%{name}.png
%{_datadir}/icons/hicolor/64x64/apps/%{name}.png
%{_datadir}/icons/hicolor/128x128/apps/%{name}.png

%changelog
* Sun May 07 2006 David Walluck <adder@cse.uconn.edu> 0:0.1.0-1mdk
- release
