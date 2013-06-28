# 
# This material is subject to the VoteHere Source Code Evaluation
# License Agreement ("Agreement").  Possession and/or use of this
# material indicates your acceptance of this Agreement in its entirety.
# Copies of the Agreement may be found at www.votehere.net.
# 
# Copyright 2004 VoteHere, Inc.  All Rights Reserved
# 
# You may not download this Software if you are located in any country
# (or are a national of a country) subject to a general U.S. or
# U.N. embargo or are deemed to be a terrorist country (i.e., Cuba,
# Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States
# (each a "Prohibited Country") or are otherwise denied export
# privileges from the United States or Canada ("Denied Person").
# Further, you may not transfer or re-export the Software to any such
# country or Denied Person without a license or authorization from the
# U.S. government.  By downloading the Software, you represent and
# warrant that you are not a Denied Person, are not located in or a
# national of a Prohibited Country, and will not export or re-export to
# any Prohibited Country or Denied Party.
die qq( 
  This is not a standalone script.  Please run it using 
  mkinterface.pl or your own wrapper around 
  VHTI_INTERFACE.pm
) if (! defined $generator_loaded_flag);

my $project   = 'vhti_call';
my $extension = '';

use Data::Dumper;
$Data::Dumper::Purity = 1;

no_vhti_free();
no_vhti_dup();

open (FILE, ">$root_path/$project$extension") || croak "Unable to open $project$extension $!";
select FILE;

print <<'THESTART';
#!/usr/bin/perl -w

require VHTI;
THESTART

for (sort @function_files) {
   /(?:.*?\/)*(.*)?\.h/;
   print "require VHTI::$1;\n";
}

print <<'THEMAINSCRIPT';

VHTI::set_error_mode('CROAK');

$fns = '';
$fn = '';
$fnname = '';
$mod = '';
@in = ();
@out = ();

$fns = eval {
   my $VAR1 = '';
   eval join('', <DATA>);
   $VAR1;
};

$fn = shift @ARGV;
die "ERROR: You must specify a function to invoke" unless defined $fn;
if ($fn =~ /^VHTI_/) {
   $fnname = $fn;
   $fn = $';
} else {
   $fnname = 'VHTI_' . $fn;
}

$fn_data = $fns->{$fnname};
die "ERROR: Unknown function $fn" unless defined $fn_data;

for (@{$fn_data->{ARGS}}) {
   die (
      "ERROR: Not enough arguments to $fn:\n" 
      . join("\n", map { 
            "   " . $_->{DIR} . " " . $_->{RTYPE} 
         } @{$fn_data->{ARGS}})
      . "\n"
   ) unless defined ($_->{ARGV} = shift @ARGV);
}

unless ($fn_data->{FILE} =~ /.*\/(.*).h/) {
   die "ERROR: Unable to determine module for $fn\n";
} else {
   $mod = $1;
}

$fn = "VHTI::" . $mod . "::" . $fn;

for (@{$fn_data->{IN}}) {
   SWITCH: {
      ($_->{ARGV} =~ /^\./) && do {
         # The argument is a filename.
         open (FILE, ("<" . $_->{ARGV})) || (
            die "ERROR: Unable to open input file " . $_->{ARGV} . ": $!");
         push @in, ($_->{VALUE} = join('', <FILE>));
         close FILE;
         last SWITCH;
      };
      ($_->{ARGV} =~ /^</) && do {
         # The argument is literal xml.
         push @in, ($_->{VALUE} = $_->{ARGV});
         last SWITCH;
      };
      ($_->{ARGV} =~ /^"/) && do {
         # The argument is a string.
         $_->{ARGV} =~ s/"//g;
         push @in, ($_->{VALUE} = $_->{ARGV});
         last SWITCH;
      };
      ($_->{ARGV} =~ /^\d+/) && do {
         # The argument is a number.
         push @in, ($_->{VALUE} = $_->{ARGV});
         last SWITCH;
      };
      ($_->{ARGV} =~ /^-/) && do {
         # The argument should be read from STDIN.
         push @in, ($_->{VALUE} = join('', <STDIN>));
         last SWITCH;
      };
      die "ERROR: Unrecognized input parameter: $_->{ARGV}.";
   }
}

@out = $fn->(@in);

for (@{$fn_data->{OUT}}) {
   $_->{VALUE} = shift @out;
   SWITCH: {
      ($_->{ARGV} =~ /^\./) && do {
         # The argument is a filename.
         open (FILE, (">" . $_->{ARGV})) || (
            die "ERROR: Unable to open output file " . $_->{ARGV} . ": $!");
         print FILE $_->{VALUE};
         close FILE;
         last SWITCH;
      };
      ($_->{ARGV} =~ /^-/) && do {
         # The argument should be written to STDOUT.
         print $_->{VALUE};
         last SWITCH;
      };
      die "ERROR: Unrecognized output parameter: $_->{ARGV}."
   }
}

exit 0;

THEMAINSCRIPT

print "__END__\n";
print Dumper({%functions});

select STDOUT;
close FILE;

