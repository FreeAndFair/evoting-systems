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
package XML_Tree_Creator;

use Data::Dumper;
use Carp;
use Carp::Assert;
use XML::SAX;
use XML::SAX::ParserFactory;

sub new {
   my $class = shift;
   my $xml = shift;

   my $self = bless {}, $class;

   $self;
}

sub up {
   my $self = shift;

   $self->{currel} = $self->current->parent;

   # print "after up, currel = $self->{currel}\n";
   $self;
}

sub current {
   my $self = shift;

   $self->{currel};
}

sub start_document {
   my $self = shift;
   my $struct = shift;

   $self->{currel} = construct XML_Tree("bogus root");

   # print 'in start_document: ' . Dumper($struct) . "\n";
   $self;
}

sub end_document {
   my $self = shift;
   my $struct = shift;

   $self->{root} = $self->current->element(0);
   # $self->up;
   assert($self->current->name eq 'bogus root') if DEBUG;

   # print 'in end_document: ' . Dumper($struct) . "\n";
   $self;
}

sub start_element {
   my $self = shift;
   my $struct = shift;

   my $newel = $self->current->new_element($struct->{Name});
   $self->{currel} = $newel;
   
   while (($name, $value) = each %{$struct->{Attributes}}) {
      $self->current->add_attribute($value->{Name}, $value->{Value});
   }

   # print 'in start_element: ' . Dumper($struct) . "\n";
   $self;
}

sub end_element {
   my $self = shift;
   my $struct = shift;

   assert($self->current->name eq $struct->{Name}) if DEBUG;
   $self->up;

   # print 'in end_element: ' . Dumper($struct) . "\n";
   $self;
}

sub characters {
   my $self = shift;
   my $struct = shift;

   $self->current->add_characters($struct->{Data});

   # print 'in characters: ' . Dumper($struct) . "\n";
   $self;
}

sub parse {
   my $self = shift;
   my $xml = shift;

   unless (defined $xml) {
      $xml = $self;
      $self = &new;
   }

   my $p = XML::SAX::ParserFactory->parser(Handler => $self);

   $p->parse_string($xml);

   return $self->{root};

   sub handle_char
   {
      my $ex = shift;
      my $string = shift;

      print "handle char ($string)\n";

      $current->add_chars($string);
   }

   sub handle_start
   {
      my $ex = shift;
      my $el = shift;
      my $atts = { @_ };

      print "handle start ($el)\n";

      my $new = &construct;
      $current->add_element($new);

      $current = $new;
      $current->{name} = $el;
      $current->{atts} = $atts;
   }

   sub handle_end
   {
      my $ex = shift;
      my $el = shift;

      print "handle end ($el)\n";

      should ($el, $current->name) if DEBUG;
      $current = $current->parent;
   }

}

1;

