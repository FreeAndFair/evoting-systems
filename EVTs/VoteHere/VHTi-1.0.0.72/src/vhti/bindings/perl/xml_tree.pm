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
package XML_Tree;

use Carp;
use Carp::Assert;
use XML_Tree_Creator;
use Data::Dumper;

our $xml_decl = qq(<?xml version="1.0" encoding="utf-8" ?>\n);

sub new {
  my $oldself  = shift;
  my $class = ref($oldself) || $oldself;
  my $xml = shift;
  if ($xml) {
    my $constructor = new XML_Tree_Creator;

    $newself = $constructor->parse($xml);
  }
  return $newself;
}

sub construct {
   my $class = shift;
   my $name = shift;

   return bless {
      name => $name,
      atts => {},
      num_ele => 0,
      elems => [],
      chars => [''],
      parent => 0,
   }, $class;
}

sub parent {
   my $self = shift;

   $self->{parent};
}

sub name {
   my $self = shift;

   $self->{name};
}

sub num_elements {
   my $self = shift;

   $self->{num_ele};
}

sub elements {
   my $self = shift;

   $self->{elems};
}

sub element {
   my $self = shift;
   my $index = shift;

   assert($index < $self->num_elements) if DEBUG;

   $self->elements->[$index];
}

sub e {
   my $self = shift;
   my $name = shift;
   my $index = 0;
   # even # of params implies no index.
   unless ($#_ & 1) {
      $index = shift;
   }
   my $att = {@_};
   my $matches = 0;

   @ele = map {
      if (($_->name eq $name)
         && ($_->matches_attributes($att))
         && ($index == ($matches ++))) {
         return $_;
      }
   } @{$self->elements};

   undef;
}

sub characters {
   my $self = shift;

   join('', @{$self->all_characters});
}

sub remove_all_characters {
   my $self = shift;

   for my $each (@{$self->all_characters}) {
      $each = '';
   }
}

sub all_characters {
   my $self = shift;

   $self->{chars};
}

sub characters_before {
   my $self = shift;
   my $index = shift;

   assert($index <= $self->num_elements) if DEBUG;

   $self->all_characters->[$index];
}

sub new_element {
   my $self = shift;
   my $name = shift;

   my $newel = construct(XML_Tree, $name);
   $self->add_element($newel);

   $newel;
}

sub add_element {
   my $self = shift;
   my $new = shift;

   $self->{num_ele} ++;
   push @{$self->elements}, $new;
   push @{$self->all_characters}, '';
   $new->{parent} = $self;

   $self;
}

sub add_element_before {
   my $self = shift;
   my $new = shift;
   my $index = shift;

   $index = 0 if (!defined ($index)) ;

   assert($index < $self->num_elements) if DEBUG;

   $self->{num_ele} ++;

   splice @{$self->elements}, $index, 0, $new;
   splice @{$self->all_characters}, $index, 0, '';
   $new->{parent} = $self;

   $new;
}

sub delete_element {
  my $self = shift;
  my $index = shift;

  assert($index < $self->num_elements) if DEBUG;

  splice @{$self->{elems}}, $index, 1;
  $self->{num_ele} --;
}

sub add_characters {
   my $self = shift;
   my $chars = shift;

   $self->all_characters->[$self->num_elements] .= $chars;

   $self;
}

sub attributes {
   my $self = shift;

   $self->{atts};
}

sub add_attribute {
   my $self = shift;
   my $name = shift;
   my $value = shift;

   $self->attributes->{$name} = $value;

   $self;
}

sub has_attribute {
   my $self = shift;
   my $name = shift;

   defined $self->attributes->{$name};
}

sub attribute {
   my $self = shift;
   my $name = shift;

   $self->attributes->{$name};
}

sub a {
   my $self = shift;
   my $name = shift;

   unless (defined $self->attributes->{$name}) {
      undef;
   } else {
      $self->attributes->{$name};
   }
}

sub matches_attributes {
   my $self = shift;
   my $req = shift;

   for my $key (keys %$req) {
      my $val = $req->{$key};
      unless ($self->has_attribute($key)) {
         return 0;
      }
      unless ($self->attribute($key) eq $val) {
         return 0;
      }
   }
   1;
}

sub format_as_text {
  my $self = shift;
  $xml_decl
    . $self->internal_format_as_text ();
}

sub internal_format_as_text {
   my $self = shift;

   ((0 == $self->num_elements) && ( 0 == length $self->characters))
   ? ("<" . $self->name . $self->format_attributes . "/>")
   : ("<" . $self->name . $self->format_attributes . ">"
      . $self->format_content . "</" . $self->name . ">");
}

sub format_attributes {
   my $self = shift;

   my $result = '';

   while (my ($key, $value) = each(%{$self->attributes})) {
      $result .= " $key=\"$value\"";
   }

   $result;
}

sub format_content {
   my $self = shift;

   my $result = '';

   for my $index (0 .. ($self->num_elements - 1)) {
      $result .= $self->entitified_characters_before($index);
      $result .= $self->element($index)->internal_format_as_text;
   }
   $result .= $self->entitified_characters_before($self->num_elements);

   $result;
}

sub entitified_characters_before {
   my $self = shift;
   my $index = shift;

   my $chars = $self->characters_before($index);
   $chars =~ s/\&/&amp;/g;
   $chars =~ s/\</&lt;/g;
   $chars =~ s/\>/&gt;/g;

   # This is crucial.  Hopefully I'll make this all unnecessary soon,
   # but until then, here's an explanation of a problem, and why this
   # is a solution.

   # The problem is that VHTI's signing and checking functions don't
   # do quite the right thing with XML, and we're trying to work
   # around that here.  Both signing and checking "canonicalize" their
   # XML input before hashing.  But that canonicalization is slightly
   # broken.  The short story is that "<a>\r</a>" canonicalizes to
   # "<a>\n</a>", whereas "<a>&#13;</a>" remains unchanged.  This is
   # bizarre, since `&#13;' is precisely the character reference that
   # represents "\r"; any sane person would expect both those inputs
   # to canonicalize to the same thing.  But this bizarre behavior is
   # actually legal according to http://www.w3.org/TR/REC-xml, section
   # 2.11.  (It's conceivable that libxml can be taught to Quit Doing
   # That, Then, but I don't know how).

   # Anyway, simply ensuring that we always emit a character reference
   # instead of an actual carriage return works around the problem for
   # now.  But the real solution is to quit signing XML in the first
   # place, and instead sign byte streams; that way nobody has to
   # waste a day discovering these subtleties.

   $chars =~ s/\r/&#13;/g;

   # You could also turn *all* non-ASCII characters into character
   # references, like this.  This is handy in itself (in that it
   # prevents scary weird stuff from appearing in your XML), and it
   # further mimics the behavior of libxml2.  However, there's no need
   # to do it, since we include proper encoding information in our XML
   # declaration.

   if (1) {
     # November 2003: turn this back on to work around a problem that
     # I cannot reproduce reliably -- some of the VHTI tests fail when
     # parsing XML that we emitted.
     $chars =~ s/(\P{IsASCII})/sprintf "&#x%X;", ord $1/ge;
   }

   $chars;
}

{
  no warnings qw(once);
  eval join('',<main::DATA>) || die $@ unless caller();
}
1;
__END__

use Test::More qw(no_plan);

my $t = XML_Tree->construct ("Sam");
$t->new_element ("Foo");
$t->new_element ("Bar");
$t->new_element ("Baz");
$t->new_element ("Ugh");

eval {
  $t->delete_element ($t->num_elements ());
};
ok ($@, "proper exception with too-large index to delete_element");

$t->delete_element (0);
is ($t->format_as_text, $xml_decl . q(<Sam><Bar/><Baz/><Ugh/></Sam>), "expected result after deleting first element");
$t->delete_element ($t->num_elements () - 1);
is ($t->format_as_text, $xml_decl . q(<Sam><Bar/><Baz/></Sam>), "expected result after deleting last element");

while ($t->num_elements ()) {
  $t->delete_element (0);
}

is (0, $t->num_elements (), "deleting all elements leaves zero elements behind");

$t->add_element (XML_Tree->construct ("FooTwo"));
$t->add_element_before (XML_Tree->construct ("FooOne"), 0);
is ($t->format_as_text, $xml_decl . q(<Sam><FooOne/><FooTwo/></Sam>), "expected result after inserting element");
$t->add_element_before (XML_Tree->construct ("FooZero"), 0);
is ($t->format_as_text, $xml_decl . q(<Sam><FooZero/><FooOne/><FooTwo/></Sam>), "expected result after inserting element");

my $weird_binary_element = $t->add_element_before (XML_Tree->construct ("OhNo"));
$weird_binary_element->add_characters ("\x13\x100\x1000\x2000\x4000\x8000\xD7FF\xE000\xFFFD\x10000");

# Ensure we can reparse it
eval {
  XML_Tree->new ($t->format_as_text ());
};
like ($@, qr(), "No problem parsing binary stuff");

print XML_Tree->new ("$xml_decl<foo/>")->format_as_text (), "\n";
