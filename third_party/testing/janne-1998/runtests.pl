#!/usr/local/bin/perl
#
# (C)opyright 1998 Janne Saarela/World Wide Web Consortium
#
# Run tests with the SiRPAC compiler to see if any output file contains null's
#

my($start_sirpac) = "java -Dorg.xml.sax.parser=com.ibm.xml.parser.SAXDriver org.w3c.rdf.SiRPAC";


my(@files) = <*.rdf>;

foreach $rdfsource (@files) {
  print "Processing $rdfsource...";
  `$start_sirpac $rdfsource >$rdfsource.triples`;
  my $nulls = `fgrep null $rdfsource.triples`;
  $nulls .= `fgrep Error $rdfsource.triples`;
  if ($nulls eq "" && (-s "$rdfsource.triples")) {
    print "...ok\n";
  } else {
    print "...not ok.\n";
  }
}
