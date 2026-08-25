#!/usr/local/bin/perl

my ($targetdir) = "tests";
my ($counter) = 0;

while (<STDIN>) {
  if (/\?xml version/) {
    $counter++;
    open (FILE, ">$targetdir/file$counter.rdf") || die "Cannot create $targetdir/file$counter.rdf\n";
    print "Creating test file $targetdir/file$counter.rdf\n";
  }
  print FILE $_;
}

close (FILE);
