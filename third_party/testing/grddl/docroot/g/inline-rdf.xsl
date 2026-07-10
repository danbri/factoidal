<?xml-stylesheet href="http://www.w3.org/StyleSheets/base.css" type="text/css"?>
<?xml-stylesheet href="http://www.w3.org/2002/02/style-xsl.css" type="text/css"?>

<xsl:transform
    version="1.0"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
    xmlns:data-view="http://www.w3.org/2003/g/data-view#" 
    xmlns:xa="http://www.w3.org/2003/g/xml-attributes#"
    >

<xsl:import href="xml-attributes" />

<!-- set non-default mode of processing -->
<xsl:variable name="xa:use-xml-base-in-xhtml"
              select="true()" />
              
<xsl:output method="xml" encoding="utf-8" indent="yes" />

<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <link rel="stylesheet" href="http://www.w3.org/StyleSheets/base"/>
    <title>Extracting Inline RDF</title>
  </head>
  <body>
    <div class='head'><a href="/"><img src="/Icons/w3c_home" alt="W3C"/></a></div>
    <h1>inline-rdf.xsl &#8212; extract inline RDF</h1>


<p>This is a <a href="http://www.w3.org/TR/grddl">GRDDL</a>
transformation that lifts embedded RDF out of XML documents.</p>

<p>Values for xml:lang and xml:base are inherited from
ancestor elements in the original document, as appropriate.</p>

<p>This is part of the <a href="http://www.w3.org/2001/sw/grddl-wg/library">standard library</a> of GRDDL transforms.</p>

<p>
This transform is copyright, 2004-2007, W3C.
It is available for use under the terms of the
<a href="http://www.w3.org/Consortium/Legal/2002/copyright-software-20021231">W3C Software License</a>
</p>
<!--
  <address>
Dan Connolly, Dec 2004 <br />
</address>
-->
<p>
<small>$Id: inline-rdf.xsl,v 1.2 2007/06/15 12:55:41 jcarroll Exp $</small>
</p>
  </body>
</html>

<xsl:template match="/">
<rdf:RDF>
   <xsl:apply-templates />
</rdf:RDF>
</xsl:template>

<xsl:template match="rdf:RDF">
  <xsl:apply-templates select="*" mode="rdfTopLevel" />
</xsl:template>


<xsl:template match="*"  mode="rdfTopLevel" priority="1" >
  <xsl:copy>
  <!-- copy attributes -->
    <xsl:copy-of select="@*" />
  <!-- redefine xml:lang, and xml:base -->
    <xsl:call-template name="xa:base-and-lang" />
  <!-- copy other content -->
    <xsl:copy-of select="node()"/>
  </xsl:copy>
</xsl:template>


<!-- don't pass text through. -->
<xsl:template match="text()|@*">
</xsl:template>

</xsl:transform>

