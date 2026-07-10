<?xml-stylesheet href="http://www.w3.org/StyleSheets/base.css" type="text/css"?><?xml-stylesheet href="http://www.w3.org/2002/02/style-xsl.css" type="text/css"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns="http://www.w3.org/1999/xhtml"
  xmlns:h="http://www.w3.org/1999/xhtml"
  xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
  xmlns:foaf="http://xmlns.com/foaf/0.1/"
  exclude-result-prefixes="h">

<!-- Output method XML -->
<xsl:output method="xml" 
  indent="yes"
  omit-xml-declaration="no" 
  encoding="utf-8"  />

 
<!-- Documenting the XSLT : fill the @@@-->
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <link rel="stylesheet" href="http://www.w3.org/StyleSheets/base"/>
    <title>Get author from XHTML address</title>
  </head>
  <body>
    <div class='head'><a href="/"><img src="/Icons/w3c_home" alt="W3C"/></a></div>
    <h1>Get author from XHTML address</h1>

    <p>This style sheet extracts a page about the author of an XHTML document by extracting links annotated with a <code>rel='page'</code> in the  <code>address</code> elements, and returns an RDF statement that the said page has a <code>foaf:maker</code> with a <code>foaf:isPrimaryTopicOf</code> the content of the said link.</p>

    <p class="copyright">Copyright &#169; 2005 <a href="http://www.w3.org/">World Wide Web Consortium</a>, (<a
href="http://www.csail.mit.edu/"><acronym title="Massachusetts Institute of
Technology">M.I.T.</acronym></a>, <a
href="http://www.ercim.org/"><acronym
title="European Research Consortium for Informatics and Mathematics">ERCIM</acronym></a>, <a
href="http://www.keio.ac.jp/">Keio University</a>). All Rights
    Reserved. http://www.w3.org/Consortium/Legal/. W3C <a href="http://www.w3.org/Consortium/Legal/copyright-software">software licensing</a> rules apply.</p>
    <address><a href="http://www.w3.org/People/Dom/">Dominique Haza&#235;l-Massieux</a> - $Id: getAuthor.xsl,v 1.7 2007/04/20 15:08:46 jcarroll Exp $</address>
    </body>
</html>

  <xsl:template match="/">
    <rdf:RDF>
      <xsl:apply-templates />
    </rdf:RDF>
  </xsl:template>

  <xsl:template match="h:address/h:a[@rel='page']">

    <!-- using rel=alternate for the subject is a bit of a kludge -->
    <xsl:variable name="subject"
	select='/h:html/h:head/h:link[@rel="alternate"]/@href' />
    <rdf:Description rdf:about="{$subject}">
      <foaf:maker>
	<foaf:Agent>
	  <foaf:isPrimaryTopicOf rdf:resource="{@href}"/>
	</foaf:Agent>
      </foaf:maker>
    </rdf:Description>
  </xsl:template>

  <xsl:template match="h:address/h:a[@rel='maker']">
    <!-- using rel=alternate for the subject is a bit of a kludge -->
    <xsl:variable name="subject"
	select='/h:html/h:head/h:link[@rel="alternate"]/@href' />
    <rdf:Description rdf:about="{$subject}">
      <foaf:maker>
	<foaf:Agent rdf:about="{@href}">
	  <foaf:name><xsl:value-of select="normalize-space(.)"/></foaf:name>
	</foaf:Agent>
      </foaf:maker>
    </rdf:Description>
  </xsl:template>

<!-- Dom's old code -->
  <xsl:template match="h:address/h:a[@rel='homepage'][@href]">
      <rdf:Description rdf:about="">
          <dc:creator     xmlns:dc="http://purl.org/dc/elements/1.1/" rdf:parseType="Resource">
            <foaf:homepage xmlns:foaf="http://xmlns.com/foaf/0.1/" rdf:resource="{@href}"/>
            
          </dc:creator>
      </rdf:Description>
  </xsl:template>
      
  <!-- don't pass text thru -->
  <xsl:template match="text()|@*">
  </xsl:template>

  
</xsl:stylesheet>