<?xml-stylesheet href="http://www.w3.org/StyleSheets/base.css" type="text/css"?><?xml-stylesheet href="http://www.w3.org/2002/02/style-xsl.css" type="text/css"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns="http://www.w3.org/1999/xhtml" xmlns:html="http://www.w3.org/1999/xhtml" exclude-result-prefixes="html">

<!-- Output method XML -->
<xsl:output method="xml" 
  indent="yes"
  omit-xml-declaration="no" 
  encoding="utf-8"  />

 
<!-- Documenting the XSLT : fill the @@@-->
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <link rel="stylesheet" href="http://www.w3.org/StyleSheets/base"/>
    <title>Simple transform of XHTML</title>
  </head>
  <body>
    <div class='head'><a href="/"><img src="/Icons/w3c_home" alt="W3C"/></a></div>
    <h1>Simple transform of XHTML</h1>

    <p>This style sheet takes the <code>title</code> of an XHTML page, and returns an RDF statement that the said page has a <code>dc:title</code> of the content of the title element.</p>

    <p class="copyright">Copyright &#169; 2005 <a href="http://www.w3.org/">World Wide Web Consortium</a>, (<a
href="http://www.csail.mit.edu/"><acronym title="Massachusetts Institute of
Technology">M.I.T.</acronym></a>, <a
href="http://www.ercim.org/"><acronym
title="European Research Consortium for Informatics and Mathematics">ERCIM</acronym></a>, <a
href="http://www.keio.ac.jp/">Keio University</a>). All Rights
    Reserved. http://www.w3.org/Consortium/Legal/. W3C <a href="http://www.w3.org/Consortium/Legal/copyright-software">software licensing</a> rules apply.</p>
    <address><a href="http://www.w3.org/People/Dom/">Dominique Haza&#235;l-Massieux</a> - $Id: glean_title.xsl,v 1.2 2006/12/05 17:09:35 connolly Exp $</address>
    </body>
</html>

  <!-- default: Identity Transformation -->
  <xsl:template match="/">
    <rdf:RDF  xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">
      <!-- using rel=alternate for the subject is a bit of a kludge -->
      <xsl:variable name="subject"
		    select='/html:html/html:head/html:link[@rel="alternate"]/@href' />
      <rdf:Description rdf:about="{$subject}">
        <dc:title     xmlns:dc="http://purl.org/dc/elements/1.1/"><xsl:value-of select="/html:html/html:head/html:title"/></dc:title>
      </rdf:Description>
    </rdf:RDF>
  </xsl:template>

</xsl:stylesheet>