<?xml-stylesheet href="http://www.w3.org/StyleSheets/base.css" type="text/css"?><?xml-stylesheet href="http://www.w3.org/2002/02/style-xsl.css" type="text/css"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns="http://www.w3.org/1999/xhtml" xmlns:svg="http://www.w3.org/2000/svg">

<!-- Output method XML -->
<xsl:output method="xml" 
  indent="yes"
  omit-xml-declaration="no" 
  encoding="utf-8"  />

 
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <link rel="stylesheet" href="http://www.w3.org/StyleSheets/base"/>
    <title>Simple transformation for SVG</title>
  </head>
  <body>
    <div class='head'><a href="/"><img src="/Icons/w3c_home" alt="W3C"/></a></div>
    <h1>Simple transformation for SVG</h1>

    <p>This style sheet takes the <code>title</code> of an SVG document, and returns an RDF statement that the said page has a <code>dc:title</code> of the content of the title element.</p>

    <p class="copyright">Copyright &#169; 2005 <a href="http://www.w3.org/">World Wide Web Consortium</a>, (<a
href="http://www.csail.mit.edu/"><acronym title="Massachusetts Institute of
Technology">M.I.T.</acronym></a>, <a
href="http://www.ercim.org/"><acronym
title="European Research Consortium for Informatics and Mathematics">ERCIM</acronym></a>, <a
href="http://www.keio.ac.jp/">Keio University</a>). All Rights
    Reserved. http://www.w3.org/Consortium/Legal/. W3C <a href="http://www.w3.org/Consortium/Legal/copyright-software">software licensing</a> rules apply.</p>
    <address><a href="http://www.w3.org/People/Dom/">Dominique Haza&#235;l-Massieux</a> - $Id: svg2dc.xsl,v 1.1 2007/03/27 16:10:33 jcarroll Exp $</address>
    </body>
</html>


  <xsl:template match="/">
    <rdf:RDF  xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">
      <rdf:Description rdf:about="">
        <dc:title     xmlns:dc="http://purl.org/dc/elements/1.1/"><xsl:value-of select="/svg:svg/svg:title"/></dc:title>
      </rdf:Description>
    </rdf:RDF>
  </xsl:template>

</xsl:stylesheet>