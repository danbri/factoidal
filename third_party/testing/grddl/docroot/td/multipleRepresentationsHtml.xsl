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
    <title>Multiple Representations HTML Stylesheet</title>
  </head>
  <body>
    <div class='head'><a href="/"><img src="/Icons/w3c_home" alt="W3C"/></a></div>
    <h1>Multiple Representations HTML Stylesheet</h1>

    <p>This style sheet Generates two triples:</p>

    <ol>
      <li>&lt;_:bnode, dc:title, "Multiple Representations HTML Stylesheet"&gt;</li>
      <li>&lt; _:bnode, ex:mimetype "text/html"&gt;</li>
    </ol>
  </body>
</html>
  <xsl:template match="/">
    <rdf:RDF  xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
              xmlns:ex="http://example.org/test#">
              
      <rdf:Description>
        <dc:title xmlns:dc="http://purl.org/dc/elements/1.1/"><xsl:value-of select="/html:html/html:head/html:title"/></dc:title>
        <ex:mimetype>text/html</ex:mimetype>
      </rdf:Description>

    </rdf:RDF>
  </xsl:template>
</xsl:stylesheet>