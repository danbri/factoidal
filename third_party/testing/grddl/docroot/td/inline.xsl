<?xml version="1.0" encoding="utf-8"?>
<!-- $Id: inline.xsl,v 1.1 2007/03/13 19:55:27 cogbuji Exp $ -->
<xsl:stylesheet
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    xmlns:r="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
    xmlns:dc="http://purl.org/dc/elements/1.1/"
    xmlns:h="http://www.w3.org/1999/xhtml"
    version="1.0">
  <xsl:output method="xml" media-type="application/rdf+xml" indent="yes"/>

  <xsl:template match="/">
    <r:RDF>
      <xsl:apply-templates/>
    </r:RDF>
  </xsl:template>

  <xsl:template match="h:title">
    <r:Description r:about="">
      <dc:title><xsl:value-of select="."/></dc:title>
    </r:Description>
  </xsl:template>

  <!-- Text gets ignored. -->
  <xsl:template match="text()|@*"/>
</xsl:stylesheet>
