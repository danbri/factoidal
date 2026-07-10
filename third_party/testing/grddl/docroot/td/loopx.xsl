<?xml version="1.0" encoding="utf-8"?>
<!-- $Id: loopx.xsl,v 1.3 2007/03/28 14:17:58 jcarroll Exp $ -->
<xsl:stylesheet
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    xmlns:r="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
    xmlns:g="http://www.w3.org/2003/g/data-view#"
    version="1.0">
  <xsl:output method="xml" media-type="application/rdf+xml" indent="yes"/>

  <xsl:template match="/">
      <r:RDF>
	    <r:Description r:about="">
	      <g:namespaceTransformation
	      r:resource="loopy.xsl" />
	    </r:Description>
	  </r:RDF>
  </xsl:template>

</xsl:stylesheet>
