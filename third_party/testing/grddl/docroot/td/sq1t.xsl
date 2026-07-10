<xsl:transform
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    version="1.0"
    >
  <xsl:output method="xml" indent="yes" />

  <xsl:template match="/">
    <rdf:RDF  xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
	      xmlns:dc="http://purl.org/dc/elements/1.1/">
      <rdf:Description rdf:about="">
        <dc:description>an sq1 document</dc:description>
      </rdf:Description>
    </rdf:RDF>
  </xsl:template>
</xsl:transform>
