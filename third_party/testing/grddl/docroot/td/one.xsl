<!-- stylesheet that returns an empty RDF document -->
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform" 
 >

<!-- Output method XML -->
<xsl:output method="xml" 
  indent="yes"
  omit-xml-declaration="no" 
  encoding="utf-8"  />

  <xsl:template match="/">
    <rdf:RDF  xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
              >
       <rdf:Description rdf:value="one"/>
    </rdf:RDF>
  </xsl:template>
</xsl:stylesheet>
