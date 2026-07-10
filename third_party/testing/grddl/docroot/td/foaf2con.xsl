<?xml version="1.0" encoding="utf-8"?>
<xsl:stylesheet version = '1.0'
     xmlns:xsl='http://www.w3.org/1999/XSL/Transform'
     xmlns:foaf="http://xmlns.com/foaf/0.1/"
     xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
     xmlns:con="http://www.w3.org/2000/10/swap/pim/contact#"
>

<xsl:template match="/">

<rdf:RDF>

<xsl:apply-templates />

</rdf:RDF>

</xsl:template>

<xsl:template match="foaf:Agent">
   <con:SocialEntity rdf:about="{@rdf:about}" />
</xsl:template>

</xsl:stylesheet>
