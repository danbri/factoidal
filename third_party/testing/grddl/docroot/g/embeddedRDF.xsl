<?xml-stylesheet href="http://www.w3.org/StyleSheets/base.css" type="text/css"?>
<?xml-stylesheet href="http://www.w3.org/2002/02/style-xsl.css" type="text/css"?>

<xsl:transform
    version="1.0"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
    xmlns:data-view="http://www.w3.org/2003/g/data-view#" 
    >

<xsl:output method="xml" encoding="utf-8" indent="yes" />

<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <link rel="stylesheet" href="http://www.w3.org/StyleSheets/base"/>
    <title>(Deprecated) Extracting Embedded RDF</title>
  </head>
  <body>
    <div class='head'><a href="/"><img src="/Icons/w3c_home" alt="W3C"/></a></div>
    <h1>Deprecated embeddedRDF.xsl &#8212; extract embedded RDF</h1>

<p>
This transform is deprecated, please use <a href="inline-rdf">inline-rdf</a>.
</p>

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
<small>$Id: embeddedRDF.xsl,v 1.18 2007/06/19 10:45:17 jcarroll Exp $</small>
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
    <xsl:attribute name="xml:lang">
      <xsl:value-of select="ancestor-or-self::*[@xml:lang][1]/@xml:lang" />
    </xsl:attribute>
    
    <xsl:if test="ancestor-or-self::*[position()!=last()][@xml:base]">
        <xsl:call-template name="xmlbase"/>
    </xsl:if>
  <!-- copy other content -->
    <xsl:copy-of select="node()"/>
  </xsl:copy>
</xsl:template>

<xsl:template name="xmlbase">
 <xsl:variable name="base"
     select="ancestor-or-self::*[position()!=last()][@xml:base][1]/@xml:base" />
  <xsl:if test="ancestor-or-self::*[position()!=last()][@xml:base][2]">
     <xsl:variable name="scheme"
         select="substring-before($base,':')"/>
     <xsl:variable name="schemeRest"
         select="translate(substring($scheme,2),
            'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-+.',
               '')" />
     <xsl:variable name="schemeFirst"
          select="translate(substring($scheme,1,1),
            'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz',
               '')" />
     <xsl:if test="not($schemeRest = '' and $schemeFirst = ''
                        and string-length($scheme) &gt; 0 )">
        <xsl:message terminate = "yes" >
<xsl:text>http://www.w3.org/2003/g/embeddedRDF
Nested relative xml:base attributes are not supported.</xsl:text>
        </xsl:message>
     </xsl:if>
  </xsl:if> 
  <xsl:attribute name="xml:base">
     <xsl:value-of select="$base" />
  </xsl:attribute>
</xsl:template>

<!-- don't pass text through. -->
<xsl:template match="text()|@*">
</xsl:template>

</xsl:transform>

<!-- debug code - for use within name="xmlbase"
<xsl:text>base = '</xsl:text>
<xsl:value-of select="$base"/>

<xsl:text>'
scheme = '</xsl:text>
<xsl:value-of select="$scheme"/>

<xsl:text>'
schemeRest = '</xsl:text>
<xsl:value-of select="$schemeRest"/>

<xsl:text>'
schemeFirst = '</xsl:text>
<xsl:value-of select="$schemeFirst"/>
<xsl:text>'
</xsl:text>
end debug code -->
