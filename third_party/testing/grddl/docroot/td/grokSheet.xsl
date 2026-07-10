<?xml version="1.0" encoding="utf-8"?>
<!-- $Id: grokSheet.xsl,v 1.1 2006/11/01 06:42:51 connolly Exp $ -->
<xsl:stylesheet
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:gmr="http://www.gnumeric.org/v10.dtd" 
  xmlns:r="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
  xmlns:s="http://www.w3.org/2000/01/rdf-schema#"
  xmlns:dc="http://purl.org/dc/elements/1.1/"
  xmlns:ts="http://www.w3.org/2003/08dc-ymx/trip-rules#"
  version="1.0">

  <xsl:output method="xml" indent="yes"/>

  <xsl:template match="gmr:Cells">
    <xsl:if test="gmr:Cell">
    <r:RDF>
      <r:Description r:about=''>
        <xsl:for-each select='gmr:Cell[@Row = "0"]'>
          <dc:title><xsl:value-of select='.'/></dc:title>
        </xsl:for-each>
      </r:Description>

      <xsl:call-template name="grokTable">
        <xsl:with-param name="headingRow" select="1"/>
        <xsl:with-param name="lastRow" select="6"/>
      </xsl:call-template>
    </r:RDF>
    </xsl:if>
  </xsl:template>

  <xsl:template name="grokTable">
    <xsl:param name="headingRow"/>
    <xsl:param name="lastRow"/>


    <xsl:call-template name="grokCellHeadings">
      <xsl:with-param name="headingRow" select='$headingRow'/>
      <xsl:with-param name="thisCol" select='0'/>
      <xsl:with-param name="lastCol" select='12'/> <!-- GLOBAL -->
    </xsl:call-template>

    <xsl:call-template name="grokRows">
      <xsl:with-param name="headingRow" select='$headingRow'/>
      <xsl:with-param name="thisRow" select='$headingRow + 1'/>
      <xsl:with-param name="lastRow" select='$lastRow'/>
    </xsl:call-template>
  </xsl:template>
  
  <xsl:template name="grokRows">
    <xsl:param name="headingRow"/>
    <xsl:param name="thisRow"/>
    <xsl:param name="lastRow"/>

    <xsl:if test='$thisRow &lt;= $lastRow'>
      <r:Description>
        <xsl:call-template name="grokCells">
          <xsl:with-param name="headingRow" select='$headingRow'/>
          <xsl:with-param name="thisRow" select='$thisRow'/>
          <xsl:with-param name="thisCol" select='0'/>
          <xsl:with-param name="lastCol" select='12'/> <!-- GLOBAL -->
        </xsl:call-template>
      </r:Description>

      <xsl:call-template name="grokRows">
        <xsl:with-param name="headingRow" select='$headingRow'/>
        <xsl:with-param name="thisRow" select='$thisRow + 1'/>
        <xsl:with-param name="lastRow" select='$lastRow'/>
      </xsl:call-template>

    </xsl:if>
  </xsl:template>

  <xsl:template name="grokCells">
    <xsl:param name="headingRow"/>
    <xsl:param name="thisRow"/>
    <xsl:param name="thisCol"/>
    <xsl:param name="lastCol"/>

    <xsl:if test='$thisCol &lt;= $lastCol'>
      
      <xsl:variable name="thisCell"
        select='gmr:Cell[@Col = $thisCol and @Row = $thisRow]'/>
      <xsl:variable name="headingCell"
        select='gmr:Cell[@Col = $thisCol and @Row = $headingRow]'/>
      <xsl:if test="$thisCell">
        
        <xsl:element name='{concat("dc:", string($headingCell))}'
          namespace='http://purl.org/dc/elements/1.1/'>
          <xsl:value-of select='$thisCell'/>
        </xsl:element>
      </xsl:if>
      <xsl:call-template name="grokCells">
        <xsl:with-param name="headingRow" select='$headingRow'/>
        <xsl:with-param name="thisRow" select='$thisRow'/>
        <xsl:with-param name="thisCol" select='$thisCol + 1'/>
        <xsl:with-param name="lastCol" select='$lastCol'/>
      </xsl:call-template>

    </xsl:if>
  </xsl:template>

  <xsl:template name="grokCellHeadings">
    <xsl:param name="headingRow"/>
    <xsl:param name="thisCol"/>
    <xsl:param name="lastCol"/>
    
    <xsl:if test='$thisCol &lt;= $lastCol'>
      
      <xsl:variable name="thisCell"
        select='gmr:Cell[@Col = $thisCol and @Row = $headingRow]'/>
      <xsl:if test="$thisCell">
        <r:Property r:about='{concat("http://purl.org/dc/elements/1.1/", string($thisCell))}'>
          <s:label><xsl:value-of select='$thisCell'/></s:label>
        </r:Property>
      </xsl:if>

      <xsl:call-template name="grokCellHeadings">
        <xsl:with-param name="headingRow" select='$headingRow'/>
        <xsl:with-param name="thisCol" select='$thisCol + 1'/>
        <xsl:with-param name="lastCol" select='$lastCol'/>
      </xsl:call-template>
      
    </xsl:if>
  </xsl:template>


  <!-- don't pass text thru -->
  <xsl:template match="text()|@*">
  </xsl:template>

</xsl:stylesheet>
