<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE rdf:RDF [
    <!ENTITY owl "http://www.w3.org/2002/07/owl#" >
    <!ENTITY xsd "http://www.w3.org/2001/XMLSchema#" >
    <!ENTITY rdfs "http://www.w3.org/2000/01/rdf-schema#" >
    <!ENTITY rdf "http://www.w3.org/1999/02/22-rdf-syntax-ns#" >
    <!ENTITY cpr "http://purl.org/cpr/0.5#" >
]>
<xsl:stylesheet 
  xmlns:xsl  ="http://www.w3.org/1999/XSL/Transform" 
  version    ="1.0"
  xmlns:ex   ="http://example.com/"
  xmlns      ="urn:hl7-org:v3"
  xmlns:rim  ="urn:hl7-org:v3"
  xmlns:dc   ="http://purl.org/dc/elements/1.1/"
  xmlns:rdfs ="http://www.w3.org/2000/01/rdf-schema#" 
  xmlns:rdf  ="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
  xmlns:cpr  ="&cpr;"
  xmlns:edns ="http://www.loa-cnr.it/ontologies/ExtendedDnS.owl#"
  xmlns:skos ="http://www.w3.org/2004/02/skos/core#"
  xmlns:dol  ="http://www.loa-cnr.it/ontologies/DOLCE-Lite.owl#"
  xmlns:inf  ="http://www.loa-cnr.it/ontologies/ExtendedDnS.owl#"
  xmlns:galen="http://www.co-ode.org/ontologies/galen#"
  xmlns:obo  ="http://www.geneontology.org/owl#"
  xmlns:foaf ="http://xmlns.com/foaf/0.1/"
 >
  <xsl:output method="xml"/>
  <xsl:template match="text()"/>
  <xsl:template match="node()">
    <xsl:apply-templates select="*"/>
  </xsl:template>
  <xsl:template match="/">
    <rdf:RDF>
      <rdfs:Description rdf:about=''>
        <rdfs:isDefinedBy rdf:resource="http://purl.org/cpr"/>
      </rdfs:Description>      
      <xsl:apply-templates select="rim:ClinicalDocument"/>  
    </rdf:RDF>    
  </xsl:template>  
  <xsl:template match="rim:ClinicalDocument[rim:recordTarget/rim:patientRole/rim:patientPatient]">
    <cpr:patient-record>
      <xsl:apply-templates select="rim:effectiveTime"/>          
      <xsl:apply-templates select="rim:recordTarget/rim:patientRole/rim:patientPatient"/>      
      <xsl:for-each select="rim:author/rim:assignedAuthor/rim:assignedPerson">
        <foaf:maker>
          <foaf:Person>
            <xsl:apply-templates select="rim:name"/>          
          </foaf:Person>
        </foaf:maker>        
      </xsl:for-each>      
      <xsl:apply-templates select="rim:component"/>
    </cpr:patient-record>
  </xsl:template>
  <xsl:template match="rim:methodCode | rim:code[@displayName] | rim:value[@displayName]">
    <skos:prefLabel>
      <xsl:value-of select="@displayName"/>
    </skos:prefLabel>    
  </xsl:template>
  <xsl:template match="rim:translation[@value and @code]">
    <xsl:if test="@code">
      <ex:unit><xsl:value-of select="@code"/></ex:unit>
    </xsl:if>        
    <rdf:value><xsl:value-of select="@value"/></rdf:value>    
  </xsl:template>
  <xsl:template match="rim:value[@unit]">
    <xsl:if test="@unit">
      <ex:unit><xsl:value-of select="@unit"/></ex:unit>
    </xsl:if>        
    <rdf:value><xsl:value-of select="@value"/></rdf:value>    
  </xsl:template>  
  <xsl:template match="node()[rim:text]" mode="human-readable-label">
    <skos:prefLabel>
      <xsl:value-of select="rim:text"/>
    </skos:prefLabel>    
  </xsl:template>
  <xsl:template match="@value" mode="date-or-time">
    <xsl:choose>
      <xsl:when test="string-length(.) = 4">
        <xsl:value-of select="."/>
      </xsl:when>
      <xsl:when test="string-length(.) = 8">
        <xsl:value-of select="concat(substring(.,1,4),'-',substring(.,5,2),'-',substring(.,7,2))"/>
      </xsl:when>
      <xsl:otherwise>
        <!--xsl:attribute name="rdf:datatype" 
          namespace="http://www.w3.org/1999/02/22-rdf-syntax-ns#">http://www.w3.org/2001/XMLSchema#dateTime</xsl:attribute-->
        <xsl:value-of select="concat(substring(.,1,4),'-',substring(.,5,2),'-',substring(.,7,2),'T',substring(.,9,2),':',substring(.,11,2),':00')"/>        
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  <xsl:template match="rim:effectiveTime[not(rim:high)]">    
    <xsl:choose>
      <xsl:when test="@value">
        <xsl:element name="dc:date" namespace="http://purl.org/dc/elements/1.1/">          
          <xsl:apply-templates select="@value" mode="date-or-time"/>
        </xsl:element>
      </xsl:when>
      <xsl:when test="rim:period">
        <xsl:copy>
          <rim:period>
            <rdf:value><xsl:value-of select="rim:period/@value"/></rdf:value>
            <ex:unit><xsl:value-of select="rim:period/@unit"/></ex:unit>            
          </rim:period>
        </xsl:copy>
      </xsl:when>
      <xsl:otherwise>
        <!-- This can be described as an open ended interval using OWL time: http://www.w3.org/TR/owl-time -->
        <xsl:copy>
          <xsl:value-of select="rim:high/@value"/>
        </xsl:copy>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  <xsl:template match="rim:doseQuantity">
    <xsl:copy>
      <rdf:Description>
        <xsl:if test="rim:center/@unit">
          <ex:unit><xsl:value-of select="rim:center/@unit"/></ex:unit>
        </xsl:if>        
        <rdf:value><xsl:value-of select="rim:center/@value"/></rdf:value>
      </rdf:Description>
    </xsl:copy>
  </xsl:template>
  <xsl:template match="rim:SubstanceAdministration">
    <cpr:substance-administration>
      <xsl:apply-templates mode="human-readable-label" select="."/>
      <xsl:apply-templates select="rim:effectiveTime | rim:doseQuantity"/>
    </cpr:substance-administration>
  </xsl:template>
  <xsl:template match="rim:approachSiteCode">
    <xsl:copy>
        <xsl:if test="@displayName"><xsl:value-of select="@displayName"/></xsl:if>
    </xsl:copy>            
  </xsl:template>
  <xsl:template match="rim:routeCode">
    <xsl:copy>
      <xsl:choose>
        <xsl:when test="@code = 'PO'">Swallow, oral</xsl:when>
        <xsl:when test="@displayName"><xsl:value-of select="@displayName"/></xsl:when>
        <xsl:otherwise><xsl:value-of select="@code"/></xsl:otherwise>
      </xsl:choose>
    </xsl:copy>
  </xsl:template>
  <xsl:template match="rim:entryRelationship">
    <xsl:choose>
      <xsl:when test="@typeCode='COMP'">
        <obo:OBO_REL_has_improper_part>
          <xsl:apply-templates select="*"/> 
        </obo:OBO_REL_has_improper_part>        
      </xsl:when>
      <xsl:otherwise/>      
    </xsl:choose>
  </xsl:template>  
  <xsl:template match="rim:Procedure">
    <cpr:therapeutic-act>
      <xsl:apply-templates select="rim:code | rim:effectiveTime | rim:targetSiteCode"/>  
    </cpr:therapeutic-act>    
  </xsl:template>      
  <xsl:template match="rim:entry">
    <xsl:for-each select="rim:Procedure[rim:code] | rim:Observation | rim:SubstanceAdministration">
      <obo:OBO_REL_has_proper_part>
        <cpr:clinical-description>
          <cpr:description-of>
            <xsl:apply-templates select="."/>
          </cpr:description-of>
        </cpr:clinical-description>      
      </obo:OBO_REL_has_proper_part>      
    </xsl:for-each>    
  </xsl:template>
  <xsl:template match="rim:Observation">
    <xsl:param name="medical-history-taking" select="false"/>
    <xsl:choose>
      <xsl:when test="@negationInd = 'true' or @moodCode='INT'">
      </xsl:when>
      <xsl:otherwise>
        <rdf:Description>
          <xsl:choose>
            <xsl:when test="$medical-history-taking">
              <rdf:type rdf:resource="&cpr;medical-history-screening-act"/>
              <inf:realizes>
                <xsl:choose>
                  <xsl:when test="../../../rim:Observation[rim:value]">
                    <!-- A manefestation / interpetation of a phenomenon? (cpr:medical-sign) -->
                    <cpr:medical-sign>
                      <xsl:apply-templates select="rim:value"/>
                      <cpr:interpretant-of>
                        <cpr:symptom>
                          <xsl:apply-templates select="../../../rim:Observation/rim:value"/>
                        </cpr:symptom>
                      </cpr:interpretant-of>
                    </cpr:medical-sign>                      
                  </xsl:when>
                  <xsl:otherwise>
                  </xsl:otherwise>
                </xsl:choose>
              </inf:realizes>                  
            </xsl:when>
            <xsl:when test="../../rim:entryRelationship[@typeCode='COMP']">
              <!-- A measurement.  GALEN models the notion of a measurement well  -->
              <rdf:type rdf:resource="&cpr;clinical-examination"/>
              <inf:realizes>
                <galen:AbsoluteMeasurement>
                  <xsl:apply-templates select="rim:code | rim:value"/>
                </galen:AbsoluteMeasurement>
              </inf:realizes>
            </xsl:when>            
            <xsl:otherwise>
              <rdf:type rdf:resource="&cpr;screening-act"/>
            </xsl:otherwise>
          </xsl:choose> 
          <xsl:if test="not(rim:code[@code = '84100007' and @codeSystemName = 'SNOMED CT'])">
            <xsl:apply-templates select="rim:effectiveTime"/>  
          </xsl:if>
          <xsl:choose>
            <xsl:when test="rim:methodCode">
              <xsl:apply-templates select="rim:methodCode"/>
            </xsl:when>
            <xsl:when test="not(../../rim:entryRelationship[@typeCode='COMP'])">
              <xsl:apply-templates select="rim:code"/>
            </xsl:when>
          </xsl:choose>
          <xsl:apply-templates select="rim:entryRelationship | rim:targetSiteCode | rim:effectiveTime"/>            
          <xsl:choose>
            <xsl:when test="@classCode = 'COND'">
              <!--                
                From: http://www.hl7.org/library/data-model/RIM/C30202/ActClass.htm#C-0-D11527-cpt
                An observable finding or state that persists over time and tends to 
                require intervention or management, and, therefore, distinguished from an 
                Observation made at a point in time; may exist before an Observation of 
                the Condition is made or after interventions to manage the Condition are undertaken.
                Examples: equipment repair status, device recall status, a health risk, 
                a financial risk, public health risk, pregnancy, health maintenance, chronic illness 
              -->
              <inf:realizes>
                <cpr:diagnosis>
                  <xsl:apply-templates select="rim:value"/>
                  <xsl:apply-templates select="rim:targetSiteCode"/>
                </cpr:diagnosis>
              </inf:realizes>                
            </xsl:when>
            <xsl:when test="rim:code[@code = '84100007' and @codeSystemName = 'SNOMED CT']">
              <xsl:choose>
                <xsl:when test="rim:entryRelationship[@typeCode='MFST'] and rim:value and not($medical-history-taking)">
                  <!--                
                    History taking act (cpr:medical-history-screening-act) - a manefestation of a problem determined from a case history
                  -->
                  <obo:OBO_REL_has_improper_part>
                    <xsl:apply-templates select="rim:entryRelationship[@typeCode='MFST']/rim:Observation">
                      <xsl:with-param name="medical-history-taking" select="true()"/>
                    </xsl:apply-templates>
                  </obo:OBO_REL_has_improper_part>                  
                </xsl:when>
                <xsl:when test="not($medical-history-taking)">
                  <obo:OBO_REL_has_improper_part>
                    <!-- Generic history taking act - Be sure to associate the date with the findings -->
                    <cpr:medical-history-screening-act>
                      <xsl:apply-templates select="rim:code"/>
                      <xsl:for-each select="rim:value[@displayName]">
                        <inf:realizes>
                          <rdf:Description>
                            <xsl:apply-templates select="../rim:effectiveTime"/>
                            <xsl:apply-templates select="."/>
                          </rdf:Description>
                        </inf:realizes>
                      </xsl:for-each>                      
                    </cpr:medical-history-screening-act>
                  </obo:OBO_REL_has_improper_part>                  
                </xsl:when>
              </xsl:choose>
            </xsl:when>    
            <xsl:when test="rim:code[@code = '282290005' and @codeSystemName = 'SNOMED CT']">
              <!--                
                Image interpretation - use foaf:Image to describe the image
              -->
              <inf:realizes>
                <cpr:medical-sign>
                  <xsl:apply-templates select="rim:value"/>
                  <cpr:interpretant-of>
                    <foaf:Image>
                      <xsl:apply-templates select="//rim:ExternalObservation[@classCode='DGIMG']/rim:code"/>  
                    </foaf:Image>
                  </cpr:interpretant-of>
                  <xsl:apply-templates select="rim:targetSiteCode"/>
                </cpr:medical-sign>
              </inf:realizes>                
            </xsl:when>    
            <xsl:when test="rim:value and not(../../rim:entryRelationship[@typeCode='COMP'])">
              <inf:realizes>
                <rdf:Description>
                  <xsl:apply-templates select="rim:value"/>                  
                </rdf:Description>
              </inf:realizes>
              <xsl:if test="rim:value/rim:translation[@value and @code]">
                <inf:realizes>
                  <rdf:Description>
                    <xsl:apply-templates select="rim:value/rim:translation"/>                  
                  </rdf:Description>
                </inf:realizes>                
              </xsl:if>                
            </xsl:when>
          </xsl:choose>          
        </rdf:Description>
      </xsl:otherwise>      
    </xsl:choose>    
  </xsl:template>
  <xsl:template match="rim:reference[@typeCode='SPRT']/rim:ExternalObservation[@classCode='DGIMG']">
    <xsl:element name="foaf:Image">
      <!--xsl:if test="rim:id">
        <xsl:attribute name="rdf:about" namespace="http://www.w3.org/1999/02/22-rdf-syntax-ns#">urn:tag:<xsl:value-of select="rim:id/@root"/></xsl:attribute>
      </xsl:if-->
      <xsl:apply-templates select="rim:code"/>
    </xsl:element> 
  </xsl:template>
  <xsl:template match="rim:targetSiteCode[@displayName]">
    <galen:hasSpecificLocation>
        <xsl:value-of select="@displayName"/>
    </galen:hasSpecificLocation>
  </xsl:template>
  <xsl:template match="rim:name/rim:family">
    <foaf:family_name><xsl:value-of select="."/></foaf:family_name>
  </xsl:template>
  <xsl:template match="rim:name/rim:given">
    <foaf:firstName><xsl:value-of select="."/></foaf:firstName>
  </xsl:template>
  <xsl:template match="rim:patientPatient">
    <edns:about>
      <galen:Patient>
        <xsl:apply-templates select="rim:name"/>
      </galen:Patient>
    </edns:about>
  </xsl:template>
  <xsl:template match="rim:*">
    <xsl:apply-templates select="*"/> 
  </xsl:template>  
</xsl:stylesheet>