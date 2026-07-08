<?xml version="1.0" encoding="UTF-8"?>
<!-- First-matching-rule firing semantics. Source: ISO/IEC 19757-3:2016
     section 6.5 ("a node is processed by the first matching rule
     only"): within a pattern a node fires under the FIRST rule whose
     context selects it; later rules in the same pattern do NOT fire on
     that node. Both asserts use false() so every firing is observable;
     the two rules are distinguished by their @context. If first-match
     were violated, an <item> would additionally fire the wildcard rule. -->
<sch:schema xmlns:sch="http://purl.oclc.org/dsdl/schematron" queryBinding="xslt">
  <sch:pattern id="first-match">
    <sch:rule context="item">
      <sch:assert test="false()">Item rule fired.</sch:assert>
    </sch:rule>
    <sch:rule context="*">
      <sch:assert test="false()">Wildcard rule fired.</sch:assert>
    </sch:rule>
  </sch:pattern>
</sch:schema>
