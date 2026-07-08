<?xml version="1.0" encoding="UTF-8"?>
<!-- Conditional co-occurrence constraint ("if A then B required").
     Source: ISO/IEC 19757-3:2016 Annex examples and Rick Jelliffe's
     Schematron tutorial (schematron.com) — the archetypal
     "not(condition) or requirement" assertion idiom. -->
<sch:schema xmlns:sch="http://purl.oclc.org/dsdl/schematron" queryBinding="xslt">
  <sch:pattern id="payment-cooccurrence">
    <sch:rule context="payment">
      <sch:assert test="not(@type = 'card') or card-number">Card payments must include a card-number.</sch:assert>
    </sch:rule>
  </sch:pattern>
</sch:schema>
