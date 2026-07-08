// Schematron validation (entry ABI schematronValidate ->
// Schematron.Validate).
'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { schematronValidate, capabilities } = require('..');

const PENDING = 'pending npm-entry build';

const SCHEMA = `<schema xmlns="http://purl.oclc.org/dsdl/schematron">
  <pattern>
    <rule context="doc">
      <assert test="@ok">doc must carry an ok attribute</assert>
    </rule>
  </pattern>
</schema>`;

test('schematronValidate: failing assert produces a finding', async (t) => {
  const caps = await capabilities();
  if (!caps.schematron) { t.skip(PENDING); return; }
  const r = await schematronValidate(SCHEMA, '<doc/>');
  assert.ok(Array.isArray(r.findings));
  assert.ok(r.findings.length >= 1);
  const f = r.findings.find((x) => x.type === 'assert-fail');
  assert.ok(f, 'expected an assert-fail finding');
  assert.match(f.message, /ok attribute/);
});

test('schematronValidate: satisfied assert produces no assert-fail', async (t) => {
  const caps = await capabilities();
  if (!caps.schematron) { t.skip(PENDING); return; }
  const r = await schematronValidate(SCHEMA, '<doc ok="yes"/>');
  assert.equal(r.findings.filter((x) => x.type === 'assert-fail').length, 0);
});
