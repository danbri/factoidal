// XSLT 1.0 transform engine (entry ABI xsltTransform -> XSLT.Transform).
'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { xsltTransform, capabilities } = require('..');

const PENDING = 'pending npm-entry build';

const STYLESHEET = `<xsl:stylesheet version="1.0"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <xsl:template match="/">
    <greeting><xsl:value-of select="/doc/name"/></greeting>
  </xsl:template>
</xsl:stylesheet>`;

const SOURCE = '<doc><name>World</name></doc>';

test('xsltTransform: value-of into a literal result element', async (t) => {
  const caps = await capabilities();
  if (!caps.xslt) { t.skip(PENDING); return; }
  const out = await xsltTransform(STYLESHEET, SOURCE);
  assert.equal(typeof out, 'string');
  assert.match(out, /greeting/);
  assert.match(out, /World/);
});

test('xsltTransform: identity-style xsl:copy-of', async (t) => {
  const caps = await capabilities();
  if (!caps.xslt) { t.skip(PENDING); return; }
  const ss = `<xsl:stylesheet version="1.0"
      xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
    <xsl:template match="/"><xsl:copy-of select="/doc/name"/></xsl:template>
  </xsl:stylesheet>`;
  const out = await xsltTransform(ss, SOURCE);
  assert.match(out, /<name>World<\/name>/);
});

test('xsltTransform: rejects malformed XML', async (t) => {
  const caps = await capabilities();
  if (!caps.xslt) { t.skip(PENDING); return; }
  await assert.rejects(() => xsltTransform('<not well formed', SOURCE));
});
