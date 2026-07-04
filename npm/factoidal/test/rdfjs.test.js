// Unit tests for the RDF/JS data model + N-Quads token converters.
// Pure JavaScript — no engine bundle involved.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  dataFactory: df,
  Dataset,
  termFromSrj,
  termToNQuads,
  quadToNQuads,
  nquadsToQuads,
  XSD_STRING,
  RDF_LANGSTRING,
} = require('../rdfjs.js');

test('DataFactory: namedNode identity and equals', () => {
  const a = df.namedNode('http://example.org/a');
  const b = df.namedNode('http://example.org/a');
  const c = df.namedNode('http://example.org/c');
  assert.equal(a.termType, 'NamedNode');
  assert.equal(a.value, 'http://example.org/a');
  assert.ok(a.equals(b));
  assert.ok(!a.equals(c));
  assert.ok(!a.equals(null));
  assert.ok(!a.equals(df.literal('http://example.org/a')));
});

test('DataFactory: blankNode fresh labels and equals', () => {
  const b1 = df.blankNode();
  const b2 = df.blankNode();
  assert.equal(b1.termType, 'BlankNode');
  assert.notEqual(b1.value, b2.value, 'auto labels are fresh');
  assert.ok(df.blankNode('x').equals(df.blankNode('x')));
  assert.ok(!df.blankNode('x').equals(df.blankNode('y')));
});

test('DataFactory: literal defaults, language, datatype', () => {
  const plain = df.literal('hi');
  assert.equal(plain.termType, 'Literal');
  assert.equal(plain.language, '');
  assert.equal(plain.datatype.value, XSD_STRING);

  const lang = df.literal('hallo', 'de');
  assert.equal(lang.language, 'de');
  assert.equal(lang.datatype.value, RDF_LANGSTRING);

  const typed = df.literal('30',
    df.namedNode('http://www.w3.org/2001/XMLSchema#integer'));
  assert.equal(typed.language, '');
  assert.equal(typed.datatype.value,
    'http://www.w3.org/2001/XMLSchema#integer');

  assert.ok(df.literal('hi').equals(df.literal('hi')));
  assert.ok(!df.literal('hi').equals(df.literal('hi', 'en')));
  assert.ok(!df.literal('hi').equals(typed));
});

test('DataFactory: defaultGraph and variable', () => {
  assert.ok(df.defaultGraph().equals(df.defaultGraph()));
  assert.equal(df.defaultGraph().value, '');
  const v = df.variable('x');
  assert.equal(v.termType, 'Variable');
  assert.ok(v.equals(df.variable('x')));
  assert.ok(!v.equals(df.variable('y')));
});

test('DataFactory: quad equals (incl. graph) and fromQuad', () => {
  const q1 = df.quad(
    df.namedNode('http://x/s'), df.namedNode('http://x/p'),
    df.literal('o'));
  const q2 = df.quad(
    df.namedNode('http://x/s'), df.namedNode('http://x/p'),
    df.literal('o'), df.defaultGraph());
  const q3 = df.quad(
    df.namedNode('http://x/s'), df.namedNode('http://x/p'),
    df.literal('o'), df.namedNode('http://x/g'));
  assert.equal(q1.termType, 'Quad');
  assert.ok(q1.equals(q2), 'missing graph means default graph');
  assert.ok(!q1.equals(q3));
  const copy = df.fromQuad(q3);
  assert.ok(copy.equals(q3));
  assert.notEqual(copy, q3);
});

test('termFromSrj covers uri/bnode/literal shapes', () => {
  assert.ok(termFromSrj({ type: 'uri', value: 'http://x/a' })
    .equals(df.namedNode('http://x/a')));
  assert.ok(termFromSrj({ type: 'bnode', value: 'b0' })
    .equals(df.blankNode('b0')));
  assert.ok(termFromSrj({ type: 'literal', value: 'hi' })
    .equals(df.literal('hi')));
  assert.ok(termFromSrj({ type: 'literal', value: 'hi', 'xml:lang': 'en' })
    .equals(df.literal('hi', 'en')));
  assert.ok(termFromSrj({
    type: 'typed-literal', value: '1',
    datatype: 'http://www.w3.org/2001/XMLSchema#integer',
  }).equals(df.literal('1',
    df.namedNode('http://www.w3.org/2001/XMLSchema#integer'))));
});

test('termToNQuads tokens match the F* serializer rules', () => {
  assert.equal(termToNQuads(df.namedNode('http://x/a')), '<http://x/a>');
  assert.equal(termToNQuads(df.blankNode('b0')), '_:b0');
  assert.equal(termToNQuads(df.literal('hi')), '"hi"');
  assert.equal(termToNQuads(df.literal('hi', 'en')), '"hi"@en');
  assert.equal(
    termToNQuads(df.literal('1',
      df.namedNode('http://www.w3.org/2001/XMLSchema#integer'))),
    '"1"^^<http://www.w3.org/2001/XMLSchema#integer>');
  // Escapes: exactly \\ \" \n \r \t (mirrors RDF.NQuads.Serialize).
  assert.equal(
    termToNQuads(df.literal('a"b\\c\nd\re\tf')),
    '"a\\"b\\\\c\\nd\\re\\tf"');
});

test('N-Quads round-trip: quads -> text -> quads', () => {
  const quads = [
    df.quad(df.namedNode('http://x/s'), df.namedNode('http://x/p'),
      df.literal('plain')),
    df.quad(df.namedNode('http://x/s'), df.namedNode('http://x/p'),
      df.literal('tagged', 'en-GB'), df.namedNode('http://x/g')),
    df.quad(df.blankNode('b1'), df.namedNode('http://x/p'),
      df.literal('esc "q" \\ \n end')),
    df.quad(df.namedNode('http://x/s'), df.namedNode('http://x/p'),
      df.blankNode('b2')),
  ];
  const text = quads.map(quadToNQuads).join('');
  const back = nquadsToQuads(text);
  assert.equal(back.length, quads.length);
  for (let i = 0; i < quads.length; i++) {
    assert.ok(back[i].equals(quads[i]), `quad ${i} round-trips`);
  }
});

test('nquadsToQuads handles UCHAR escapes and comments', () => {
  const text =
    '# comment line\n' +
    '<http://x/s> <http://x/p> "smile \\U0001F600 u \\u00E9" .\n' +
    '\n';
  const quads = nquadsToQuads(text);
  assert.equal(quads.length, 1);
  assert.equal(quads[0].object.value, 'smile \u{1F600} u é');
});

test('nquadsToQuads blankNodePrefix keeps documents apart', () => {
  const text = '_:b1 <http://x/p> "v" .\n';
  const [q1] = nquadsToQuads(text, { blankNodePrefix: 'docA_' });
  const [q2] = nquadsToQuads(text, { blankNodePrefix: 'docB_' });
  assert.equal(q1.subject.value, 'docA_b1');
  assert.ok(!q1.subject.equals(q2.subject));
});

test('Dataset: DatasetCore contract (size/add/delete/has/match/iterate)', () => {
  const s = df.namedNode('http://x/s');
  const p = df.namedNode('http://x/p');
  const g = df.namedNode('http://x/g');
  const q1 = df.quad(s, p, df.literal('1'));
  const q2 = df.quad(s, p, df.literal('2'), g);

  const ds = new Dataset([q1, q2, q1]); // duplicate ignored
  assert.equal(ds.size, 2);
  assert.ok(ds.has(q1));
  assert.ok(ds.has(df.quad(s, p, df.literal('1'))), 'has() is by value');

  assert.equal(ds.match(null, null, null, g).size, 1);
  assert.equal(ds.match(s).size, 2);
  assert.equal(ds.match(df.namedNode('http://x/other')).size, 0);

  assert.equal([...ds].length, 2);

  ds.delete(df.quad(s, p, df.literal('1')));
  assert.equal(ds.size, 1);
  assert.ok(!ds.has(q1));
});

test('Dataset: toNQuads / fromNQuads round-trip', () => {
  const ds = new Dataset([
    df.quad(df.namedNode('http://x/s'), df.namedNode('http://x/p'),
      df.literal('v', 'en'), df.namedNode('http://x/g')),
  ]);
  const back = Dataset.fromNQuads(ds.toNQuads());
  assert.equal(back.size, 1);
  assert.ok([...back][0].equals([...ds][0]));
});
