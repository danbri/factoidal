// Pins docs/web/hub/28-verified-math-rendered.md.
//
// Like post27, the cells call the typed `fn` methods now
// (mathmlEval/toanSummation/matrixDeterminant) rather than reaching
// for the raw factoidalNpmEntry ABI, and reference each other
// ObservableHQ-style (`formatMathValue`, then `mathmlDemo`, then
// `summationMathml`, then the Content->Presentation cell that reads
// it) -- exercised via runReactivePost(). `fn` here is the real
// npm/factoidal typed API. `html` has no DOM in Node, so this file
// supplies a minimal tagged-template stub that mirrors
// @observablehq/stdlib's template() for plain-string interpolations
// (see third_party/observable/dist/stdlib.esm.js's `template()`: a
// non-Node/non-Array interpolated value is concatenated into the source
// string as-is, unescaped, before the browser parses it as markup) --
// so the test can assert on the exact markup the real `html` would also
// receive, without needing a DOM to build it.
//
// The sigmoid section (issue #289) adds seven cells at the end:
// sigmoidFormulaMathml/sigmoidFormulaDisplay (engine-serialized
// MathML for the formula), sigmoidParams/sigmoidSamples (the F*-
// computed points, Math.Sigmoid.sigmoid_points via
// fn.sigmoidPoints), sigmoidPlot/sigmoidPlotDisplay (a pure SVG
// string built from those points -- pixel placement only, no exp
// anywhere in this file or the cell), and sigmoidInteractive (a
// self-contained DOM cell with three range sliders wired to
// fn.sigmoidPoints, following post21's "minimal document stub, assert
// it runs to completion and the shape it built" pattern for the parts
// Node has no layout engine to render).

import {
  NPM_FACTOIDAL_INDEX,
  extractObservableCells,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const POST_FILE = '28-verified-math-rendered.md';
const fn = (await import(NPM_FACTOIDAL_INDEX)).default;

// Node-side stand-in for @observablehq/stdlib's `html` tagged template.
// Only string interpolations appear in this post's cells (no DOM Node
// or Array parts), so raw string concatenation matches template()'s
// real behavior for that case exactly -- see the file banner above.
function html(strings, ...values) {
  let out = strings[0];
  for (let i = 0; i < values.length; i++) out += String(values[i]) + strings[i + 1];
  return out;
}

const cells = extractObservableCells(POST_FILE);

test('post28: post ships fourteen live cells', () => {
  assert.equal(cells.length, 14, `expected 14 live cells, found ${cells.length}`);
});

test('post28: dependency inference names the cells in order', () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  // The one anonymous cell (`pretty(mathmlDemo)`) gets the runtime's
  // fallback name `cell0` -- the anon counter increments only over
  // anonymous cells, not the absolute cell index. See
  // tests/hub/_helpers.mjs's runReactivePost().
  assert.deepEqual(post.names, [
    'formatMathValue',
    'mathmlDemo',
    'cell0',
    'summationMathml',
    'summationPresentation',
    'determinantPlain',
    'determinantExact',
    'sigmoidFormulaMathml',
    'sigmoidFormulaDisplay',
    'sigmoidParams',
    'sigmoidSamples',
    'sigmoidPlot',
    'sigmoidPlotDisplay',
    'sigmoidInteractive',
  ]);
});

test('post28: mathmlDemo evaluates 2+3 to an exact rational and 1/0 to undef', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const demo = await post.value('mathmlDemo');
  assert.deepEqual(demo, [
    { contentMathml: '<apply><plus/><cn>2</cn><cn>3</cn></apply>', value: '5/1' },
    { contentMathml: '<apply><divide/><cn>1</cn><cn>0</cn></apply>', value: 'undef (division-by-zero)' },
  ]);
});

test('post28: the pretty(mathmlDemo) cell renders a two-row table', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const table = await post.value('cell0');
  assert.equal(table.kind, 'table');
  assert.equal(table.rows.length, 2);
});

test('post28: summationMathml carries the verified Content MathML for the sum', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const mathml = await post.value('summationMathml');
  assert.equal(
    mathml,
    '<math xmlns="http://www.w3.org/1998/Math/MathML">' +
      '<apply><plus/>' +
      '<apply><times/><cn type="integer">10</cn><ci>y</ci></apply>' +
      '<apply><times/><cn type="integer">4</cn><ci>x</ci></apply>' +
      '</apply></math>'
  );
});

test('post28: summationPresentation converts to Presentation MathML for display', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const presentation = await post.value('summationPresentation');
  assert.equal(
    presentation,
    '<math display="block">' +
      '<mrow>' +
      '<mrow><mn>10</mn><mo>&#8290;</mo><mi>y</mi></mrow>' +
      '<mo>+</mo>' +
      '<mrow><mn>4</mn><mo>&#8290;</mo><mi>x</mi></mrow>' +
      '</mrow>' +
      '</math>'
  );
});

test('post28: determinantPlain is -2, determinantExact is the exact fraction 1/4', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  assert.equal(await post.value('determinantPlain'), '-2');
  assert.equal(await post.value('determinantExact'), '1/4');
});

test('post28: sigmoidFormulaMathml is the engine-serialized Presentation MathML for L/(1+exp(-k*(x-x0)))', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const mathml = await post.value('sigmoidFormulaMathml');
  // Cross-checked directly against the real ABI (not re-derived here):
  // this IS fn.sigmoidFormulaMathml()'s raw output, proving the cell
  // calls straight through with no hand-written MathML in between.
  const direct = await fn.sigmoidFormulaMathml();
  assert.equal(mathml, direct);
  assert.match(mathml, /^<math xmlns="http:\/\/www\.w3\.org\/1998\/Math\/MathML">/);
  assert.match(mathml, /<mfrac>/); // L / (...) renders as a fraction box
  assert.match(mathml, /<msup><mi>e<\/mi>/); // exp(...) renders as e^(...)
});

test('post28: sigmoidFormulaDisplay wraps the raw MathML for the browser unchanged', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const mathml = await post.value('sigmoidFormulaMathml');
  const display = await post.value('sigmoidFormulaDisplay');
  assert.equal(display, mathml);
});

test('post28: sigmoidParams carries the default slider values', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const params = await post.value('sigmoidParams');
  assert.deepEqual(params, { k: '1', x0: '0', l: '1', xmin: '-6', xmax: '6', n: 24 });
});

test('post28: sigmoidSamples has 25 F*-computed points; the midpoint is exact', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const samples = await post.value('sigmoidSamples');
  assert.equal(samples.length, 25, 'n=24 -> n+1=25 samples');
  // Cross-checked directly against the real ABI.
  const direct = await fn.sigmoidPoints({ k: '1', x0: '0', l: '1', xmin: '-6', xmax: '6', n: 24 });
  assert.deepEqual(samples, direct);
  // x = x0 = 0 is sample index 12 (step = (6 - -6)/24 = 0.5); at that
  // point k*(x-x0) = 0 exactly, so exp_approx(0) = 1 exactly (every
  // Taylor term past the constant 1 vanishes, repeated squaring of an
  // exact 1 stays 1), giving y = L / (1 + 1) = 0.5 exactly -- no
  // rounding anywhere in this one value, so it is asserted exactly.
  assert.equal(samples[12].x.decimal, '0.000000000');
  assert.equal(samples[12].y.decimal, '0.500000000');
  // Monotonic: x strictly increasing, y strictly increasing (the
  // logistic sigmoid is monotonic for k > 0), and bounded in (0, L).
  for (let i = 1; i < samples.length; i++) {
    assert.ok(Number(samples[i].x.decimal) > Number(samples[i - 1].x.decimal));
    assert.ok(Number(samples[i].y.decimal) > Number(samples[i - 1].y.decimal));
  }
  assert.ok(Number(samples[0].y.decimal) > 0 && Number(samples[0].y.decimal) < 0.5);
  assert.ok(Number(samples[24].y.decimal) > 0.5 && Number(samples[24].y.decimal) < 1);
});

// Same pixel-placement arithmetic as the cell's own inline copy
// (post21's pattern: duplicated here, tested directly with plain
// assertions, since cell bodies can't `import`).
function expectedPixelCoords(samples, xmin, xmax, l) {
  const width = 480, height = 220, pad = 24;
  return samples.map((p) => {
    const px = Number(p.x.decimal);
    const py = Number(p.y.decimal);
    const xFrac = (px - xmin) / (xmax - xmin);
    const yFrac = l > 0 ? py / l : 0;
    const sx = pad + xFrac * (width - 2 * pad);
    const sy = height - pad - yFrac * (height - 2 * pad);
    return sx.toFixed(2) + ',' + sy.toFixed(2);
  });
}

test('post28: sigmoidPlot is an SVG polyline over the 25 F*-computed points', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const samples = await post.value('sigmoidSamples');
  const plot = await post.value('sigmoidPlot');
  assert.match(plot, /^<svg viewBox="0 0 480 220" width="480" height="220">/);
  const expectedCoords = expectedPixelCoords(samples, -6, 6, 1).join(' ');
  assert.equal(
    plot,
    '<svg viewBox="0 0 480 220" width="480" height="220">' +
      '<polyline points="' + expectedCoords + '" fill="none" stroke="currentColor" stroke-width="2"></polyline>' +
      '</svg>'
  );
  // 25 points -> 25 space-separated coordinate pairs.
  assert.equal(expectedCoords.split(' ').length, 25);
});

test('post28: sigmoidPlotDisplay wraps the raw SVG for the browser unchanged', async () => {
  const post = runReactivePost(cells, { fn, pretty, html });
  const plot = await post.value('sigmoidPlot');
  const display = await post.value('sigmoidPlotDisplay');
  assert.equal(display, plot);
});

// The interactive cell calls `document.createElement`/`appendChild`/
// `setAttribute`/`addEventListener` (ambient globals in the browser,
// per reactive-cells.mjs's own header comment). Node has no `document`,
// so this test supplies the minimal element stub the cell's own DOM
// usage needs (post21's pattern), then removes it.
function makeStubElement() {
  return {
    className: '',
    textContent: '',
    type: '', min: '', max: '', step: '', value: '',
    innerHTML: '',
    children: [],
    appendChild(child) { this.children.push(child); return child; },
    setAttribute() {},
    addEventListener() {},
  };
}

test('post28: sigmoidInteractive builds three sliders and an SVG, and renders without throwing', async () => {
  const previousDocument = globalThis.document;
  globalThis.document = { createElement: () => makeStubElement() };
  try {
    const post = runReactivePost(cells, { fn, pretty, html });
    const result = await post.value('sigmoidInteractive');
    assert.ok(result && typeof result === 'object', 'sigmoidInteractive should return the container element');
    assert.equal(result.className, 'hub-sigmoid-demo');
    // Three <label> wrappers (k, x0, L) plus the <svg> = 4 children.
    assert.equal(result.children.length, 4);
    const svg = result.children[3];
    assert.match(svg.innerHTML, /^<polyline points="/);
    const pointsAttr = /points="([^"]*)"/.exec(svg.innerHTML)[1];
    assert.equal(pointsAttr.split(' ').length, 25, 'default n=24 -> 25 rendered points');
  } finally {
    if (previousDocument === undefined) delete globalThis.document; else globalThis.document = previousDocument;
  }
});

