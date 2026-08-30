---
title: "Bring a block: browser artifact inspection"
description: "Choose a Lean IBK1 block in the browser, inspect its versioned header, calculate its SHA-256 identity, and optionally cache the exact bytes in origin-private storage."
layout: hub.njk
series: docs-hub
series_order: 46
vocab: none
status: published
tests: tests/hub/post46_test.mjs
---

The block-engine MVP has a real canonical byte object now: an `IBK1` file is a
shared RDF-term dictionary plus ID rows, framed by CRC32C. The native Lean
query path can additionally require a trusted SHA-256 digest before decoding.
This page gives the browser the same *artifact* boundary: choose bytes, inspect
the untrusted header, calculate their identity, and optionally cache the exact
bytes locally. It does **not** claim browser-side `IBK1` query execution yet;
that needs a narrow Lean-WASM decode/query export.

```observable-js
blockFormat = ({
  magic: "IBK1",
  version: 1,
  headerBytes: 5,
  integrityNow: "CRC32C framing plus SHA-256 checked against a trusted digest",
  browserBoundary: "inspect, hash and optionally cache bytes; no block query ABI yet",
})
```

The ordinary file input works in current browsers. Where the File System Access
picker is available, the button uses it; the input is the portable fallback.
The optional cache is the origin-private file system (OPFS), not an upload: it
is private to this HTTPS site and can later support a worker-owned range-read
block cache. Delete the browser's site data to remove it.

```observable-js
blockArtifactPicker = {
  const root = html`<div>
    <p><strong>IBK1 artifact inspector.</strong> Select a local <code>.ibk1</code> file.</p>
    <p><button type="button">Choose block</button> <input type="file" accept=".ibk1,application/octet-stream" hidden></p>
    <label><input type="checkbox"> Cache a copy in this browser's OPFS after inspection</label>
    <pre aria-live="polite">No file selected.</pre>
  </div>`;
  const choose = root.querySelector("button");
  const input = root.querySelector('input[type="file"]');
  const cache = root.querySelector('input[type="checkbox"]');
  const output = root.querySelector("pre");
  const hex = (bytes) => Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
  async function inspect(file) {
    const bytes = new Uint8Array(await file.arrayBuffer());
    const magic = new TextDecoder().decode(bytes.slice(0, 4));
    const version = bytes[4];
    const digest = crypto?.subtle
      ? hex(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)))
      : "unavailable: Web Crypto is required for SHA-256";
    let cached = false;
    if (cache.checked && navigator.storage?.getDirectory) {
      const dir = await navigator.storage.getDirectory();
      const blocks = await dir.getDirectoryHandle("factoidal-blocks", { create: true });
      const handle = await blocks.getFileHandle(`${digest}.ibk1`, { create: true });
      const stream = await handle.createWritable();
      await stream.write(bytes);
      await stream.close();
      cached = true;
    }
    output.textContent = JSON.stringify({
      name: file.name, bytes: bytes.length, magic, version,
      recognizedIBK1: magic === blockFormat.magic && version === blockFormat.version,
      sha256: digest, cachedInOPFS: cached,
    }, null, 2);
  }
  input.addEventListener("change", () => input.files?.[0] && inspect(input.files[0]).catch((e) => output.textContent = `Inspection failed: ${e.message}`));
  choose.addEventListener("click", async () => {
    try {
      if (window.showOpenFilePicker) {
        const [handle] = await window.showOpenFilePicker({ types: [{ description: "Factoidal IBK block", accept: { "application/octet-stream": [".ibk1"] } }], multiple: false });
        await inspect(await handle.getFile());
      } else input.click();
    } catch (e) {
      if (e.name !== "AbortError") output.textContent = `Selection failed: ${e.message}`;
    }
  });
  return root;
}
```

`recognizedIBK1: true` means only that the five-byte public header agrees with
the current format. It is not acceptance: the Lean decoder still checks all
lengths, term/ID references and CRC32C, and assurance-grade use also compares
the displayed SHA-256 to a digest obtained from a trusted manifest. The next
profile is a signed snapshot manifest; a later multi-block profile may use a
Merkle root plus a block inclusion proof. Those strengthen what identity the
bytes are expected to have; they do not change this canonical block file.

For the full native path and its verified-digest command, see
[the segmented-IBK design note](../../../20260830-segmented-ibk-design/). The
smallest browser deployment target is deliberately the same shape: bytes +
trusted identity + narrow Lean block-core operation → result bytes.

`blockFormat` is pinned in
[`tests/hub/post46_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post46_test.mjs); the picker is deliberately
tested in the deployed browser, since file permission must result from a real
user gesture rather than a headless test bypass.
