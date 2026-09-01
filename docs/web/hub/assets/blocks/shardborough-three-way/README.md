# Three-predicate IBK3 browser fixture

These three current-format IBK3 artifacts are generated from
`formal/lean4/Harness/TestData/three-way-subject.ttl` (13 RDF triples,
SHA-256 `8d07b81bf71e0b4c548b5faae50c4231b41bd99ecedc00a5e46817413e815346`)
by the Lean publisher:

```sh
formal/lean4/.lake/build/bin/l4block-shard-pack \
  formal/lean4/Harness/TestData/three-way-subject.ttl OUTPUT-DIRECTORY ibk3
```

| File | Predicate | Rows | Bytes | SHA-256 |
|---|---|---:|---:|---|
| `type.ibk3` | `http://example.org/type` | 4 | 310 | `7797b38983808f0dded40813672b79f4b8d9f07956ff203d9becab9df8e40a68` |
| `name.ibk3` | `http://example.org/name` | 5 | 536 | `6a26193245b2ede29b80a5dcc8530da9f3415f7f96188948d27438142bbd7ede` |
| `member.ibk3` | `http://example.org/member` | 4 | 342 | `78540ea53aab57c78d4b0f025d6fbbe307e40d16fbd822331ec1cc0d6c2e542d` |

The Hub demo supplies each complete artifact to the Lean/WASM
`scanIBK3Predicate` operation with one blank-node scope shared by all blocks
from this source document. These are primary block bytes only. The browser demo
does not claim SBM activation, Merkle inclusion, sidecar range reads, or delta
replay; those are exercised by the native persistent harness.
