# Life-sciences IBK3 blocks for the Shardborough hub notebook

Twelve current-format `IBK3` predicate blocks packed by the Lean publisher
from the three Wikidata life-sciences extracts already published beside the
hub (`docs/fstar-extracted/lifesci/*.ttl`, identical bytes to
`examples/wikidata/subsets/lifesci-kgx/data/`). 43,103 triples in total;
2.5 MB of blocks. The notebook fetches only the blocks a query names.

```sh
formal/lean4/.lake/build/bin/l4block-shard-pack \
  examples/wikidata/subsets/lifesci-kgx/data/<member>.ttl OUTPUT-DIRECTORY ibk3
```

Files are renamed from the publisher's `predicate-N.ibk3` to the Wikidata
property they hold; bytes are unchanged. All objects in these extracts are
IRIs (no blank nodes, no literals).

Source documents (SHA-256 of the Turtle; used as each member's blank-node
import scope):

| Member | Source | Triples | SHA-256 |
|---|---|---:|---|
| chromosome | `chromosome.ttl` | 9,227 | `58fc83f472a86526c5ce442bfefe83d25364f20d51f4c06158f9881a0f03b42f` |
| sequence_variant | `sequence_variant.ttl` | 6,455 | `f5b5a08b0b30df1ed4e42f1db4417cbaac239a878e8c26a419cdb2dfa9c04fcb` |
| disease | `disease.ttl` | 27,421 | `b8f06644f0fce1cb0577c38fda2e4f6f1e65d7fae6aee900a9065a9bb8048b42` |

Blocks (predicate IRIs are `http://www.wikidata.org/prop/direct/<P>`):

| File | Property | Rows | Bytes | SHA-256 |
|---|---|---:|---:|---|
| `chromosome/P31.ibk3` | P31 instance of | 9,227 | 563,282 | `01484578d6b9696d0298a20898b8a2bf209f7477cc938002c35aa1c55611068a` |
| `sequence_variant/P31.ibk3` | P31 instance of | 1,800 | 110,085 | `a7722b5893193e59cc3429b99a3e1550b86145c6d680b2104a0bb34bef7bb7af` |
| `sequence_variant/P361.ibk3` | P361 part of | 719 | 35,535 | `e726e04b9a9d15f5097ac2c4befe55baddbb9699635c3ceba6136c3c60fe9dda` |
| `sequence_variant/P3354.ibk3` | P3354 positive therapeutic predictor | 877 | 46,502 | `b1c22afab1539748f75b7d70c5d68dd7c0692f8804d0c330f484b823821fbb76` |
| `sequence_variant/P3433.ibk3` | P3433 biological variant of | 1,702 | 118,769 | `0c1bec972f134d617a98a7bb6275e0e421b2b4a930df9cd6d3c0cf9f34dd59c1` |
| `sequence_variant/P1057.ibk3` | P1057 chromosome | 1,357 | 82,884 | `24c8a5b2faf5d56f41edcb8707e17c9d26bf4cc903f8618efbdb3bcd29130e15` |
| `disease/P31.ibk3` | P31 instance of | 13,283 | 806,110 | `a28630ba7f87c4e579e5be4bf6a9165285895921cbf7fa2c71d8613e17d214b5` |
| `disease/P780.ibk3` | P780 symptoms and signs | 3,416 | 127,726 | `2777b3af2b0f2cbba8057795956f02ad33183ab07aae2054ad28c7b7f0b6ebd6` |
| `disease/P828.ibk3` | P828 has cause | 1,842 | 150,632 | `79e09106dd4633f2fa2d009b26d5a801b52bc871bf48a0996880df58f45c5173` |
| `disease/P2293.ibk3` | P2293 genetic association | 5,586 | 424,997 | `811ce421fe4973bae40534dbc73792e9c6a6a4d8820de3ecfd9947eb8bf41c3f` |
| `disease/P927.ibk3` | P927 anatomical location | 542 | 39,028 | `f145420c498cc83c2b207e942e39ab3143e2acf34c224fd18f010dbebc497152` |
| `disease/P2176.ibk3` | P2176 drug or therapy used for treatment | 2,752 | 115,718 | `bfafa617d56ca49fa38284ff5dd61b1e2356b5e85f3071aa379749c660bb5579` |

Row counts were measured by the Lean WASM `scanIBK3Predicate` operation on
each block; source triple counts by `tools/corpus-profile.sh`. These are
primary block bytes only: the notebook does not claim SBM activation, Merkle
inclusion, sidecar range reads or delta replay, which the native persistent
harness exercises.
