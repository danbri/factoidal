// The sample Shardborough store this package carries, so a fresh install
// answers a SPARQL query with no other download and no native binary.
//
// The store was packed by `l4block-shard-pack … ibk3` and activated by
// `l4block-shard-activate`. Nothing here decodes it; this module only
// resolves its path inside the installed package.
//
// CONTENT AND LICENCE. Five IPTC NewsCodes vocabularies, published by the
// IPTC under CC BY 4.0 and taken from danbri/skosdex third_party/skos:
// spamfstat, videoqualifier, subjectqualifier, videocodec and spct.
// 4,434 triples in 13 predicate blocks. See NOTICE.

import { fileUrlToPath, joinPath } from './store-host/paths.mjs'

/** The collection root of the bundled sample store: the directory holding
 * CURRENT. Pass it to `factoidal inspect` / `factoidal query`, or to
 * `openStore` from `@factoidal/core/store-host`. */
export function sampleStorePath () {
  const packageRoot = fileUrlToPath(new URL('.', import.meta.url).href)
  return joinPath(packageRoot, 'sample-store')
}

/** What the sample store holds, as recorded when it was packed. The engine
 * is the authority on every one of these numbers at run time; they are here
 * so a caller can print something before it opens the store. */
export const sampleStoreFacts = Object.freeze({
  triples: 4434,
  blocks: 13,
  layout: 'predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0',
  wireVersion: 6,
  source: 'IPTC NewsCodes (spamfstat, videoqualifier, subjectqualifier, videocodec, spct)',
  licence: 'CC BY 4.0',
  licenceUrl: 'https://creativecommons.org/licenses/by/4.0/',
  publisher: 'https://iptc.org/'
})

export default sampleStorePath
