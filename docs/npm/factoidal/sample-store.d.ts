/** The collection root of the sample Shardborough store bundled with this
 * package: the directory that holds CURRENT. */
export declare function sampleStorePath (): string

export declare const sampleStoreFacts: Readonly<{
  triples: number
  blocks: number
  layout: string
  wireVersion: number
  source: string
  licence: string
  licenceUrl: string
  publisher: string
}>

export default sampleStorePath
