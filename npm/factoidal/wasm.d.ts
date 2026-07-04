// TypeScript declarations for 'factoidal/wasm' — same API as the main
// entry, backed by the wasm_of_ocaml engine bundle (Node >= 22).

import {
  DataFactory,
  DataInput,
  DataFormat,
  Dataset,
  ParseOptions,
  QueryOptions,
  SerializeOptions,
  Bindings,
} from './index';

export {
  Dataset,
  DataFactory,
  DataInput,
  DataFormat,
  ParseOptions,
  QueryOptions,
  SerializeOptions,
  Bindings,
};

export function parse(text: string, options?: ParseOptions): Promise<Dataset>;
export function query(
  data: DataInput,
  sparql: string,
  options?: QueryOptions
): Promise<Bindings[] | boolean | Dataset>;
export function update(
  data: DataInput,
  updateText: string,
  options?: { format?: DataFormat }
): Promise<Dataset>;
export function serialize(
  data: DataInput,
  options?: SerializeOptions
): Promise<string>;
export function canonicalize(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<string>;
export function capabilities(): Promise<{
  entry: boolean;
  construct: boolean;
  update: boolean;
  canonicalize: boolean;
}>;
export const dataFactory: DataFactory;
/** True if the wasm loader + .wasm asset are present. */
export function wasmAvailable(): boolean;
export const version: string;

declare const _default: {
  parse: typeof parse;
  query: typeof query;
  update: typeof update;
  serialize: typeof serialize;
  canonicalize: typeof canonicalize;
  capabilities: typeof capabilities;
  Dataset: typeof Dataset;
  dataFactory: DataFactory;
  wasmAvailable: typeof wasmAvailable;
  version: string;
};
export default _default;
