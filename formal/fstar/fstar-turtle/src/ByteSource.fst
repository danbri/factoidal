module ByteSource

// Buffered streaming byte reader for the verified Turtle parser.
// Modeled after Serd's byte_source.h/c but using Low* idioms.
//
// Supports two input modes:
//   1. String mode: zero-copy read from a byte buffer
//   2. Stream mode: buffered reads via a callback (for file I/O)
//
// KaRaMeL extracts this to C with LowStar.Buffer operations.

open FStar.HyperStack.ST
open FStar.UInt8
open FStar.UInt32
open LowStar.Buffer
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

// Status codes matching Serd convention
type status =
  | Success
  | Failure       // normal end (e.g. EOF on already-at-EOF)
  | ErrBadSyntax
  | ErrUnknown    // I/O or stream error

// Cursor: tracks position for error reporting
noeq type cursor = {
  line: U32.t;
  col: U32.t;
}

let cursor_init : cursor = { line = 1ul; col = 1ul }

// Page size for buffered stream reads (4096 bytes, matching Serd)
let page_size : U32.t = 4096ul

// The byte source abstraction.
// For KaRaMeL extraction, we use a noeq type with mutable state.
//
// In string mode:
//   buf points to the input string, buf_len is its length,
//   read_head advances through it, no allocation needed.
//
// In stream mode:
//   buf is an allocated page_size buffer, read_func fills it,
//   buf_len tracks how many valid bytes are in the buffer.

// Read callback type: reads up to n bytes into dst, returns count read.
// This is an assume val that will be stubbed in C.
assume val read_func_t : Type0

// Error check callback: returns true if the stream has an error condition.
assume val error_func_t : Type0

noeq type byte_source = {
  buf: B.buffer U8.t;          // read buffer (string pointer or allocated page)
  buf_len: U32.t;              // valid bytes in buf
  buf_capacity: U32.t;         // allocated size (0 for string mode)
  read_head: U32.t;            // current position in buf
  cur: cursor;                 // line/col tracker
  eof: bool;                   // end-of-input reached
  from_stream: bool;           // true = stream mode, false = string mode
}

// Peek: return current byte without advancing.
// Requires: not eof, read_head < buf_len
let peek (src: byte_source) : ST.Stack U8.t
  (requires fun h ->
    B.live h src.buf /\
    not src.eof /\
    U32.v src.read_head < U32.v src.buf_len)
  (ensures fun h0 r h1 -> h0 == h1)
  = B.index src.buf src.read_head

// Peek as int (returns -1 on EOF, byte value otherwise).
// This is the primary interface used by the parser.
let peek_byte (src: byte_source) : ST.Stack FStar.Int32.t
  (requires fun h -> B.live h src.buf)
  (ensures fun h0 _ h1 -> h0 == h1)
  = if src.eof then FStar.Int32.int_to_t (-1)
    else if U32.(src.read_head >=^ src.buf_len) then FStar.Int32.int_to_t (-1)
    else FStar.Int32.int_to_t (U8.v (B.index src.buf src.read_head))

// Update cursor for newline tracking
let update_cursor (c: cursor) (byte: U8.t) : cursor =
  if byte = 0x0Auy then  // '\n'
    { line = U32.(c.line +^ 1ul); col = 0ul }
  else
    { line = c.line; col = U32.(c.col +^ 1ul) }

// Advance: move read_head forward by one byte.
// In string mode, just increments. Sets eof when past end.
// Returns updated byte_source (functional update for extraction).
let advance_string (src: byte_source) : ST.Stack (byte_source & status)
  (requires fun h ->
    B.live h src.buf /\
    not src.from_stream /\
    not src.eof /\
    U32.v src.read_head < U32.v src.buf_len)
  (ensures fun h0 _ h1 -> B.live h1 (fst (snd (h0, (src, Success)))).buf)
  = let byte = B.index src.buf src.read_head in
    let new_head = U32.(src.read_head +^ 1ul) in
    let new_cur = update_cursor src.cur byte in
    let new_eof = U32.(new_head >=^ src.buf_len) in
    ({ src with read_head = new_head; cur = new_cur; eof = new_eof }, Success)

// Open from a string buffer (zero-copy).
// The caller owns the buffer and must keep it live.
let open_string (buf: B.buffer U8.t) (len: U32.t) : ST.Stack byte_source
  (requires fun h -> B.live h buf /\ U32.v len <= B.length buf)
  (ensures fun h0 r h1 -> h0 == h1 /\ not r.from_stream)
  = { buf = buf;
      buf_len = len;
      buf_capacity = 0ul;  // signal: string mode, no deallocation needed
      read_head = 0ul;
      cur = cursor_init;
      eof = U32.(len =^ 0ul);
      from_stream = false }

// Skip UTF-8 BOM (0xEF 0xBB 0xBF) if present at current position.
// Returns Success if BOM was skipped or not present.
let skip_bom (src: byte_source) : ST.Stack (byte_source & status)
  (requires fun h ->
    B.live h src.buf /\
    not src.eof)
  (ensures fun _ _ _ -> True)
  = if U32.(src.buf_len -^ src.read_head <^ 3ul) then (src, Success)
    else
      let b0 = B.index src.buf src.read_head in
      let b1 = B.index src.buf U32.(src.read_head +^ 1ul) in
      let b2 = B.index src.buf U32.(src.read_head +^ 2ul) in
      if b0 = 0xEFuy && b1 = 0xBBuy && b2 = 0xBFuy then
        ({ src with read_head = U32.(src.read_head +^ 3ul) }, Success)
      else
        (src, Success)
