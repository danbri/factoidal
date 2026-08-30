/- Native POSIX range reader for executable block-engine probes.

   This deliberately lives under Harness, not L4Factoidal: `pread` is an
   operating-system realization of the pure IBK2 ByteRange contract, not part
   of the verified block semantics and not available to the WASM target. -/
import L4Factoidal.Storage.IndexedBlockWireV2

namespace Harness.PosixRangeIO

open L4Factoidal.Storage.IndexedBlockWireV2

/-- Read at an absolute file offset without changing any shared file cursor.
    The C implementation returns an empty array on open/read/short-read
    failure; `readRange?` below turns that into an explicit refusal by checking
    the exact requested extent. -/
@[extern "l4_block_pread"]
opaque preadRaw (path : @& String) (offset length : UInt64) : IO ByteArray

def readRange? (path : String) (range : ByteRange) : IO (Option ByteArray) := do
  let bytes ← preadRaw path (UInt64.ofNat range.offset) (UInt64.ofNat range.length)
  if bytes.size == range.length then pure (some bytes) else pure none

end Harness.PosixRangeIO
