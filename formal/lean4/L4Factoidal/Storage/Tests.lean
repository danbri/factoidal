/-
L4Factoidal.Storage.Tests — build-time checks for the HDT byte
primitives, covering by EVALUATION what is not yet proved.
-/
import L4Factoidal.Storage.Bytes

namespace L4Factoidal.Storage

-- VByte round trip across single-byte, boundary and multi-byte
-- values. This is the evaluation cover standing in for the general
-- theorem stated in Bytes.lean.
#guard vbyteDecode (vbyteEncode 0) == some (0, 1)
#guard vbyteDecode (vbyteEncode 1) == some (1, 1)
#guard vbyteDecode (vbyteEncode 127) == some (127, 1)
#guard vbyteDecode (vbyteEncode 128) == some (128, 2)
#guard vbyteDecode (vbyteEncode 129) == some (129, 2)
#guard vbyteDecode (vbyteEncode 16383) == some (16383, 2)
#guard vbyteDecode (vbyteEncode 16384) == some (16384, 3)
#guard vbyteDecode (vbyteEncode 1000000) == some (1000000, 3)

-- HDT's VByte marks the LAST byte with the high bit, the OPPOSITE of
-- LEB128's continuation marker. A single-byte value therefore has its
-- high bit SET — the check that catches a flipped polarity, which
-- otherwise only shows up on multi-byte values.
#guard vbyteEncode 5 == [133]        -- 5 + 128
#guard vbyteEncode 128 == [0, 129]   -- low 7 bits clear, then 1|128

-- Decoding an empty or truncated buffer fails rather than guessing.
#guard vbyteDecode [] == none
#guard vbyteDecode [0] == none       -- continuation with nothing after

-- 32-bit little-endian round trip.
#guard readU32LE (writeU32LE 0) 0 == some 0
#guard readU32LE (writeU32LE 1) 0 == some 1
#guard readU32LE (writeU32LE 4294967295) 0 == some 4294967295
#guard readU32LE (writeU32LE 305419896) 0 == some 305419896   -- 0x12345678
#guard writeU32LE 1 == [1, 0, 0, 0]                           -- little-endian
#guard readU32LE [1, 2, 3] 0 == none                          -- short buffer

-- Checksums are deterministic and change with the data.
#guard crc8 [] == crc8 []
#guard crc8 [1, 2, 3] != crc8 [1, 2, 4]
#guard crc32c [1, 2, 3] != crc32c [1, 2, 4]

-- Section round trip, by evaluation.
private def sec : Section := ⟨[1, 2, 3], [10, 20, 30, 40]⟩
#guard Section.parse sec.serialize 3 4 == some sec
#guard sec.serialize.length == 3 + 1 + 4 + 4

-- CORRUPTION IS REJECTED, not partially read. A storage layer that
-- reads on through a bad checksum turns a disk error into wrong
-- query answers.
private def corruptData : List UInt8 :=
  sec.serialize.set 5 99      -- flip a data byte
#guard Section.parse corruptData 3 4 == none
private def corruptPreamble : List UInt8 :=
  sec.serialize.set 0 99      -- flip a preamble byte
#guard Section.parse corruptPreamble 3 4 == none

-- A truncated section fails rather than returning a short read.
#guard Section.parse (sec.serialize.take 5) 3 4 == none

end L4Factoidal.Storage
