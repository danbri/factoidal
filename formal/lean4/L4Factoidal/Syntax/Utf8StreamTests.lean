/- Build-time executable checks for bounded UTF-8 chunk decoding. -/
import L4Factoidal.Syntax.Utf8Stream

namespace L4Factoidal.Syntax

def decodeTwo (first second : ByteArray) : Except String String := do
  let (a, state) ← Utf8Stream.feed Utf8Stream.init first
  let (b, state) ← Utf8Stream.feed state second
  state.finish
  pure (a ++ b)

def decodesTwoAs (first second : ByteArray) (expected : String) : Bool :=
  match decodeTwo first second with
  | .ok text => text == expected
  | .error _ => false

def rejects (bytes : ByteArray) : Bool :=
  match Utf8Stream.feed Utf8Stream.init bytes with
  | .error _ => true
  | .ok _ => false

def hasIncompleteTail (bytes : ByteArray) : Bool :=
  match Utf8Stream.feed Utf8Stream.init bytes with
  | .error _ => false
  | .ok (_, state) => match state.finish with
    | .error _ => true
    | .ok _ => false

/- A two-byte codepoint split after its leading byte. -/
#guard decodesTwoAs ("Ü".toUTF8.extract 0 1) ("Ü".toUTF8.extract 1 2) "Ü"

/- A four-byte codepoint split after three bytes: the maximum retained tail. -/
#guard decodesTwoAs ("😀".toUTF8.extract 0 3) ("😀".toUTF8.extract 3 4) "😀"

/- A split UTF-8 sequence is not an error until end-of-stream; malformed
interior data is rejected immediately. -/
#guard hasIncompleteTail ("😀".toUTF8.extract 0 3)
#guard rejects (ByteArray.mk #[0xff])

end L4Factoidal.Syntax
