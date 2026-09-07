/-
Harness.XmppServe — `l4xmpp-serve`, one XMPP client connection on
stdin and stdout.

The carrier (see `deploy/fly/xmpp/`) listens on a socket, terminates TLS
and forks one copy of this process per connection with the socket on its
standard streams. This file therefore contains no socket code, no TLS,
and no protocol decisions. It does five things:

  1. read bytes from stdin into a buffer;
  2. ask `L4Factoidal.XMPP.Framing.nextUnit` where the next unit ends;
  3. call `L4Factoidal.XMPP.Server.step`;
  4. perform each `Out` — write bytes to stdout, append bytes to a file,
     replace a file, remove a file;
  5. poll this session's own mailbox directory and hand whatever is in it
     to `Server.deliver`.

Everything that could be called a protocol decision — what to answer,
whether a password is right, where a stanza goes, what a roster looks
like as bytes — is in `L4Factoidal/XMPP/`. NOT part of the verified
library: this file does I/O, per the same rule that keeps the W3C
harness out of it.

Inter-connection routing is a directory of files. `<spool>/<bare
jid>/<counter>` holds one stanza's exact bytes; the receiving process
reads the directory, sends each file's contents, and unlinks it. It is
the first slice, chosen because Lean's `IO` gives file operations and no
socket pair, and because a spool file is inspectable when a test fails.
A shared-memory or socket-pair carrier can replace it without touching
`L4Factoidal/XMPP/`: the `Out.route` action already names a destination
and a payload, not a file.

Usage:
  l4xmpp-serve --domain example.com --state DIR [--accounts FILE]
               [--plaintext] [--stream-id ID] [--nonce N]

  --accounts FILE   one `user:password` per line. Absent, the file
                    `DIR/accounts` is read; absent again, the process
                    starts with no accounts and every authentication
                    fails.
  --plaintext       the carrier did NOT terminate TLS (the port 5222
                    test listener). Recorded in the session config and
                    reported on stderr; see `Config.tlsCarrier`.
  --stream-id, --nonce  fix the two random values so a test transcript is
                    reproducible. Absent, they come from the clock.
  --max-units N     refuse more than N top-level units on this stream
                    (default 1000000). See `Options.maxUnits`.
-/
import L4Factoidal.XMPP.Server

open L4Factoidal.XMPP
open L4Factoidal.XMPP.Server (Session Env Out Config Account)

namespace Harness.XmppServe

/-! ## Options -/

structure Options where
  domain : String := "localhost"
  stateDir : String := ".xmpp-state"
  accountsFile : Option String := none
  plaintext : Bool := false
  streamId : Option String := none
  nonce : Option String := none
  /-- The most top-level units this connection may send. RFC 6120 has no
  such limit; it exists so the read loop is a bounded recursion rather
  than a `partial def`, which this repository does not allow to grow.
  Reaching it closes the stream with `policy-violation` (RFC 6120
  section 4.9.3.14), which is a stated refusal and not a hang.
  A million units is far above any real session. -/
  maxUnits : Nat := 1000000

/-- Argument parsing as a fold, so there is no recursion to bound. The
state carries the flag whose value is expected next; a flag left waiting
for a value at the end is an error rather than a silently ignored one. -/
def applyArg : Except String (Options × Option String) → String →
    Except String (Options × Option String)
  | .error m, _ => .error m
  | .ok (o, pending), a =>
    match pending with
    | some flag =>
      match flag with
      | "--domain" => .ok ({ o with domain := a }, none)
      | "--state" => .ok ({ o with stateDir := a }, none)
      | "--accounts" => .ok ({ o with accountsFile := some a }, none)
      | "--stream-id" => .ok ({ o with streamId := some a }, none)
      | "--nonce" => .ok ({ o with nonce := some a }, none)
      | "--max-units" => .ok ({ o with maxUnits := (a.toNat?).getD o.maxUnits }, none)
      | _ => .error s!"unknown argument `{flag}`"
    | none =>
      if a == "--plaintext" then .ok ({ o with plaintext := true }, none)
      else if a == "--domain" || a == "--state" || a == "--accounts"
              || a == "--stream-id" || a == "--nonce" || a == "--max-units" then
        .ok (o, some a)
      else .error s!"unknown argument `{a}`"

def parseArgs (o : Options) (args : List String) : Except String Options :=
  match args.foldl applyArg (.ok (o, none)) with
  | .error m => .error m
  | .ok (_, some flag) => .error s!"`{flag}` needs a value"
  | .ok (o', none) => .ok o'

/-! ## Accounts -/

def parseAccounts (text : String) : List Account :=
  (text.splitOn "\n").filterMap (fun line =>
    let l := line.trim
    if l.isEmpty || l.startsWith "#" then none
    else match l.splitOn ":" with
      | u :: rest => if u.isEmpty then none else some ⟨u, String.intercalate ":" rest⟩
      | [] => none)

/-! ## Paths. The host owns the file names; the bytes are the server's. -/

/-- A bare JID as one path segment. Every byte that is not a letter, a
digit, `.`, `-` or `_` becomes `%` and two hex digits, so no JID can
escape the spool directory or collide with another. -/
def pathSafe (s : String) : String :=
  String.join (s.toUTF8.toList.map (fun b =>
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '.' || c == '-' || c == '_' then String.singleton c
    else
      let hex := "0123456789abcdef"
      let hi := hex.get! ⟨(b.toNat / 16)⟩
      let lo := hex.get! ⟨(b.toNat % 16)⟩
      "%" ++ String.singleton hi ++ String.singleton lo))

def spoolDir (o : Options) (bare : String) : System.FilePath :=
  System.FilePath.mk o.stateDir / "spool" / pathSafe bare

def rosterPath (o : Options) (bare : String) : System.FilePath :=
  System.FilePath.mk o.stateDir / "roster" / (pathSafe bare ++ ".tsv")

def presencePath (o : Options) (full : String) : System.FilePath :=
  System.FilePath.mk o.stateDir / "presence" / pathSafe full

/-! ## Performing the server's actions -/

def readRoster (o : Options) (bare : String) : IO Server.Roster := do
  let p := rosterPath o bare
  if ← p.pathExists then
    return Server.rosterDecode (← IO.FS.readFile p)
  else return []

/-- Append one stanza to a bare JID's mailbox. The file name is the
current nanosecond clock plus a counter, so delivery order is the order
of the directory listing sorted by name. -/
def routeTo (o : Options) (bare : String) (text : String) (seq : Nat) : IO Unit := do
  let dir := spoolDir o bare
  IO.FS.createDirAll dir
  let stamp := (← IO.monoNanosNow)
  IO.FS.writeFile (dir / s!"{stamp}-{seq}") text

def performOut (o : Options) (out : IO.FS.Stream) (seq : Nat) : Out → IO Bool
  | .send text => do out.putStr text; out.flush; return false
  | .route bare text => do routeTo o bare text seq; return false
  | .saveRoster bare encoded => do
      let p := rosterPath o bare
      IO.FS.createDirAll (p.parent.getD ".")
      IO.FS.writeFile p encoded
      return false
  | .presence _bare full available => do
      let p := presencePath o full
      IO.FS.createDirAll (p.parent.getD ".")
      if available then IO.FS.writeFile p "1"
      else if ← p.pathExists then IO.FS.removeFile p
      return false
  | .close => return true

/-- Drain this session's mailbox: read every file, unlink it, and hand
its bytes to `Server.deliver`, which decides whether the session may
receive them yet. -/
def drainMailbox (o : Options) (s : Session) (out : IO.FS.Stream) : IO Unit := do
  match s.bareJid with
  | none => return ()
  | some bare =>
    let dir := spoolDir o bare
    if !(← dir.pathExists) then return ()
    let entries := (← dir.readDir).map (·.fileName)
    for name in entries.qsort (· < ·) do
      let p := dir / name
      let text ← try IO.FS.readFile p catch _ => pure ""
      try IO.FS.removeFile p catch _ => pure ()
      if !text.isEmpty then
        for a in Server.deliver s text do
          let _ ← performOut o out 0 a

/-! ## The loop -/

/-- Read whatever bytes are available on stdin, blocking for at least one
when the buffer holds no complete unit. `IO.FS.Stream.read` returns an
empty array at end of file. -/
def readChunk (inp : IO.FS.Stream) : IO String := do
  let bytes ← inp.read 4096
  if bytes.isEmpty then return ""
  return String.fromUTF8! bytes

structure LoopState where
  session : Session
  env : Env
  buffer : String
  seq : Nat
  eof : Bool
  done : Bool

/-- Process every complete unit sitting in the buffer. `fuel` bounds the
recursion: every unit consumes at least one character, so the buffer's
length is always enough. -/
def drainBuffer (o : Options) (out : IO.FS.Stream) (st : LoopState) :
    Nat -> IO LoopState
  | 0 => return st
  | fuel + 1 => do
  if st.done then return st
  match Framing.nextUnit (!st.session.awaitingStreamOpen) st.buffer with
  | none => return st
  | some (unit, rest) =>
    -- The roster on disk is the truth; read it fresh so a change another
    -- connection made is seen.
    let roster ← match st.session.bareJid with
      | some b => readRoster o b
      | none => pure st.env.roster
    let (s', env', outs) := Server.step st.session { st.env with roster := roster } unit
    let mut closed := false
    let mut seq := st.seq
    for a in outs do
      seq := seq + 1
      if ← performOut o out seq a then closed := true
    drainBuffer o out
      { session := s', env := env', buffer := rest, seq := seq
        eof := st.eof, done := closed || s'.stage == .closed } fuel

/-- The read loop, bounded by `Options.maxUnits`. Exhausting the bound is
RFC 6120 section 4.9.3.14 `policy-violation`, reported to the client
before the stream closes. -/
def loop (o : Options) (inp out : IO.FS.Stream) (st : LoopState) :
    Nat → IO LoopState
  | 0 => do
      for a in Server.streamError "policy-violation" "too many stream units" do
        let _ ← performOut o out 0 a
      return { st with done := true }
  | fuel + 1 => do
  if st.done then return st
  let st ← drainBuffer o out st (st.buffer.length + 1)
  if st.done then return st
  drainMailbox o st.session out
  if st.eof then return { st with done := true }
  let chunk ← readChunk inp
  if chunk.isEmpty then
    -- End of input. Answer a half-closed stream the way RFC 6120
    -- section 4.4 asks, then stop.
    let st ← drainBuffer o out { st with eof := true } (st.buffer.length + 1)
    if !st.done then out.putStr "</stream:stream>"; out.flush
    return { st with done := true }
  loop o inp out { st with buffer := st.buffer ++ chunk } fuel

def usage : String :=
  "usage: l4xmpp-serve --domain DOMAIN --state DIR [--accounts FILE] " ++
  "[--plaintext] [--stream-id ID] [--nonce N] [--max-units N]"

def main (args : List String) : IO UInt32 := do
  match parseArgs {} args with
  | .error m => do
      (← IO.getStderr).putStrLn s!"l4xmpp-serve: {m}"
      (← IO.getStderr).putStrLn usage
      return 2
  | .ok o =>
    let accountsText ← do
      match o.accountsFile with
      | some f => try IO.FS.readFile f catch _ => pure ""
      | none =>
        let p := System.FilePath.mk o.stateDir / "accounts"
        if ← p.pathExists then IO.FS.readFile p else pure ""
    let accounts := parseAccounts accountsText
    let stamp := (← IO.monoNanosNow)
    let cfg : Config :=
      { domain := o.domain
        streamId := o.streamId.getD s!"s{stamp}"
        serverNonce := o.nonce.getD s!"n{stamp}"
        -- A fixed per-deployment salt. RFC 5802 wants a per-account
        -- salt; this build derives credentials from a plaintext account
        -- file at authentication time, so there is one salt and it is
        -- recorded here rather than implied. Stated as a limitation in
        -- deploy/fly/xmpp/README.md.
        saltB64 := "W22ZaJ0SNY7soEsUEjb6gQ=="
        iterationCount := 4096
        accounts := accounts
        tlsCarrier := !o.plaintext }
    IO.FS.createDirAll (System.FilePath.mk o.stateDir)
    let err ← IO.getStderr
    err.putStrLn s!"l4xmpp-serve: domain={o.domain} accounts={accounts.length} tls-carrier={!o.plaintext}"
    let inp ← IO.getStdin
    let out ← IO.getStdout
    let _ ← loop o inp out
      { session := Session.init cfg, env := ⟨[]⟩, buffer := "", seq := 0
        eof := false, done := false } o.maxUnits
    return 0

end Harness.XmppServe

def main (args : List String) : IO UInt32 := Harness.XmppServe.main args
