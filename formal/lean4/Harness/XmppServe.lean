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
import Std.Sync.Mutex
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
  /-- Milliseconds between mailbox polls (see `pollMailbox`). -/
  pollMs : Nat := 50
  /-- The most mailbox polls one connection may make, for the same
  reason `maxUnits` exists. At the default 50 ms this is about 58 days. -/
  maxPollTicks : Nat := 100000000

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

/-- What the two concurrent parts of the host share. The read loop and
the mailbox poller both write to the same socket, so every write goes
through `lock`: without it a delivered stanza could land in the middle of
a reply and produce bytes that are not XML. `session` is the poller's
view of the connection — it reads it to ask `Session.canDeliver`, and
never writes it. -/
structure Host where
  opts : Options
  out : IO.FS.Stream
  lock : Std.Mutex Unit
  session : IO.Ref Session
  finished : IO.Ref Bool

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

/-- Perform one action. Returns whether the connection should close.
Every byte that reaches the socket passes through `h.lock`. -/
def performOut (h : Host) (seq : Nat) : Out → IO Bool
  | .send text => do
      h.lock.atomically (liftM (m := IO) (do h.out.putStr text; h.out.flush))
      return false
  | .route bare text => do routeTo h.opts bare text seq; return false
  | .saveRoster bare encoded => do
      let p := rosterPath h.opts bare
      IO.FS.createDirAll (p.parent.getD ".")
      IO.FS.writeFile p encoded
      return false
  | .presence _bare full available => do
      let p := presencePath h.opts full
      IO.FS.createDirAll (p.parent.getD ".")
      if available then IO.FS.writeFile p "1"
      else if ← p.pathExists then IO.FS.removeFile p
      return false
  | .close => return true

/-- Drain this session's mailbox: read every file, unlink it, and hand
its bytes to `Server.deliver`, which decides whether the session may
receive them yet. -/
def drainMailbox (h : Host) (s : Session) : IO Unit := do
  -- `Session.canDeliver` is the gate, and it is asked BEFORE the
  -- directory is touched. Reading a stanza this session may not yet
  -- receive would delete it, and `Server.deliver` returning nothing
  -- would leave no trace of the loss.
  if !s.canDeliver then return ()
  match s.bareJid with
  | none => return ()
  | some bare =>
    let dir := spoolDir h.opts bare
    if !(← dir.pathExists) then return ()
    let entries := (← dir.readDir).map (·.fileName)
    for name in entries.qsort (· < ·) do
      let p := dir / name
      let text ← try IO.FS.readFile p catch _ => pure ""
      let acts := Server.deliver s text
      -- Unlink only after the bytes have been handed on, so a crash
      -- between the two loses nothing.
      for a in acts do
        let _ ← performOut h 0 a
      if !acts.isEmpty then
        try IO.FS.removeFile p catch _ => pure ()

/-- The mailbox poller, run as a separate task beside the read loop.

It exists because the read loop BLOCKS: `IO.FS.Stream.read` waits for a
byte, and a session that has authenticated and is sitting quietly would
otherwise never look at its mailbox — a message sent to it while it was
idle would arrive only when it next typed something. That was measured,
not guessed: with the poller absent, `tools/xmpp-interop.sh` timed out
at "romeo receives the message" while the stanza sat in the spool.

Bounded like everything else here: `ticks` is an explicit `Nat`. -/
def pollMailbox (h : Host) : Nat → IO Unit
  | 0 => pure ()
  | ticks + 1 => do
    if ← h.finished.get then return ()
    drainMailbox h (← h.session.get)
    IO.sleep (UInt32.ofNat h.opts.pollMs)
    pollMailbox h ticks

/-! ## The loop -/

/-- Read one byte from stdin, blocking until it arrives. Empty means end
of file.

ONE byte, not a block. `IO.FS.Stream.read n` is `fread`: it blocks until
`n` bytes have arrived or the stream ends, so asking for 4096 stalls an
interactive client that has sent one stanza and is waiting for the
answer. That was measured, not guessed: the first version of this file
asked for 4096 and the live SCRAM exchange in `tests/xmpp/server.mjs`
timed out with the server holding a complete `<auth/>` it had never been
handed. A batch replay through a closed pipe did NOT show it, because
end of file releases the read.

The cost is one system call per byte. For a chat stream that is a few
hundred calls per stanza, which is not the bottleneck; if it ever
becomes one, the fix is a non-blocking read that returns what is
available, not a larger blocking one. -/
def readChunk (inp : IO.FS.Stream) : IO String := do
  let lead ← inp.read 1
  if lead.isEmpty then return ""
  let b := lead.get! 0
  -- RFC 3629: the lead byte says how many continuation bytes follow. A
  -- character split across two reads would otherwise reach
  -- `String.fromUTF8!` half-formed, and a message body in any language
  -- but English would end the connection.
  let extra : Nat :=
    if b < 0x80 then 0
    else if b ≥ 0xF0 then 3
    else if b ≥ 0xE0 then 2
    else if b ≥ 0xC0 then 1
    else 0
  let rest ← if extra == 0 then pure ByteArray.empty else inp.read (USize.ofNat extra)
  let all := lead ++ rest
  match String.fromUTF8? all with
  | some str => return str
  | none =>
    -- Not valid UTF-8. RFC 6120 section 11.5 makes the stream UTF-8, so
    -- this is a bad-format stream error rather than something to guess
    -- at; returning the replacement character lets the framer reach the
    -- server, which answers with the error.
    return "\uFFFD"

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
def drainBuffer (h : Host) (st : LoopState) :
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
      | some b => readRoster h.opts b
      | none => pure st.env.roster
    let (s', env', outs) := Server.step st.session { st.env with roster := roster } unit
    let mut closed := false
    let mut seq := st.seq
    for a in outs do
      seq := seq + 1
      if ← performOut h seq a then closed := true
    h.session.set s'
    drainBuffer h
      { session := s', env := env', buffer := rest, seq := seq
        eof := st.eof, done := closed || s'.stage == .closed } fuel

/-- The read loop, bounded by `Options.maxUnits`. Exhausting the bound is
RFC 6120 section 4.9.3.14 `policy-violation`, reported to the client
before the stream closes. -/
def loop (h : Host) (inp : IO.FS.Stream) (st : LoopState) :
    Nat → IO LoopState
  | 0 => do
      for a in Server.streamError "policy-violation" "too many stream units" do
        let _ ← performOut h 0 a
      return { st with done := true }
  | fuel + 1 => do
  if st.done then return st
  let st ← drainBuffer h st (st.buffer.length + 1)
  if st.done then return st
  drainMailbox h st.session
  if st.eof then return { st with done := true }
  let chunk ← readChunk inp
  if chunk.isEmpty then
    -- End of input. Answer a half-closed stream the way RFC 6120
    -- section 4.4 asks, then stop.
    let st ← drainBuffer h { st with eof := true } (st.buffer.length + 1)
    if !st.done then
      let _ ← performOut h 0 (.send "</stream:stream>")
    return { st with done := true }
  loop h inp { st with buffer := st.buffer ++ chunk } fuel

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
    let session0 := Session.init cfg
    let h : Host := {
      opts := o, out := out
      lock := ← Std.Mutex.new ()
      session := ← IO.mkRef session0
      finished := ← IO.mkRef false }
    let poller ← IO.asTask (pollMailbox h o.maxPollTicks)
    let _ ← loop h inp
      { session := session0, env := ⟨[]⟩, buffer := "", seq := 0
        eof := false, done := false } o.maxUnits
    h.finished.set true
    let _ ← IO.wait poller
    return 0

end Harness.XmppServe

def main (args : List String) : IO UInt32 := Harness.XmppServe.main args
