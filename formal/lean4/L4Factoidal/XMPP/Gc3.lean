/-!
GC3 ("Groupchat 3.0") room/participant state machine.

Not yet implemented — GC3 itself is still an early-stage, unfinished
XSF spec (see DESIGN.md). Intended scope once it stabilizes: persistent
join/leave (offline participants remain "in" the room), affiliation/
permission transitions, occupant-id stability across nickname changes,
join idempotency, and the stanza codec for GC3's wire format — each as a
proved safety property, not just an executable check. See
`factoidal`'s `lean4-proof-patterns` skill for the proof style to reuse
(fuel-bounded definitions, nested-match splitting, timed per-theorem
compiles).
-/

namespace L4Factoidal.XMPP.Gc3

end L4Factoidal.XMPP.Gc3
