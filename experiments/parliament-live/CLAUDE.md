# Forgetmeknot Palace (FPKG) — agent rules

A small graph navigator over UK Parliament APIs.

The per-API documentation lives in the **forgetmenot** skills repo at
<https://github.com/danbri/forgetmenot/tree/main/skills>. **Read the
relevant `SKILL.md` before touching an endpoint.** We are guests on those
APIs and the Open Parliament Licence (OPL) gives us a lot but expects us
to be polite, accurate, and non-impersonating.

## Core rules

### 1. Probe-then-render. No exceptions.

Before writing or modifying any renderer for an endpoint, **the very
first action in that turn must be a `curl` to that endpoint and reading
the actual JSON keys**. Pattern-matching from a sibling endpoint is how
you write `v.PublishedDivision.Title` for Members-API voting (which
doesn't exist — voting uses lowercase camelCase fields directly on
`value`). One real probe beats hours of confidently-wrong code.

If you have already probed an endpoint earlier in the session, you may
re-use that knowledge — but if you have not, probe before you render.

### 2. Defensive renderers fail loud.

Never fall back to placeholder strings like `'(division)'` or
`'(unknown)'` when key fields are missing. If the data shape doesn't
match what the renderer expects, surface that — render a visibly-broken
state that includes the keys actually present (e.g. `⚠ shape mismatch:
keys = id, title, date, …`). Future shape changes then become
immediately visible bugs rather than masquerading as boring real data.

### 3. The proxy is the only path. Never call parliament.uk directly from the page.

The page must always go through the proxy at `/api/...` (or absolute
`http://localhost:8787/api/...` when loaded outside its origin). The
proxy is the place that applies TTL policy, the attribution header, and
CORS. Parliament APIs do not allow CORS, so a direct call from the page
will fail.

### 4. TTL policy lives in `server.mjs`.

It mirrors what each API advertises **and** what the data actually
changes like — short TTLs for live (`now-api` ≤5 s), long for
effectively-immutable (Hansard debate text, recorded divisions, member
thumbnails). Never extend a TTL beyond what the data's mutability
supports. Read the existing comments before adding a new upstream.

### 5. No semantic logic in the proxy.

The proxy is whitelist + cache + attribution + CORS. Decisions about
which fields to render, which entities to follow, how to interpret
slides — those are app concerns, in the page. The proxy must remain a
"dumb pipe with policy".

### 6. OPL attribution is non-negotiable.

Every page must visibly carry the string

> Contains Parliamentary information licensed under the Open Parliament
> Licence v3.0

with a link to the licence. Every proxy response also carries the same
in `X-Attribution`. This is a licence condition, not a stylistic choice.

### 7. Branding: do not impersonate.

The Royal Arms and Crowned Portcullis are explicitly excluded from the
OPL — never use them. The internal name is **Forgetmeknot Palace**
(FPKG). Avoid "Parliament" as a prominent UI string; the page must read
as a third-party prototype. "UK Parliament" appears only in factual
data-source labels (About page, footer) and in the OPL attribution.

### 8. Use the data and tooling that exist. Don't improvise.

Endpoints currently wired:

| Source | Path on our proxy | Use |
|---|---|---|
| `now-api.parliament.uk` | `/api/now/<zone>/<…>` | live chamber state |
| `members-api.parliament.uk` | `/api/members/<…>` | members, parties, constituencies, voting record |
| `hansard-api.parliament.uk` | `/api/hansard/<…>` | historical debate text, section tree, calendar |
| `commonsvotes-api.parliament.uk` | `/api/cvotes/<…>` | recorded divisions (Commons) |
| `lordsvotes-api.parliament.uk` | `/api/lvotes/<…>` | recorded divisions (Lords) |
| `api.parliament.uk/sparql` | `/api/sparql` | linked-data join across the lot — not yet wired into the UI |

Probed and ready to wire as needed:

- `bills-api.parliament.uk` — Bills, stages, sponsors. CORS-cacheable.
- `oralquestionsandmotions-api.parliament.uk` — forward chamber business
  via `AnsweringWhen`; EDMs.
- `committees-api.parliament.uk` — committees, members, broadcasts.

When you need to extend, **read the corresponding `SKILL.md` first** —
the docs name the parameter shape and pagination quirks.

### 9. Cross-API caching signals.

We have a written-down policy for how one API tells us how stale
another can safely be (e.g. `now-api` blank for >5 min → today's
Hansard cannot grow → bump Hansard TTL). When you change a TTL, think
about whether a cross-signal makes a tighter bound possible.

### 10. Accessibility

- Body text must meet WCAG AA (≥4.5:1 contrast) on the background.
  `--ink-mute` is **never** primary text — decoration/stripes only.
  `--ink-soft` is the lowest acceptable for any prose at ≥14 px.
- Minimum body font: 16 px. Minimum secondary text: 13 px.
- Don't shout in all-caps for navigation, headings, or content. All-caps
  is reserved for very small label tags only (e.g. badge pills).
- Mobile-first. Test at 360 px wide before adding anything desktop-only.

### 11. Honesty in the UI

When data is missing, show that explicitly. When the chamber is not
sitting, say so and link to the next sitting day if known. Don't compose
plausible-looking placeholders that obscure missing data — that's a
specific kind of dishonesty in a graph navigator.

### 12. Deployment

We deploy to fly.io as app **`fpkg`** in the `contextris` org, region
`lhr`. Password gate is implemented both server-side
(`PROXY_PASSWORD` env / fly secret) and client-side (SHA-256 hash baked
into `index.html`). The client check is UX; the server check is the gate.
