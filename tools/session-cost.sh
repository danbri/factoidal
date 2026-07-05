#!/bin/bash
# Sum the estimated cost of an agent session INCLUDING its subagent
# children, via agentsview (https://pypi.org/project/agentsview/).
#
# Usage:
#   tools/session-cost.sh                 # all sessions in this project
#   tools/session-cost.sh <project-name>  # explicit project (default: factoidal)
#
# See skills/session-cost-accounting/SKILL.md for interpretation notes.
set -euo pipefail
PROJECT="${1:-factoidal}"

uvx agentsview sync >/dev/null 2>&1 || true
uvx agentsview session list --project "$PROJECT" --include-children --json 2>/dev/null | python3 -c "
import sys, json, subprocess
d = json.load(sys.stdin)
ss = d if isinstance(d, list) else d.get('sessions', d.get('items', []))
ids = [s['id'] for s in ss]
rows, total, out_tok = [], 0.0, 0
for i in ids:
    r = subprocess.run(['uvx','agentsview','session','usage', i, '--json'],
                       capture_output=True, text=True)
    try:
        u = json.loads(r.stdout)
    except Exception:
        continue
    c = float(u.get('cost_usd') or 0)
    o = int(u.get('total_output_tokens') or 0)
    total += c; out_tok += o
    rows.append((c, i, ','.join(u.get('models') or ['?']), o))
rows.sort(reverse=True)
mains = [r for r in rows if not r[1].startswith('agent-')]
subs  = [r for r in rows if r[1].startswith('agent-')]
print(f'sessions: {len(rows)} ({len(mains)} main + {len(subs)} subagent)')
print(f'TOTAL estimated cost: \${total:,.2f}')
print(f'total output tokens:  {out_tok:,}')
print(f'  main sessions:      \${sum(r[0] for r in mains):,.2f}')
print(f'  subagents:          \${sum(r[0] for r in subs):,.2f}')
print('top 10 by cost:')
for c, i, m, o in rows[:10]:
    print(f'  \${c:9.2f}  {i[:24]:24}  {m}  out={o:,}')
"
