# Build receipt

- SHA: `f7e25ac11ff8a81d4e3a5d3befa290d77f61942f`
- HEAD commit date (UTC): 2026-10-10T17:50:43Z
- Build date (UTC): 2026-10-10T18:01:01Z
- Toolchain: `leanprover/lean4:v4.33.1` — Lean 4.33.1
  (x86_64-unknown-linux-gnu, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Release),
  Lake `5.0.0-src+819816b`; mathlib pinned to
  `0df444a360eaa60ab8c11dca51a86af692955474` in `lean/lake-manifest.json`
- Checkout state: clean (`git status` empty, no stash) — built exactly at this SHA
- Command: `cd lean && lake build`
- Exit code: 0
- Result: Build completed successfully (3020 jobs), 0 errors, 0 warnings
- Explicit sorry/admit/axiom in Definitions/ + Theorems/: 0
- Applies to: P0.1–P0.4 (Lean sources unchanged since `d7a243d`; this SHA only syncs `todo.md`)

## What this SHA adds

- Docs only: `todo.md` sync by the external auditor (documents the cut-open
  rank-semantics closure and the seven missing `AxiomAudit.lean` entries at
  `d7a243d`). No Lean / dependency / paper changes.

## Axiom audit (lake env lean, exit 0)

127 `#print axioms` entries via committed `lean/AxiomAudit.lean` — executed
(not read from an old log); 127/127 produced output. Every line lists only a
subset of `propext` / `Classical.choice` / `Quot.sound`, or no axioms at all
(11 entries). No `sorryAx`, no custom axioms in any dependency closure.

Coverage caveat: 131 public theorems at this SHA vs 127 audit entries; the
auditor flagged seven un-covered new theorems (target 134 entries including
`crk_orderIso`) in `todo.md`. The seven remain unaudited at this SHA; the
audit entry file itself was not changed here.
