# Build receipt

- SHA: `23b93b81baac87ab07bd85c70bde5a010f8d329d`
- Date (UTC): 2026-10-10T12:55:56Z
- Toolchain: Lean 4.33.1 (x86_64-unknown-linux-gnu, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Release); Lake `5.0.0-src+819816b` (mathlib pinned in lean/lake-manifest.json)
- Command: `cd lean && lake build`
- Exit code: 0
- Result: Build completed successfully (3019 jobs), 0 errors, 0 warnings
- Explicit sorry/admit/axiom in Definitions/ + Theorems/ + AxiomAudit: 0
- Working tree at build time: clean (`git status --short` empty before commit)

## What this SHA adds

- `lean/Theorems/Thm_PrimeMother_ReturnCombination.lean` gains the
  P2.1c(v) singleton packet word complete classification — paper
  `thm:return-combination`, part (ii), the one-prime case. For p ≥ 2,
  `packetWord [p] = [0,1] ++ (List.range' 2 (p-2) ++ [0])`:
  - `packetWord_singleton_get_interior`: position i (2 ≤ i < p) carries
    the fresh label i
  - `packetWord_singleton_get_p`: position p holds the closing label 0
  - `packetWord_singleton_label`: every position is classified (0 at 0,
    1 at 1, 0 at p, label i at interior i)
  - `packetWord_singleton_occ_unique`: every nonzero class occurs at
    most once
  - `packetWord_singleton_elementary`: elementary return of support
    length p at endpoints (0, p)
  - `packetWord_singleton_occ_zero`: `occurrences (packetWord [p]) 0 =
    {0, p}` (exactly the two endpoints)
  - `packetWord_singleton_packet`: `ReturnPacket (packetWord [p]) = {0}`
    (complete packet, no other two-occurrence class)
  - `packetWord_singleton_simpleReturn`: every recurrent class occurs
    exactly twice
- `lean/AxiomAudit.lean` gains the 8 new `#print axioms` entries; the
  "Return combination P2.1c (32)" section comment is corrected to (40)
  (32 pre-existing + 8 new).

## Axiom audit (lake env lean, exit 0)

90 `#print axioms` entries via committed `lean/AxiomAudit.lean`
(6+5+3+5+7+3+5+9+7+40, matching the section comments); every line lists
only `propext` / `Classical.choice` / `Quot.sound` (or no axioms). New
entries:

```
'PrimeMother.packetWord_singleton_get_interior' depends on axioms: [propext, Quot.sound]
'PrimeMother.packetWord_singleton_get_p' depends on axioms: [propext, Quot.sound]
'PrimeMother.packetWord_singleton_label' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_singleton_occ_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_singleton_elementary' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_singleton_occ_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_singleton_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_singleton_simpleReturn' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No sorryAx in any dependency closure.
