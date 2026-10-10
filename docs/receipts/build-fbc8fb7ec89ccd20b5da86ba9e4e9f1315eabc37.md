# Build receipt

- SHA: `fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37`
- Date (UTC): 2026-10-10T13:46:33Z
- Toolchain: Lean 4.33.1 (x86_64-unknown-linux-gnu, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Release); Lake `5.0.0-src+819816b` (mathlib pinned in lean/lake-manifest.json)
- Command: `cd lean && lake build`
- Exit code: 0
- Result: Build completed successfully (3019 jobs), 0 errors, 0 warnings
- Explicit sorry/admit/axiom in Definitions/ + Theorems/: 0

## What this SHA adds

- `lean/Theorems/Thm_PrimeMother_ReturnCombination.lean` gains the P2.1c(v)
  per-block geometric records for the multi-prime packet word:
  `blockRecordsAux` (def, threads the same state as `packetWordAux` and
  records `(left-endpoint label, left endpoint, right endpoint)` per prime
  block), `packetWordAux_append_suffix` (builder output = input ++ suffix),
  `packetWordAux_blocks_elementary` (every recorded block is an elementary
  return of the final packet word), `blockRecordsAux_support` (block
  support length `b - a` equals the corresponding input prime), and
  `packetWord_blocks_elementary` (public version for `packetWord` at the
  base state `[0,1]`). All 4 new theorems proved with 0 sorry; each carries
  a docstring locating it in the forward construction of paper
  `thm:return-combination` (ii).
- `lean/AxiomAudit.lean` gains the 4 new `#print axioms` entries
  (P2.1c section header (40) → (44)).

## Axiom audit (lake env lean, exit 0)

94 `#print axioms` entries via committed `lean/AxiomAudit.lean`; every line
lists only `propext` / `Classical.choice` / `Quot.sound` (or no axioms).
New entries:

```
'PrimeMother.packetWordAux_append_suffix' depends on axioms: [propext]
'PrimeMother.packetWordAux_blocks_elementary' depends on axioms: [propext, Quot.sound]
'PrimeMother.blockRecordsAux_support' depends on axioms: [propext, Quot.sound]
'PrimeMother.packetWord_blocks_elementary' depends on axioms: [propext, Quot.sound]
```

No sorryAx in any dependency closure.
