# Build receipt

- SHA: `f0ae0fa994ea3e7e1d19ff0bda4dc6eb3a6eb18`
- Date (UTC): 2026-10-10T12:07:20Z
- Toolchain: Lean 4.33.1 (x86_64-unknown-linux-gnu, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Release); Lake `5.0.0-src+819816b` (mathlib pinned in lean/lake-manifest.json)
- Command: `cd lean && lake build`
- Exit code: 0
- Result: Build completed successfully (3019 jobs), 0 errors, 0 warnings
- Explicit sorry/admit/axiom in Definitions/ + Theorems/ + AxiomAudit: 0

## What this SHA adds

- `lean/Theorems/Thm_PrimeMother_ReturnCombination.lean` gains the
  P2.1c(iv) `[2,3]` two-prime packet regression — the smallest nontrivial
  distinct-prime case, mirroring `packetWord_two_two`:
  - `packetWord_two_three`: `packetWord [2,3] = [0,1,0,2,1]` (unfold + rfl)
  - `packetWord_two_three_return_two` / `packetWord_two_three_return_three`:
    elementary returns of classes 0 and 1 at endpoints (0,2) and (1,4),
    support lengths 2 and 3 (the input primes)
  - `packetWord_two_three_occ_two` / `packetWord_two_three_occ_three`:
    each class occurs exactly twice
  - `packetWord_two_three_packet`: `ReturnPacket (packetWord [2,3]) = {0,1}`
    (complete packet, no other two-occurrence class)
  - `packetWord_two_three_simpleReturn`: no class occurs 3+ times
  - `packetWord_two_three_classify`: no extra elementary returns — every
    elementary return is one of the two prime-class returns
  - `packetWord_two_three_distinct_support`: the two class returns have
    distinct support lengths 2 vs 3, feeding
    `sector_of_distinct_support_lengths`
  - `packetWord_two_three_adjacent`: the two returns overlap, so the packet
    overlap graph is the single edge (path graph on two vertices)
- `lean/AxiomAudit.lean` gains the 10 new `#print axioms` entries; the
  stale "Return combination P2.1c (17)" section comment is corrected to
  (32) (22 pre-existing + 10 new).

## Axiom audit (lake env lean, exit 0)

82 `#print axioms` entries via committed `lean/AxiomAudit.lean`
(6+5+3+5+7+3+5+9+7+32, matching the section comments); every line lists
only `propext` / `Classical.choice` / `Quot.sound` (or no axioms). New
entries:

```
'PrimeMother.packetWord_two_three' depends on axioms: [Quot.sound]
'PrimeMother.packetWord_two_three_return_two' depends on axioms: [propext, Quot.sound]
'PrimeMother.packetWord_two_three_return_three' depends on axioms: [propext, Quot.sound]
'PrimeMother.packetWord_two_three_occ_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_two_three_occ_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_two_three_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_two_three_simpleReturn' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_two_three_classify' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_two_three_distinct_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeMother.packetWord_two_three_adjacent' depends on axioms: [propext, Quot.sound]
```

No sorryAx in any dependency closure.
