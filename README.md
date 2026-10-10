# primemother

Lean 4 formalization of **"The Prime-Distribution Birth Mother: Single-Prime,
Finite-Combination, and All-Prime Return Births"**
(`paper/prime_distribution_birth_mother_provenance.tex`).

## What is formalized

The §§2–6 core chain (unary prime-birth model) plus the P2 return-word /
packet / descent infrastructure:

| Paper section | Lean module | Status |
|---|---|---|
| §2 Atomic successor source, clock reconstruction | `Definitions/Def_PrimeMother_Source.lean` | Abstract `Chain`/`ChainLE`/`crk`, `clock_iso`, order-iso |
| §3 Regular atlas, atlas-rank lemma | `Definitions/Def_PrimeMother_Atlas.lean` | Definitions + birth rule + block tilings + `BirthLedger`/`BirthProvenance` |
| §4 Birth ledger, mother relation, one-direction sector | `Definitions/Def_PrimeMother_Atlas.lean` | `HasRegAtlas`, `Mother`, `birth`, `QualifiedMother` |
| §5 Exact prime-birth theorem | `Theorems/Thm_PrimeMother_PrimeBirth.lean` | `birth_iff_prime` proved, 0 sorry |
| Distribution (Nat form) | `Theorems/Thm_PrimeMother_Distribution.lean` | `birthCount_eq_primeCounting`: birth count = `Nat.primeCounting`; Nat only, no real-measure identity |
| Regression tests | `Theorems/Thm_PrimeMother_Regression.lean` | 0/1/2/3/4/6/9/25 proved |
| P2.1 Return words (normal form) | `Definitions/Def_PrimeMother_ReturnWord.lean` | `IsReturnWord` inductive + basic theory |
| P2.1 Return packets, overlap graph | `Definitions/Def_PrimeMother_ReturnPacket.lean` | Elementary returns, simple-return sector, `Packet`, cut-open rank bridge (`sector_of_distinct_support_lengths`) |
| P2.1 Return combination | `Theorems/Thm_PrimeMother_ReturnCombination.lean` | `spine`/`singlePrimeWord` infrastructure; exact packet for sorted ≥2 input (`packetWord_packet_exact`, `isSimpleReturn_packetWord`); `[2,2]` regression: `packetWord = [0,1,0,1]` |
| P2.2 Descent | `Theorems/Thm_PrimeMother_ReturnDescent.lean` | Conditional single-step descent (`descent_leaf_delete` under overlap spanning tree, `treeWalk_reaches_root`); full-packet deletion / termination tower still open |

**Main theorem** (`birth_iff_prime`): for every `n ≥ 2`,
`birth n = true ↔ Nat.Prime n` — the one-direction primitive births have
posterior ranks exactly equal to the primes.

**Scope note (honest):** the abstract unlabelled source layer is partially
formalized — the canonical `Chain` model with `ChainLE`/`crk`, `clock_iso`,
and order-isomorphism results (`Def_PrimeMother_Source.lean`) — but the
general paper source ↔ `Chain` transport and the source → atlas/birth/ledger
transport are still open; see `todo.md` P1.1. The old `Prefix := Nat` rank
model is retained only as transport. Paper §§7–22 beyond the current P2
items (mixed fibres, boundaries, obstructions) are not yet implemented;
see `todo.md` P2.

## Build

Fixed toolchain: Lean `v4.33.1`, mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

```bash
cd lean
lake build        # full build (default target: Theorems)
```

Verified: `lake build` passes with 0 errors, 0 warnings, 0 `sorry` in the
library. Per-SHA build receipts (SHA, versions, jobs, exit code, axiom
output) live in [`docs/receipts/`](docs/receipts/).

## Axiom audit

Committed audit entry [`lean/AxiomAudit.lean`](lean/AxiomAudit.lean)
(imports all 9 library modules; run with `cd lean && lake env lean AxiomAudit.lean`
— it is not in the default target). 127 `#print axioms` entries, every line
lists only Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) or no axioms at all. No `sorryAx`, no custom axioms.

## Roadmap

See `todo.md` (maintained by the external auditor; read-only for contributors).
P0 (reproducible unary model) is complete with build receipts. P1 is partially
open (source/atlas transport, uniqueness theorem, ordered ledger, full atlas
family). P2 is underway: P2.1 return words / packets / exact-packet
classification in progress, P2.2 conditional descent in progress, P2.3–P2.5
not yet implemented.
