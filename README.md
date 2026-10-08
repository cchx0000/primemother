# primemother

Lean 4 formalization of **"The Prime-Distribution Birth Mother: Single-Prime,
Finite-Combination, and All-Prime Return Births"**
(`paper/prime_distribution_birth_mother_provenance.tex`).

## What is formalized

The §§2–6 core chain (unary prime-birth model):

| Paper section | Lean module | Status |
|---|---|---|
| §2 Atomic successor source, clock reconstruction | `Definitions/Def_PrimeMother_Source.lean` | Definitions (rank model) |
| §3 Regular atlas, atlas-rank lemma | `Definitions/Def_PrimeMother_Atlas.lean` | Definitions + birth rule |
| §4 Birth ledger, mother relation, one-direction sector | `Definitions/Def_PrimeMother_Atlas.lean` | `HasRegAtlas`, `Mother`, `birth` |
| §5 Exact prime-birth theorem | `Theorems/Thm_PrimeMother_PrimeBirth.lean` | `birth_iff_prime` proved, 0 sorry |
| Regression tests | `Theorems/Thm_PrimeMother_Regression.lean` | 0/1/2/3/4/6/9/25 proved |

**Main theorem** (`birth_iff_prime`): for every `n ≥ 2`,
`birth n = true ↔ Nat.Prime n` — the one-direction primitive births have
posterior ranks exactly equal to the primes.

**Scope note (honest):** the current formalization is a *rank model*
(`Prefix := Nat`, `rk H := H`). The abstract unlabelled source layer
(§2's source → Nat equivalence) is not yet formalized; see `todo.md` P1.1.
Paper §§7–22 (finite return packets, boundary, obstructions) are not yet
implemented; see `todo.md` P2.

## Build

Fixed toolchain: Lean `v4.33.1`, mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

```bash
cd lean
lake build        # full build (default target: Theorems)
```

Verified: `lake build` passes with 0 errors, 0 `sorry` in the library.

## Axiom audit

`#print axioms` on `birth_E`, `birth_root`, `birth_succ_succ`,
`birth_iff_no_earlier_mother`, `birth_iff_prime` shows only Lean's three
standard axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`.

## Roadmap

See `todo.md` (maintained by the external auditor; read-only for contributors).
P0 (reproducible unary model) is complete. P1/P2 cover semantics, README/CI,
and the paper's finite-return / boundary conclusions.
