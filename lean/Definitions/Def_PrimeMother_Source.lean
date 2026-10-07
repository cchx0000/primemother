/-
Prime-Distribution Birth Mother — Core source definitions.

Formalizes §2 (The unlabelled mother source) of
`paper/prime_distribution_birth_mother_provenance.tex`.

The unlabelled atomic successor source produces a single persistent history
  o → x₁ → x₂ → ⋯
Prefixes are classified by their posterior rank (edge count).  Clock
reconstruction (Prop. 2.4) identifies the prefix order with ℕ₀ via rank.
-/

namespace PrimeMother

/-- A retained prefix is identified with its posterior rank (edge count).
    Clock reconstruction: Pref(R) ∪ {H(o)} ≅ ℕ₀ via H ↦ rk(H). -/
abbrev Prefix := ℕ

/-- Posterior rank: number of atomic source edges in the prefix. -/
def rk (H : Prefix) : ℕ := H

/-- The one-edge prefix E (atomic unit, not an arithmetic birth). -/
def E : Prefix := 1

/-- The root prefix H(o) has rank 0. -/
def root : Prefix := 0

theorem rk_root : rk root = 0 := rfl

theorem rk_E : rk E = 1 := rfl

/-- Clock reconstruction: rank is the order isomorphism Pref ≅ ℕ₀. -/
theorem clock_reconstruction (H : Prefix) : rk H = H := rfl

end PrimeMother
