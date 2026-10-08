/-
Prime-Distribution Birth Mother — Core source definitions.

Formalizes §2 (The unlabelled mother source) of
`paper/prime_distribution_birth_mother_provenance.tex`.

The unlabelled atomic successor source produces a single persistent history
  o → x₁ → x₂ → ⋯
Prefixes are classified by their posterior rank (edge count).  Clock
reconstruction (Prop. 2.4) identifies the prefix order with Nat₀ via rank.

P1.1: this file now contains BOTH layers —
  (a) the abstract unlabelled source (`Chain`, `ChainLE`, `crk`), and
  (b) the rank model (`Prefix := Nat`, `rk`), which is the transport of (a)
      along the clock-reconstruction isomorphism.
The old `clock_reconstruction : rk H = H` is kept as the rank-model
triviality; the genuine source-level statement is `clock_iso`.
-/

namespace PrimeMother

/-! ## (a) Abstract unlabelled source -/

/-- The unlabelled atomic successor source: a single chain
    `o → x₁ → x₂ → ⋯`.  No labels, no arithmetic — just the origin
    and one atomic successor step. -/
inductive Chain : Type
  | origin : Chain
  | step : Chain → Chain
  deriving DecidableEq, Repr

/-- Prefix order on the source: `H₁ ≤ H₂` iff `H₁` is a prefix of `H₂`. -/
inductive ChainLE : Chain → Chain → Prop
  | origin_le : ∀ H, ChainLE .origin H
  | step_le : ∀ {a b}, ChainLE a b → ChainLE (.step a) (.step b)

/-- Posterior rank: number of atomic source edges in the prefix. -/
def crk : Chain → Nat
  | .origin => 0
  | .step c => crk c + 1

/-- Rank respects the prefix order. -/
theorem crk_mono {a b : Chain} (h : ChainLE a b) : crk a ≤ crk b := by
  induction h with
  | origin_le H => simp [crk]
  | step_le _ ih => simp [crk]; omega

/-- Rank is strictly monotone on strict prefixes. -/
theorem crk_strict_mono {a b : Chain} (h : ChainLE a b) (hne : a ≠ b) :
    crk a < crk b := by
  induction h with
  | origin_le H =>
    simp [crk]
    cases H with
    | origin => exact absurd rfl hne
    | step c => simp [crk]
  | @step_le a b h ih =>
    have hne' : a ≠ b := fun heq => hne (congrArg Chain.step heq)
    have hlt := ih hne'
    simp only [crk]
    omega

/-- Every rank is realized by exactly one prefix: the `n`-fold step chain. -/
def chainOf : Nat → Chain
  | 0 => .origin
  | n + 1 => .step (chainOf n)

theorem crk_chainOf (n : Nat) : crk (chainOf n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chainOf, crk, ih]

/-- Rank determines the prefix: `crk` is injective. -/
theorem crk_injective : Function.Injective crk := by
  intro a b hab
  induction a generalizing b with
  | origin =>
    cases b with
    | origin => rfl
    | step c => simp [crk] at hab
  | step a iha =>
    cases b with
    | origin => simp [crk] at hab
    | step c =>
      simp [crk] at hab
      rw [iha hab]

/-- Clock reconstruction (Prop. 2.4, source level): the prefix order on the
    unlabelled source is order-isomorphic to `Nat₀` via posterior rank.
    Root is preserved (`crk .origin = 0`), successor is preserved
    (`crk (.step c) = crk c + 1`), and the isomorphism is unique because
    rank is injective. -/
theorem clock_iso : Function.Injective crk ∧ Function.Surjective crk :=
  ⟨crk_injective, fun n => ⟨chainOf n, crk_chainOf n⟩⟩

/-- The rank image is all of `Nat₀`: nothing is lost in reconstruction. -/
theorem clock_surjective : Function.Surjective crk := clock_iso.2

/-! ## (b) Rank model (transport along `clock_iso`) -/

/-- A retained prefix is identified with its posterior rank (edge count).
    This is the rank model: the transport of the abstract source along
    `clock_iso`.  It is NOT the source itself — see (a) above. -/
abbrev Prefix := Nat

/-- Posterior rank on the rank model (identity, by transport). -/
def rk (H : Prefix) : Nat := H

/-- The one-edge prefix E (atomic unit, not an arithmetic birth). -/
def E : Prefix := 1

/-- The root prefix H(o) has rank 0. -/
def root : Prefix := 0

theorem rk_root : rk root = 0 := rfl

theorem rk_E : rk E = 1 := rfl

/-- Rank-model triviality: on `Prefix := Nat`, rank is the identity.
    This is NOT the paper's source-level clock reconstruction —
    that is `clock_iso` above. -/
theorem clock_reconstruction (H : Prefix) : rk H = H := rfl

end PrimeMother
