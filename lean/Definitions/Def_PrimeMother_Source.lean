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

import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic

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

/-! ### Order structure of the source -/

/-- Prefix order is reflexive: every prefix is a prefix of itself. -/
private theorem chainLE_refl : ∀ _a : Chain, ChainLE _a _a
  | .origin => ChainLE.origin_le _
  | .step c => ChainLE.step_le (chainLE_refl c)

/-- Prefix order is transitive. -/
private theorem chainLE_trans : ∀ {_a _b _c : Chain}, ChainLE _a _b → ChainLE _b _c → ChainLE _a _c
  | _, _, _, ChainLE.origin_le _, _hbc => ChainLE.origin_le _
  | _, _, _, ChainLE.step_le hab, ChainLE.step_le hbc => ChainLE.step_le (chainLE_trans hab hbc)

/-- A prefix of rank at most `n` sits below the canonical `n`-fold step chain. -/
private theorem chainLE_of_crk_le : ∀ (a : Chain) (n : Nat), crk a ≤ n → ChainLE a (chainOf n) := by
  intro a
  induction a with
  | origin => intro n _; exact ChainLE.origin_le _
  | step c ih =>
    intro n h
    simp only [crk] at h
    match n with
    | 0 => omega
    | n + 1 =>
      have h' : crk c ≤ n := by omega
      exact ChainLE.step_le (ih n h')

/-- Every prefix equals the canonical chain of its rank. -/
private theorem chain_eq_chainOf_crk (b : Chain) : b = chainOf (crk b) :=
  crk_injective (crk_chainOf (crk b)).symm

/-- Clock reconstruction (Prop. 2.4, order form): the prefix order on the
    unlabelled source coincides with the order of posterior ranks.
    Forward: `crk_mono`; backward: a prefix of rank ≤ `n` lies below the
    canonical `n`-fold step chain. -/
theorem chainLE_iff_crk_le {a b : Chain} : ChainLE a b ↔ crk a ≤ crk b := by
  constructor
  · exact crk_mono
  · intro h
    have hle : ChainLE a (chainOf (crk b)) := chainLE_of_crk_le a (crk b) h
    rw [chain_eq_chainOf_crk b]
    exact hle

/-- The prefix relation is the order structure of the source. -/
instance : Preorder Chain where
  le := ChainLE
  le_refl := fun a => chainLE_refl a
  le_trans := fun _a _b _c hab hbc => chainLE_trans hab hbc
  lt_iff_le_not_ge := fun _a _b => Iff.rfl

/-- Clock reconstruction (Prop. 2.4, bundled): the posterior-rank map is an
    order isomorphism `Chain ≃o Nat`.  Root compatibility
    (`crk .origin = 0`) and successor compatibility
    (`crk (.step c) = crk c + 1`) hold definitionally, since `toFun` is `crk`. -/
def crk_orderIso : Chain ≃o Nat where
  toFun := crk
  invFun := chainOf
  left_inv := fun a => (chain_eq_chainOf_crk a).symm
  right_inv := crk_chainOf
  map_rel_iff' := fun {_a _b} => chainLE_iff_crk_le.symm

/-- The bundled isomorphism acts as rank on the nose. -/
theorem crk_orderIso_apply (a : Chain) : crk_orderIso a = crk a := rfl

/-- Root compatibility of the bundled isomorphism. -/
theorem crk_orderIso_origin : crk_orderIso .origin = 0 := rfl

/-- Successor compatibility of the bundled isomorphism. -/
theorem crk_orderIso_step (c : Chain) : crk_orderIso (.step c) = crk_orderIso c + 1 := by
  simp only [crk_orderIso_apply, crk]

/-- Clock reconstruction (Prop. 2.4, uniqueness): any candidate
    `f : Chain → Nat` that preserves the root (`f .origin = 0`) and the
    atomic successor (`f (.step c) = f c + 1`) coincides with posterior rank.
    This is the paper's "any order isomorphism preserving the root and
    atomic successor must give the same values". -/
theorem crk_unique {f : Chain → Nat} (hroot : f .origin = 0)
    (hsucc : ∀ c, f (.step c) = f c + 1) : f = crk := by
  funext a
  induction a with
  | origin => rw [hroot]; rfl
  | step c ih => rw [hsucc]; simp [crk, ih]

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
