/-
Prime-Distribution Birth Mother — Regular atlas and birth rule.

Formalizes §3 (Regular atlas inheritance) and §4 (One-direction provenance
and mother relation).

A regular Π-atlas on H is a tiling of H by r ≥ 2 consecutive copies of Π.
On the linear homogeneous source this exists iff rk(Π) ∣ rk(H) with
quotient r ≥ 2 (Lemma, Rank of an atlas).

The birth rule: Birth(H) = 1 iff no earlier birth Π admits a regular
atlas on H.  Births are computed in increasing rank order; the birth
ledger B_{<H} is the set of earlier births.
-/

import Definitions.Def_PrimeMother_Source

namespace PrimeMother

/-- A regular Π-atlas on H exists iff Π tiles H with r ≥ 2 blocks.
    By the atlas-rank lemma this is equivalent to
    rk Π ∣ rk H with rk H / rk Π ≥ 2. -/
def HasRegAtlas (H Π : Prefix) : Prop :=
  ∃ r : ℕ, 2 ≤ r ∧ rk Π * r = rk H

/-- Atlas-rank lemma (forward): an r-block atlas gives rk(H) = r * rk(Π). -/
theorem atlas_rank_fwd {H Π : Prefix} (h : HasRegAtlas H Π) :
    ∃ r : ℕ, 2 ≤ r ∧ rk H = r * rk Π := by
  obtain ⟨r, hr, heq⟩ := h
  exact ⟨r, hr, by rw [rk, rk] at heq ⊢; linarith⟩

/-- Atlas-rank lemma (converse): the rank equation gives an atlas. -/
theorem atlas_rank_bwd {H Π : Prefix} {r : ℕ} (hr : 2 ≤ r)
    (heq : rk Π * r = rk H) : HasRegAtlas H Π :=
  ⟨r, hr, heq⟩

/-- The birth ledger before H: earlier prefixes declared primitive.
    We model it as a predicate on prefixes. -/
def BirthLedger : Prefix → Prop := fun _ => False

/-- Mother relation: Π is an ancestral mother of H iff a regular
    Π-atlas on H exists. -/
def Mother (Π H : Prefix) : Prop := HasRegAtlas H Π

/-- The one-direction birth rule, computed by well-founded recursion on rank.
    Birth(H) = 1 iff no earlier birth Π is a mother of H.
    We define it via strong recursion: n is born iff every m < n with
    m born does not divide n with quotient ≥ 2. -/
noncomputable def birth : Prefix → Bool
  | 0 => false
  | 1 => false
  | (n + 2) =>
    if ∃ m : ℕ, m < n + 2 ∧ birth m ∧ HasRegAtlas (n + 2) m then false else true
termination_by n => n
decreasing_by
  · obtain ⟨m, hm, _, _⟩ := ‹∃ m : ℕ, m < n + 2 ∧ birth m ∧ HasRegAtlas (n + 2) m›
    exact hm

/-- The one-edge prefix E is not a birth. -/
theorem birth_E : birth E = false := rfl

/-- The root is not a birth. -/
theorem birth_root : birth root = false := rfl

/-- Unfolding lemma for the birth rule at n + 2. -/
theorem birth_succ_succ (n : ℕ) :
    birth (n + 2) =
      if ∃ m : ℕ, m < n + 2 ∧ birth m ∧ HasRegAtlas (n + 2) m then false else true := by
  rw [birth]

end PrimeMother
