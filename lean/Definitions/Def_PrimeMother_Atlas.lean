/-
Prime-Distribution Birth Mother — Regular atlas and birth rule.

Formalizes §3 (Regular atlas inheritance) and §4 (One-direction provenance
and mother relation).

A regular Pi-atlas on H is a tiling of H by r >= 2 consecutive copies of Pi.
On the linear homogeneous source this exists iff rk(Pi) divides rk(H) with
quotient r >= 2 (Lemma, Rank of an atlas).

The birth rule: Birth(H) = 1 iff no earlier birth Pi admits a regular
atlas on H.  Births are computed in increasing rank order; the birth
ledger B_{<H} is the set of earlier births.
-/

import Definitions.Def_PrimeMother_Source

open Classical

namespace PrimeMother

/-- A regular Pi-atlas on H exists iff Pi tiles H with r >= 2 blocks.
    By the atlas-rank lemma this is equivalent to
    rk Pi divides rk H with rk H / rk Pi >= 2. -/
def HasRegAtlas (H Pi : Prefix) : Prop :=
  Exists (fun r : Nat => 2 <= r /\ rk Pi * r = rk H)

/-- Atlas-rank lemma (forward): an r-block atlas gives rk(H) = r * rk(Pi). -/
theorem atlas_rank_fwd {H Pi : Prefix} (h : HasRegAtlas H Pi) :
    Exists (fun r : Nat => 2 <= r /\ rk H = r * rk Pi) := by
  obtain ⟨r, hr, heq⟩ := h
  exact ⟨r, hr, by unfold rk at heq ⊢; rw [Nat.mul_comm]; exact heq.symm⟩

/-- Atlas-rank lemma (converse): the rank equation gives an atlas. -/
theorem atlas_rank_bwd {H Pi : Prefix} {r : Nat} (hr : 2 <= r)
    (heq : rk Pi * r = rk H) : HasRegAtlas H Pi :=
  ⟨r, hr, heq⟩

/-- Mother relation: Pi is an ancestral mother of H iff a regular
    Pi-atlas on H exists. -/
def Mother (Pi H : Prefix) : Prop := HasRegAtlas H Pi

/-- The one-direction birth rule.
    Birth(H) = 1 iff no earlier birth Pi is a mother of H.
    n+2 is born iff no m < n+2 with birth m gives a regular atlas on n+2.
    Defined by strong recursion on Nat. -/
noncomputable def birth (n : Nat) : Bool :=
  Nat.strongRecOn n (motive := fun _ => Bool) fun n ih =>
    match n with
    | 0 => false
    | 1 => false
    | (n + 2) =>
      if Exists (fun m : Nat => Exists (fun h : m < n + 2 => (ih m h : Bool) = true /\ HasRegAtlas (n + 2) m))
      then false else true

/-- The one-edge prefix E is not a birth. -/
theorem birth_E : birth E = false := by
  unfold birth E Nat.strongRecOn
  rw [WellFounded.fix_eq]

/-- The root is not a birth. -/
theorem birth_root : birth root = false := by
  unfold birth root Nat.strongRecOn
  rw [WellFounded.fix_eq]

/-- Unfolding lemma for the birth rule at n + 2.
    Technical: requires showing the WellFounded.fix applications equal birth
    applications, and the two Exists formulations are propositionally equal.
    The mathematical content (birth_iff_prime) does not depend on the proof
    technique, only on this unfolding equation. -/
theorem birth_succ_succ (n : Nat) :
    birth (n + 2) =
      (if Exists (fun m : Nat => m < n + 2 /\ birth m = true /\ HasRegAtlas (n + 2) m)
       then false else true) := by
  unfold birth Nat.strongRecOn
  rw [WellFounded.fix_eq]
  -- The well-founded unfolding at n + 2 reduces (definitionally) to the
  -- third match branch, whose predecessor function is again `birth`.
  show (if Exists (fun (m : Nat) => Exists (fun (_ : m < n + 2) =>
        (birth m : Bool) = true /\ HasRegAtlas (n + 2) m))
        then false else true) =
    (if Exists (fun m : Nat => m < n + 2 /\ birth m = true /\ HasRegAtlas (n + 2) m)
     then false else true)
  congr 1
  apply propext
  constructor
  · rintro ⟨m, h, hbm, hatlas⟩
    exact ⟨m, h, hbm, hatlas⟩
  · rintro ⟨m, h, hbm, hatlas⟩
    exact ⟨m, h, hbm, hatlas⟩

end PrimeMother
