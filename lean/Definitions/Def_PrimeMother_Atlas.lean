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
import Mathlib.Tactic

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
    Pi-atlas on H exists.
    NOTE (P1.2): this is the BARE atlas relation. It does NOT require
    Pi to be an earlier birth. In particular `Mother 0 0` and
    `Mother 1 2` hold (see below), but 0 and 1 are never birth-mothers.
    The qualified relation is `QualifiedMother`. -/
def Mother (Pi H : Prefix) : Prop := HasRegAtlas H Pi

/-! ## P1.2: Actual tilings, qualified mothers, ledger, provenance

Paper Definition (Regular atlas): an ordered family (K₁,…,Kᵣ), r ≥ 2,
of consecutive segments of H such that
  (i)   every Kⱼ is isomorphic to Π as an ordered atomic path;
  (ii)  adjacent blocks meet only at their common endpoint;
  (iii) the block interiors are pairwise disjoint;
  (iv)  the ordered concatenation of the blocks is all of H.
On the rank model a segment is a rank interval; (i) is "same edge count",
which for linear chains is the path isomorphism. -/

/-- An actual block tiling of H by r consecutive copies of Pi.
    Block j occupies ranks [j * rk Pi, (j+1) * rk Pi). -/
structure AtlasTiling (H Pi : Prefix) where
  r : Nat
  hr : 2 ≤ r
  tile_eq : rk Pi * r = rk H

/-- Left endpoint (inclusive) of block j. -/
def blockLo (Pi : Prefix) (j : Nat) : Nat := j * rk Pi

/-- Right endpoint (exclusive) of block j. -/
def blockHi (Pi : Prefix) (j : Nat) : Nat := (j + 1) * rk Pi

/-- (i) Every block has exactly rk Pi atomic edges. -/
theorem block_edge_count (Pi : Prefix) (j : Nat) :
    blockHi Pi j - blockLo Pi j = rk Pi := by
  unfold blockHi blockLo
  rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]

/-- (ii) Adjacent blocks meet exactly at their common endpoint. -/
theorem block_adjacent_meet (Pi : Prefix) (j : Nat) :
    blockHi Pi j = blockLo Pi (j + 1) := rfl

/-- (iii) Block interiors are pairwise disjoint: for i < j, block i
    ends where block j has not yet begun (needs positive block size). -/
theorem block_interior_disjoint (Pi : Prefix) {i j : Nat} (hij : i < j) :
    blockHi Pi i ≤ blockLo Pi j := by
  unfold blockHi blockLo
  exact Nat.mul_le_mul_right _ (by omega)

/-- (iv) The r blocks cover [0, rk H): every rank below rk H lies in
    some block (needs positive block size). -/
theorem block_cover {H Pi : Prefix} (T : AtlasTiling H Pi)
    (hpos : 0 < rk Pi) {k : Nat} (hk : k < rk H) :
    ∃ j, j < T.r ∧ blockLo Pi j ≤ k ∧ k < blockHi Pi j := by
  have htile : rk Pi * T.r = rk H := T.tile_eq
  have h1 : k / rk Pi * rk Pi ≤ k := Nat.div_mul_le_self k (rk Pi)
  have h2 : k % rk Pi < rk Pi := Nat.mod_lt k hpos
  have h3 : k / rk Pi * rk Pi + k % rk Pi = k := by
    rw [Nat.mul_comm (k / rk Pi)]; exact Nat.div_add_mod k (rk Pi)
  have h6 : (k / rk Pi + 1) * rk Pi = k / rk Pi * rk Pi + rk Pi := by
    rw [Nat.add_mul, Nat.one_mul]
  refine ⟨k / rk Pi, ?_, by unfold blockLo; exact h1, ?_⟩
  · -- j < T.r
    by_contra hcon
    push Not at hcon
    have h4 : T.r * rk Pi ≤ k / rk Pi * rk Pi :=
      Nat.mul_le_mul_right _ hcon
    have h5 : T.r * rk Pi = rk H := by rw [Nat.mul_comm]; exact htile
    omega
  · -- k < blockHi
    unfold blockHi
    rw [h6]
    omega

/-- The tiling exists iff the multiplicative atlas relation holds.
    This is the rank-model content of the atlas-rank lemma:
    the rank equation specifies the unique linear cuts. -/
theorem tiling_exists_iff {H Pi : Prefix} :
    Nonempty (AtlasTiling H Pi) ↔ HasRegAtlas H Pi := by
  constructor
  · rintro ⟨⟨r, hr, heq⟩⟩
    exact ⟨r, hr, heq⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨⟨r, hr, heq⟩⟩

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

/-- A QUALIFIED mother: Pi is an earlier birth AND a regular Pi-atlas
    tiles H. This is the relation the birth rule actually tests. -/
def QualifiedMother (Pi H : Prefix) : Prop :=
  Pi < H ∧ birth Pi = true ∧ HasRegAtlas H Pi

/-- Qualified mothers are mothers. -/
theorem qualified_is_mother {Pi H : Prefix} (h : QualifiedMother Pi H) :
    Mother Pi H := h.2.2

/-- Boundary: the bare Mother relation holds on 0, but 0 is never
    a qualified mother (birth 0 = false). -/
theorem mother_zero_zero : Mother 0 0 := ⟨2, by omega, by unfold rk; rfl⟩

theorem not_qualified_zero (H : Prefix) : ¬ QualifiedMother 0 H := by
  rintro ⟨_, hbirth, _⟩
  have h0 : birth 0 = false := birth_root
  rw [h0] at hbirth
  exact absurd hbirth (by decide)

/-- Boundary: Mother 1 2 holds bare (1 * 2 = 2), but 1 is never
    a qualified mother (birth 1 = false). -/
theorem mother_one_two : Mother 1 2 := ⟨2, by omega, by unfold rk; rfl⟩

theorem not_qualified_one (H : Prefix) : ¬ QualifiedMother 1 H := by
  rintro ⟨_, hbirth, _⟩
  have h1 : birth 1 = false := birth_E
  rw [h1] at hbirth
  exact absurd hbirth (by decide)

/-- The birth ledger below H: earlier births, the set the birth rule
    scans. Paper §4 "Birth ledger". -/
def BirthLedger (H : Nat) : Set Nat := {m | m < H ∧ birth m = true}

/-- Provenance record for H (paper §4 "Stage provenance"):
    either H is born (all qualified earlier mothers fail) or H is
    blocked (some qualified mother witnesses the atlas). -/
inductive BirthProvenance (H : Nat) : Prop
  | born (hall : ∀ Pi, ¬ QualifiedMother Pi H) (hb : birth H = true) :
      BirthProvenance H
  | blocked (Pi : Nat) (hq : QualifiedMother Pi H) (hb : birth H = false) :
      BirthProvenance H

/-- Every H ≥ 2 has a provenance record: the birth rule decides. -/
theorem provenance_complete (H : Nat) (h2 : 2 ≤ H) :
    BirthProvenance H := by
  obtain ⟨n, rfl⟩ : ∃ n, H = n + 2 := ⟨H - 2, by omega⟩
  by_cases hb : birth (n + 2) = true
  · -- born: no qualified mother can exist
    apply BirthProvenance.born _ hb
    rintro Pi ⟨hlt, hbirth, hatlas⟩
    have hwit : ∃ m, m < n + 2 ∧ birth m = true ∧ HasRegAtlas (n + 2) m :=
      ⟨Pi, hlt, hbirth, hatlas⟩
    rw [birth_succ_succ, if_pos hwit] at hb
    exact absurd hb (by decide)
  · -- blocked: the if took the then-branch, so a witness exists
    have hb' : birth (n + 2) = false := by
      cases h : birth (n + 2) <;> simp_all
    have hb'' : (if ∃ m, m < n + 2 ∧ birth m = true ∧ HasRegAtlas (n + 2) m
        then false else true) = false := by
      rw [← birth_succ_succ]; exact hb'
    have hwit : ∃ m, m < n + 2 ∧ birth m = true ∧ HasRegAtlas (n + 2) m := by
      by_contra hcon
      rw [if_neg hcon] at hb''
      exact absurd hb'' (by decide)
    obtain ⟨m, hm, hbm, ha⟩ := hwit
    exact BirthProvenance.blocked m ⟨hm, hbm, ha⟩ hb'

/-- From a "blocked" provenance one extracts the actual inheritance
    witness: the mother and its atlas tiling. -/
theorem provenance_witness {H Pi : Nat} (hq : QualifiedMother Pi H) :
    Mother Pi H ∧ Nonempty (AtlasTiling H Pi) :=
  ⟨hq.2.2, (tiling_exists_iff).mpr hq.2.2⟩

end PrimeMother
