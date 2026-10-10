/-
Prime-Distribution Birth Mother — Descent on return packets (P2.2).

Paper: Theorem (Arbitrary finite distinct-prime return birth)
`thm:return-combination`, direction (iii), and the connected-deletion
step used in `prop:boundary-unary-descent` / `cor:boundary-mixed-fibres`
("choose a spanning tree and remove one of its leaves"; "split an
endpoint class belonging to a nonroot leaf ... the remaining induced
support graph stays connected ... the atlas ledger of every remaining
return is unchanged").

The descent arrow is internal to the source presentation: splitting a
two-occurrence endpoint class removes one return while leaving the
atomic interval and every other class unchanged. A deletion
  d_i(q; J) := (q; J \ {J_i})
is admissible when the remaining intersection (overlap) graph is
connected.

This file (first descent unit): spanning-tree infrastructure for the
overlap graph `PacketAdjacent`, the split-endpoint-class source
operation, and the core preservation lemma — deleting a non-root
spanning-tree leaf leaves every remaining elementary return unchanged,
and the restricted parent map is still a spanning tree of the remaining
overlap graph (so the remaining intersection graph stays connected).
The full tower terminating at any designated unary member, and the
same-shadow mixed-fibre contrasts, are later rounds.
-/

import Definitions.Def_PrimeMother_ReturnPacket
import Mathlib.Tactic

namespace PrimeMother

/-- A spanning tree of the overlap graph `PacketAdjacent w` over the finite
    packet vertex set `V`, rooted at the designated return `r`. Witnessed
    by a parent function plus a depth certificate: every non-root vertex
    has its parent inside `V`, adjacent to it in the overlap graph, and
    strictly closer to the root. (Paper: "choose a spanning tree" of the
    intersection graph.) -/
def IsOverlapSpanningTree (w : List Nat) (V : Finset Nat)
    (parent : Nat → Nat) (r : Nat) : Prop :=
  V ⊆ ReturnPacket w ∧
  r ∈ V ∧
  parent r = r ∧
  (∀ v ∈ V, v ≠ r → parent v ∈ V ∧ PacketAdjacent w (parent v) v) ∧
  ∃ depth : Nat → Nat, depth r = 0 ∧
    ∀ v ∈ V, v ≠ r → depth (parent v) + 1 = depth v

/-- A non-root leaf of the spanning tree: a vertex of `V`, different from
    the root, which is no other vertex's parent. The paper's descent
    always deletes such a leaf of a spanning tree rooted at the
    designated return. -/
def IsTreeLeaf (V : Finset Nat) (parent : Nat → Nat) (r v : Nat) : Prop :=
  v ∈ V ∧ v ≠ r ∧ ∀ u ∈ V, parent u ≠ v

/-- Split the first occurrence of class `v`, relabelling it `fresh`.
    Auxiliary for `splitClass`; the recursion stops after the first hit,
    so at most one position changes. -/
def splitFirst (w : List Nat) (v fresh : Nat) : List Nat :=
  match w with
  | [] => []
  | x :: xs => if x = v then fresh :: xs else x :: splitFirst xs v fresh

/-- The paper's split-endpoint-class source operation (skeleton):
    split the two-occurrence class `v` by relabelling its first
    occurrence with the fresh label `listMax w + 1`. The atomic interval
    (word length and every other position) and every other class are
    untouched; a two-occurrence class becomes two singletons. -/
def splitClass (w : List Nat) (v : Nat) : List Nat :=
  splitFirst w v (listMax w + 1)

/-- Splitting preserves the word length (the atomic interval is
    unchanged). -/
theorem splitFirst_length (w : List Nat) (v fresh : Nat) :
    (splitFirst w v fresh).length = w.length := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxv : x = v <;> simp [splitFirst, hxv, ih]

/-- The split operation preserves the word length. -/
theorem splitClass_length (w : List Nat) (v : Nat) :
    (splitClass w v).length = w.length := by
  unfold splitClass
  rw [splitFirst_length]

/-- Pointwise: splitting class `v` (fresh label `fresh`) does not affect
    any position's being labelled `c`, for `c ≠ v` and `c ≠ fresh`. -/
theorem get?_splitFirst {w : List Nat} {v fresh c : Nat}
    (hcv : c ≠ v) (hcf : c ≠ fresh) :
    ∀ i : Nat, (splitFirst w v fresh)[i]? = some c ↔ w[i]? = some c := by
  induction w with
  | nil =>
    intro i
    simp [splitFirst]
  | cons x xs ih =>
    intro i
    cases i with
    | zero =>
      simp only [splitFirst]
      by_cases hxv : x = v
      · rw [if_pos hxv]
        show (some fresh = some c) ↔ (some x = some c)
        constructor
        · intro h
          exact absurd (Option.some_inj.mp h).symm hcf
        · intro h
          have hxc : x = c := Option.some_inj.mp h
          exact absurd (hxv.symm.trans hxc).symm hcv
      · rw [if_neg hxv]
        show (some x = some c) ↔ (some x = some c)
        exact Iff.rfl
    | succ n =>
      simp only [splitFirst]
      by_cases hxv : x = v
      · rw [if_pos hxv]
        show (xs[n]? = some c) ↔ (xs[n]? = some c)
        exact Iff.rfl
      · rw [if_neg hxv]
        show ((splitFirst xs v fresh)[n]? = some c) ↔ (xs[n]? = some c)
        exact ih n

/-- The split only touches class `v`; every other class keeps exactly
    its occurrences. (`c ≤ listMax w` keeps the fresh label out of range
    of `c`.) -/
theorem occurrences_splitClass {w : List Nat} {v c : Nat}
    (hcv : c ≠ v) (hcle : c ≤ listMax w) :
    occurrences (splitClass w v) c = occurrences w c := by
  have hcf : c ≠ listMax w + 1 := by omega
  have hpt := get?_splitFirst (w := w) (v := v) (fresh := listMax w + 1)
    (c := c) hcv hcf
  unfold splitClass occurrences
  rw [splitFirst_length]
  apply Finset.ext
  intro i
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [hpt i]

/-- The running max does not drop when the first `v` is relabelled by a
    label above the current max. -/
theorem listMax_le_listMax_splitFirst (w : List Nat) (v fresh : Nat)
    (hfresh : listMax w < fresh) :
    listMax w ≤ listMax (splitFirst w v fresh) := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    simp only [listMax_cons, splitFirst] at hfresh ⊢
    by_cases hxv : x = v
    · rw [if_pos hxv]
      simp only [listMax_cons]
      omega
    · rw [if_neg hxv]
      simp only [listMax_cons]
      have hxs : listMax xs < fresh := by
        have hle : listMax xs ≤ max x (listMax xs) := Nat.le_max_right _ _
        omega
      have hle := ih hxs
      omega

/-- The running max does not drop under the split operation. -/
theorem listMax_le_listMax_splitClass (w : List Nat) (v : Nat) :
    listMax w ≤ listMax (splitClass w v) := by
  unfold splitClass
  exact listMax_le_listMax_splitFirst w v _ (by omega)

/-- Splitting the class `v` leaves every other class's elementary
    returns unchanged (for `c ≤ listMax w`, so the fresh label is out of
    range). This is the "atlas ledger of every remaining return is
    unchanged" half of the paper's descent step. -/
theorem isElementaryReturn_splitClass {w : List Nat} {v c a b : Nat}
    (hcv : c ≠ v) (hcle : c ≤ listMax w) :
    IsElementaryReturn (splitClass w v) c a b ↔
      IsElementaryReturn w c a b := by
  have hcf : c ≠ listMax w + 1 := by omega
  have hpt := get?_splitFirst (w := w) (v := v) (fresh := listMax w + 1)
    (c := c) hcv hcf
  unfold splitClass IsElementaryReturn
  rw [splitFirst_length]
  constructor
  · rintro ⟨hab, hblen, ha, hb, hmid⟩
    refine ⟨hab, hblen, (hpt a).mp ha, (hpt b).mp hb, ?_⟩
    intro k hak hkb
    exact ((hpt k).not).mp (hmid k hak hkb)
  · rintro ⟨hab, hblen, ha, hb, hmid⟩
    refine ⟨hab, hblen, (hpt a).mpr ha, (hpt b).mpr hb, ?_⟩
    intro k hak hkb
    exact ((hpt k).not).mpr (hmid k hak hkb)

/-- Every vertex of a spanning tree reaches the root by iterating the
    parent map `depth v` times. This is the explicit connectivity
    certificate carried by the tree. -/
theorem treeWalk_reaches_root {V : Finset Nat} {parent : Nat → Nat}
    {r : Nat} {depth : Nat → Nat}
    (hpar : ∀ v ∈ V, v ≠ r → parent v ∈ V)
    (hd0 : depth r = 0)
    (hdsucc : ∀ v ∈ V, v ≠ r → depth (parent v) + 1 = depth v)
    {v : Nat} (hv : v ∈ V) :
    parent^[depth v] v = r := by
  have key : ∀ n : Nat, ∀ v : Nat, v ∈ V → depth v = n →
      parent^[n] v = r := by
    intro n
    induction n with
    | zero =>
      intro v hv hdv
      by_cases hvr : v = r
      · subst hvr
        simp
      · exfalso
        have h := hdsucc v hv hvr
        omega
    | succ n ih =>
      intro v hv hdv
      by_cases hvr : v = r
      · subst hvr
        rw [hd0] at hdv
        omega
      · have hpuV := hpar v hv hvr
        have hdep : depth (parent v) = n := by
          have h := hdsucc v hv hvr
          omega
        have hih := ih (parent v) hpuV hdep
        calc parent^[n + 1] v = parent^[n.succ] v := rfl
          _ = parent^[n] (parent v) := Function.iterate_succ_apply _ _ _
          _ = r := hih
  exact key (depth v) v hv rfl

/-- Core descent preservation (paper `thm:return-combination` (iii) /
    `prop:boundary-unary-descent` connected-deletion step): deleting a
    non-root spanning-tree leaf — realized at the source level by
    splitting its endpoint class — leaves every remaining class's
    elementary returns unchanged, and the restricted parent map is still
    a spanning tree of the remaining overlap graph (hence the remaining
    intersection graph stays connected). -/
theorem descent_leaf_delete {w : List Nat} {V : Finset Nat}
    {parent : Nat → Nat} {r v : Nat}
    (htree : IsOverlapSpanningTree w V parent r)
    (hleaf : IsTreeLeaf V parent r v) :
    IsOverlapSpanningTree (splitClass w v) (V.erase v) parent r ∧
    ∀ c ∈ V.erase v, ∀ a b : Nat,
      IsElementaryReturn (splitClass w v) c a b ↔
        IsElementaryReturn w c a b := by
  obtain ⟨hsub, hrV, hpr, hadj, depth, hd0, hdsucc⟩ := htree
  obtain ⟨_hvV, hvne, hnol⟩ := hleaf
  constructor
  · -- The restricted parent map is still a spanning tree.
    refine ⟨?_, ?_, ?_, ?_, depth, hd0, ?_⟩
    · -- Remaining vertices are still a packet after the split.
      intro c hc
      rw [Finset.mem_erase] at hc
      obtain ⟨hcv, hcV⟩ := hc
      have hcP := hsub hcV
      simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at hcP
      obtain ⟨hc_lt, hc_card⟩ := hcP
      have hcle : c ≤ listMax w := by omega
      simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · have hle := listMax_le_listMax_splitClass w v
        omega
      · rw [occurrences_splitClass hcv hcle]
        exact hc_card
    · -- The root is not the deleted leaf.
      rw [Finset.mem_erase]
      exact ⟨Ne.symm hvne, hrV⟩
    · exact hpr
    · -- Parents stay inside the remaining set, with overlap adjacency.
      intro u hu hune
      rw [Finset.mem_erase] at hu
      obtain ⟨huv, huV⟩ := hu
      obtain ⟨hpuV, hadj_u⟩ := hadj u huV hune
      have hpu_ne_v : parent u ≠ v := fun hcon => hnol u huV hcon
      have hu_le : u ≤ listMax w := by
        have h := hsub huV
        simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at h
        omega
      have hpu_le : parent u ≤ listMax w := by
        have h := hsub hpuV
        simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at h
        omega
      refine ⟨Finset.mem_erase.mpr ⟨hpu_ne_v, hpuV⟩, ?_⟩
      unfold PacketAdjacent at hadj_u ⊢
      obtain ⟨hne, a, b, a', b', h1, h2, hov⟩ := hadj_u
      exact ⟨hne, a, b, a', b',
        (isElementaryReturn_splitClass hpu_ne_v hpu_le).mpr h1,
        (isElementaryReturn_splitClass huv hu_le).mpr h2, hov⟩
    · -- The depth certificate is unchanged.
      intro u hu hune
      rw [Finset.mem_erase] at hu
      exact hdsucc u hu.2 hune
  · -- Remaining elementary returns are unchanged.
    intro c hc a b
    rw [Finset.mem_erase] at hc
    obtain ⟨hcv, hcV⟩ := hc
    have hcle : c ≤ listMax w := by
      have h := hsub hcV
      simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at h
      omega
    exact isElementaryReturn_splitClass hcv hcle

end PrimeMother
