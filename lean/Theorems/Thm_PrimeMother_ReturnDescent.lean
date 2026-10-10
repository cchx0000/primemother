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

/-!
## P2.2 unit 2: exact packet deletion equation

The conditional preservation above works for any `V ⊆ ReturnPacket w`.
For a full packet we get the exact equation: splitting a packet class
`v` deletes exactly `v` from the packet (the two occurrences of `v`
become singletons — one keeps the label `v`, one takes the fresh label
— so neither label has two occurrences afterwards), with packet
cardinality dropping by exactly one.
-/

/-- After splitting, the positions labelled `fresh` are exactly the first
    occurrence of `v` (provided `fresh` does not occur in `w`). -/
theorem getElem?_splitFirst_fresh {w : List Nat} {v fresh : Nat}
    (hfresh : ∀ i : Nat, w[i]? ≠ some fresh) (i : Nat) :
    (splitFirst w v fresh)[i]? = some fresh ↔
      (w[i]? = some v ∧ ∀ j, j < i → w[j]? ≠ some v) := by
  induction w generalizing i with
  | nil => simp [splitFirst]
  | cons x xs ih =>
    have hfx : ∀ k : Nat, xs[k]? ≠ some fresh := fun k => hfresh (k + 1)
    cases i with
    | zero =>
      by_cases hxv : x = v
      · unfold splitFirst
        rw [if_pos hxv, List.getElem?_cons_zero]
        constructor
        · intro _
          exact ⟨by rw [List.getElem?_cons_zero, hxv], fun j hj => absurd hj (by omega)⟩
        · intro _; rfl
      · unfold splitFirst
        rw [if_neg hxv, List.getElem?_cons_zero]
        constructor
        · intro h
          have hxf : x = fresh := Option.some_inj.mp h
          exact absurd hxf (fun he => hfresh 0 (by rw [he]; rfl))
        · rintro ⟨h1, -⟩
          rw [List.getElem?_cons_zero] at h1
          exact absurd (Option.some_inj.mp h1) hxv
    | succ n =>
      by_cases hxv : x = v
      · unfold splitFirst
        rw [if_pos hxv]
        have hcons : (fresh :: xs)[n + 1]? = xs[n]? := rfl
        rw [hcons]
        constructor
        · intro h
          exact absurd h (hfx n)
        · rintro ⟨-, h2⟩
          have h0 := h2 0 (Nat.zero_lt_succ n)
          rw [List.getElem?_cons_zero] at h0
          exact absurd hxv (fun he => h0 (by rw [he]))
      · unfold splitFirst
        rw [if_neg hxv]
        have hcons : (x :: splitFirst xs v fresh)[n + 1]? = (splitFirst xs v fresh)[n]? := rfl
        have wcons : (x :: xs)[n + 1]? = xs[n]? := rfl
        rw [hcons, wcons, ih hfx n]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun j hj => ?_⟩
          cases j with
          | zero =>
            rw [List.getElem?_cons_zero]
            intro hc
            exact hxv (Option.some_inj.mp hc)
          | succ m =>
            have jm : (x :: xs)[m + 1]? = xs[m]? := rfl
            rw [jm]
            exact h2 m (by omega)
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun m hm => ?_⟩
          have h2' := h2 (m + 1) (by omega)
          have jm : (x :: xs)[m + 1]? = xs[m]? := rfl
          rw [jm] at h2'
          exact h2'

/-- After splitting, the positions still labelled `v` are exactly the
    non-first occurrences of `v` (provided `fresh ≠ v` and `fresh` does
    not occur in `w`). -/
theorem getElem?_splitFirst_self {w : List Nat} {v fresh : Nat}
    (hfresh : ∀ i : Nat, w[i]? ≠ some fresh) (hfv : fresh ≠ v) (i : Nat) :
    (splitFirst w v fresh)[i]? = some v ↔
      (w[i]? = some v ∧ ∃ j, j < i ∧ w[j]? = some v) := by
  induction w generalizing i with
  | nil => simp [splitFirst]
  | cons x xs ih =>
    have hfx : ∀ k : Nat, xs[k]? ≠ some fresh := fun k => hfresh (k + 1)
    cases i with
    | zero =>
      by_cases hxv : x = v
      · unfold splitFirst
        rw [if_pos hxv, List.getElem?_cons_zero]
        constructor
        · intro h
          exact absurd (Option.some_inj.mp h) hfv
        · rintro ⟨-, j, hj, -⟩
          exact absurd hj (by omega)
      · unfold splitFirst
        rw [if_neg hxv, List.getElem?_cons_zero]
        constructor
        · intro h
          exact absurd (Option.some_inj.mp h) hxv
        · rintro ⟨-, j, hj, -⟩
          exact absurd hj (by omega)
    | succ n =>
      by_cases hxv : x = v
      · unfold splitFirst
        rw [if_pos hxv]
        have hcons : (fresh :: xs)[n + 1]? = xs[n]? := rfl
        have wcons : (x :: xs)[n + 1]? = xs[n]? := rfl
        rw [hcons, wcons]
        constructor
        · intro h
          exact ⟨h, ⟨0, Nat.zero_lt_succ n, by rw [List.getElem?_cons_zero, hxv]⟩⟩
        · rintro ⟨h1, -⟩
          exact h1
      · unfold splitFirst
        rw [if_neg hxv]
        have hcons : (x :: splitFirst xs v fresh)[n + 1]? = (splitFirst xs v fresh)[n]? := rfl
        have wcons : (x :: xs)[n + 1]? = xs[n]? := rfl
        rw [hcons, wcons, ih hfx n]
        constructor
        · rintro ⟨h1, j, hj, hjv⟩
          have jm1 : (x :: xs)[j + 1]? = xs[j]? := rfl
          exact ⟨h1, j + 1, by omega, by rw [jm1]; exact hjv⟩
        · rintro ⟨h1, j, hj, hjv⟩
          refine ⟨h1, ?_⟩
          cases j with
          | zero =>
            rw [List.getElem?_cons_zero] at hjv
            exact absurd (Option.some_inj.mp hjv) hxv
          | succ m =>
            have jm : (x :: xs)[m + 1]? = xs[m]? := rfl
            rw [jm] at hjv
            exact ⟨m, by omega, hjv⟩

/-- The fresh label `listMax w + 1` occurs nowhere in `w`. -/
theorem fresh_not_mem_getElem? {w : List Nat} (i : Nat) :
    w[i]? ≠ some (listMax w + 1) := by
  intro h
  have hmem : listMax w + 1 ∈ w := List.mem_of_getElem? h
  have hle := le_listMax hmem
  omega

/-- A successful `getElem?` gives the index bound. -/
private theorem lt_length_of_getElem?_eq_some {w : List Nat} {i c : Nat}
    (h : w[i]? = some c) : i < w.length := by
  by_contra hc
  have hnone : w[i]? = none := List.getElem?_eq_none (not_lt.mp hc)
  rw [hnone] at h
  exact absurd h (by simp)

/-- Membership in `occurrences` as a conjunction. -/
private theorem mem_occurrences_iff {w : List Nat} {c i : Nat} :
    i ∈ occurrences w c ↔ (i < w.length ∧ w[i]? = some c) := by
  simp only [occurrences, Finset.mem_filter, Finset.mem_range]

/-- Splitting a packet class `v`: the fresh label occurs exactly once
    (it replaces the first occurrence of `v`). -/
theorem occurrences_splitClass_fresh_card {w : List Nat} {v : Nat}
    (hv : v ∈ ReturnPacket w) :
    (occurrences (splitClass w v) (listMax w + 1)).card = 1 := by
  have hcard : (occurrences w v).card = 2 := by
    simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at hv
    exact hv.2
  have hne : (occurrences w v).Nonempty := by
    rw [← Finset.card_pos]; omega
  have hset : occurrences (splitClass w v) (listMax w + 1)
      = {(occurrences w v).min' hne} := by
    have hmem2 : w[(occurrences w v).min' hne]? = some v :=
      (mem_occurrences_iff.mp (Finset.min'_mem _ hne)).2
    have hmemlen : (occurrences w v).min' hne < w.length :=
      (mem_occurrences_iff.mp (Finset.min'_mem _ hne)).1
    apply Finset.ext
    intro i
    have hiff : (splitFirst w v (listMax w + 1))[i]? = some (listMax w + 1) ↔
        (w[i]? = some v ∧ ∀ j, j < i → w[j]? ≠ some v) :=
      getElem?_splitFirst_fresh (fun k => fresh_not_mem_getElem? k) i
    rw [Finset.mem_singleton, mem_occurrences_iff]
    unfold splitClass
    rw [splitFirst_length, hiff]
    constructor
    · rintro ⟨hilen, h1, h2⟩
      have hi : i ∈ occurrences w v := mem_occurrences_iff.mpr ⟨hilen, h1⟩
      have hle : (occurrences w v).min' hne ≤ i := Finset.min'_le _ _ hi
      by_contra hne'
      have hlt : (occurrences w v).min' hne < i :=
        lt_of_le_of_ne hle (fun he => hne' he.symm)
      exact h2 _ hlt hmem2
    · intro h
      subst h
      refine ⟨hmemlen, hmem2, fun j hj => ?_⟩
      by_contra hcon
      have hjmem : j ∈ occurrences w v := mem_occurrences_iff.mpr
        ⟨lt_length_of_getElem?_eq_some hcon, hcon⟩
      have hle : (occurrences w v).min' hne ≤ j := Finset.min'_le _ _ hjmem
      omega
  rw [hset, Finset.card_singleton]

/-- Splitting a packet class `v`: the old label keeps exactly one
    occurrence (all but its first occurrence). -/
theorem occurrences_splitClass_self_card {w : List Nat} {v : Nat}
    (hv : v ∈ ReturnPacket w) :
    (occurrences (splitClass w v) v).card = 1 := by
  have hvle : v ≤ listMax w := by
    simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at hv
    omega
  have hcard : (occurrences w v).card = 2 := by
    simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at hv
    exact hv.2
  have hne : (occurrences w v).Nonempty := by
    rw [← Finset.card_pos]; omega
  have hfv : listMax w + 1 ≠ v := by omega
  have hset : occurrences (splitClass w v) v
      = (occurrences w v).erase ((occurrences w v).min' hne) := by
    have hmem2 : w[(occurrences w v).min' hne]? = some v :=
      (mem_occurrences_iff.mp (Finset.min'_mem _ hne)).2
    apply Finset.ext
    intro i
    have hiff : (splitFirst w v (listMax w + 1))[i]? = some v ↔
        (w[i]? = some v ∧ ∃ j, j < i ∧ w[j]? = some v) :=
      getElem?_splitFirst_self (fun k => fresh_not_mem_getElem? k) hfv i
    rw [Finset.mem_erase, mem_occurrences_iff, mem_occurrences_iff]
    unfold splitClass
    rw [splitFirst_length, hiff]
    constructor
    · rintro ⟨hilen, h1, hex⟩
      have hle_of : ∀ j, w[j]? = some v → (occurrences w v).min' hne ≤ j := by
        intro j hjv
        have hjmem : j ∈ occurrences w v := mem_occurrences_iff.mpr
          ⟨lt_length_of_getElem?_eq_some hjv, hjv⟩
        exact Finset.min'_le _ _ hjmem
      refine ⟨fun heq => hex.elim (fun j hj => ?_), hilen, h1⟩
      obtain ⟨hjlt, hjv⟩ := hj
      have hlej := hle_of j hjv
      omega
    · rintro ⟨hne', hilen, h1⟩
      have hi : i ∈ occurrences w v := mem_occurrences_iff.mpr ⟨hilen, h1⟩
      have hle : (occurrences w v).min' hne ≤ i := Finset.min'_le _ _ hi
      exact ⟨hilen, h1, (occurrences w v).min' hne,
        lt_of_le_of_ne hle (fun he => hne' he.symm), hmem2⟩
  rw [hset, Finset.card_erase_of_mem (Finset.min'_mem _ hne), hcard]

/-- Exact packet deletion: splitting a packet class `v` removes exactly
    `v` from the complete packet — the two occurrences of `v` become two
    singletons (one keeps `v`, one takes the fresh label), and every
    other class keeps its occurrences. -/
theorem ReturnPacket_splitClass_erase {w : List Nat} {v : Nat}
    (hv : v ∈ ReturnPacket w) :
    ReturnPacket (splitClass w v) = (ReturnPacket w).erase v := by
  have hvle : v ≤ listMax w := by
    simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at hv
    omega
  have hfreshcard := occurrences_splitClass_fresh_card hv
  have hselfcard := occurrences_splitClass_self_card hv
  apply Finset.ext
  intro c
  by_cases hcv : c = v
  · subst hcv
    constructor
    · simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range]
      rintro ⟨-, h2⟩
      rw [hselfcard] at h2
      omega
    · intro h
      rw [Finset.mem_erase] at h
      exact (h.1 rfl).elim
  · by_cases hcf : c = listMax w + 1
    · subst hcf
      constructor
      · simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range]
        rintro ⟨-, h2⟩
        rw [hfreshcard] at h2
        omega
      · intro h
        rw [Finset.mem_erase] at h
        simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at h
        omega
    · by_cases hcle : c ≤ listMax w
      · have hocc := occurrences_splitClass (w := w) (v := v) (c := c) hcv hcle
        have hle := listMax_le_listMax_splitClass w v
        simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
        constructor
        · rintro ⟨hlt, h2⟩
          refine ⟨hcv, by omega, by rw [← hocc]; exact h2⟩
        · rintro ⟨-, hlt, h2⟩
          refine ⟨by omega, by rw [hocc]; exact h2⟩
      · have hset : occurrences (splitClass w v) c = occurrences w c := by
          have hcf' : c ≠ listMax w + 1 := hcf
          have hpt := get?_splitFirst (w := w) (v := v) (fresh := listMax w + 1)
            (c := c) hcv hcf'
          unfold splitClass occurrences
          rw [splitFirst_length]
          apply Finset.ext
          intro i
          simp only [Finset.mem_filter, Finset.mem_range]
          rw [hpt i]
        have hcard0 : (occurrences (splitClass w v) c).card = 0 := by
          rw [hset, Finset.card_eq_zero]
          apply Finset.eq_empty_of_forall_notMem
          intro i hi
          simp only [occurrences, Finset.mem_filter, Finset.mem_range] at hi
          have hmem : c ∈ w := List.mem_of_getElem? hi.2
          have hle := le_listMax hmem
          omega
        have hmemfalse : c ∉ ReturnPacket w := by
          simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range]
          rintro ⟨hlt, -⟩
          omega
        constructor
        · simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range]
          rintro ⟨-, h2⟩
          rw [hcard0] at h2
          omega
        · intro h
          rw [Finset.mem_erase] at h
          exact absurd h.2 hmemfalse

/-- The complete packet strictly shrinks by one class per split step —
    the descent measure for the termination tower. -/
theorem card_ReturnPacket_splitClass {w : List Nat} {v : Nat}
    (hv : v ∈ ReturnPacket w) :
    (ReturnPacket (splitClass w v)).card = (ReturnPacket w).card - 1 := by
  rw [ReturnPacket_splitClass_erase hv, Finset.card_erase_of_mem hv]

/-- The deleted class keeps no elementary return: its two occurrences
    become singletons, so the exact-two-occurrence requirement fails.
    (Count/sector preservation for the remaining classes is
    `occurrences_splitClass` / `isElementaryReturn_splitClass`.) -/
theorem not_isElementaryReturn_splitClass_self {w : List Nat} {v a b : Nat}
    (hv : v ∈ ReturnPacket w) :
    ¬ IsElementaryReturn (splitClass w v) v a b := by
  intro h
  obtain ⟨hab, hblen, ha, hb, -⟩ := h
  have hcard := occurrences_splitClass_self_card hv
  have hlen : (splitClass w v).length = w.length := splitClass_length w v
  have ha' : a ∈ occurrences (splitClass w v) v := by
    simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ha⟩
    omega
  have hb' : b ∈ occurrences (splitClass w v) v := by
    simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hb⟩
    omega
  have h2 : 1 < (occurrences (splitClass w v) v).card :=
    Finset.one_lt_card.mpr ⟨a, ha', b, hb', by omega⟩
  omega

end PrimeMother
