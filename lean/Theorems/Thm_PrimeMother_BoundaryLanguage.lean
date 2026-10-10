/-
Prime-Distribution Birth Mother — shift, continuity and finite languages (P2.3).

Companion to `Definitions/Def_PrimeMother_Boundary.lean`.  Proves, for the
paper's boundary section (`prop:finite-not-boundary`,
`def:source-transitive-birth`, `lem:finite-language-criterion`,
`thm:transitive-existence`):

* the forward shift is continuous: the preimage of a cylinder is a union of
  cylinders (one per possible first label);
* the cylinders form a topological basis of the boundary topology;
* basic inclusion / monotonicity facts for windows, languages and orbit hulls.
-/

import Definitions.Def_PrimeMother_Boundary
import Mathlib.Topology.Bases
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order

namespace PrimeMother

namespace InfHist

/-- The preimage of a cylinder under shift is the union of the cylinders
obtained by prepending every possible first label.  In particular it is a
union of basic opens.  (With a finite label alphabet, as in the paper's
first-occurrence return-word model, the index set is finite.) -/
theorem shift_preimage_cylinder (w : FinHist) :
    shift ⁻¹' cylinder w = ⋃ a : ℕ, cylinder (a :: w) := by
  ext X
  simp only [Set.mem_preimage, Set.mem_iUnion, mem_cylinder_iff]
  constructor
  · intro h
    obtain ⟨a, t, ht⟩ : ∃ a t, X.seq (w.length + 1) = a :: t := by
      have hlen := X.length_eq (w.length + 1)
      match e : X.seq (w.length + 1) with
      | [] => simp [e] at hlen
      | a :: t => exact ⟨a, t, rfl⟩
    have htlen : t.length = w.length := by
      have hlen := X.length_eq (w.length + 1)
      rw [ht] at hlen
      simpa using hlen
    have htail : t.take w.length = w := by
      have h' : ((X.seq (w.length + 1)).drop 1).take w.length = w := h
      rw [ht] at h'
      exact h'
    have htw : t = w := by
      rw [← htlen, List.take_length] at htail
      exact htail
    refine ⟨a, ?_⟩
    have hlen' : (a :: w).length = w.length + 1 := rfl
    rw [hlen', ht, htw]
  · rintro ⟨a, ha⟩
    have hlen' : (a :: w).length = w.length + 1 := rfl
    rw [hlen'] at ha
    have h' : shiftSeq X w.length = w := by
      show ((X.seq (w.length + 1)).drop 1).take w.length = w
      rw [ha]
      exact List.take_length
    exact h'

/-- The forward shift is continuous in the cylinder topology. -/
theorem continuous_shift : Continuous shift := by
  rw [continuous_generateFrom_iff]
  rintro s ⟨w, rfl⟩
  rw [shift_preimage_cylinder]
  exact isOpen_iUnion fun a => TopologicalSpace.isOpen_generateFrom_of_mem ⟨a :: w, rfl⟩

/-- Cylinders form a topological basis of the boundary topology. -/
theorem cylinder_isBasis :
    TopologicalSpace.IsTopologicalBasis {s : Set InfHist | ∃ w, s = cylinder w} := by
  refine ⟨?_, ?_, rfl⟩
  · rintro t₁ ⟨u, rfl⟩ t₂ ⟨v, rfl⟩ X ⟨hXu, hXv⟩
    refine ⟨cylinder (X.seq (max u.length v.length)),
      ⟨X.seq (max u.length v.length), rfl⟩, ?_, ?_⟩
    · show X.seq (X.seq (max u.length v.length)).length
        = X.seq (max u.length v.length)
      rw [X.length_eq]
    · intro Y hY
      have hY' : Y.seq (max u.length v.length) = X.seq (max u.length v.length) := by
        rw [mem_cylinder_iff, X.length_eq] at hY
        exact hY
      have hXu' : X.seq u.length = u := hXu
      have hXv' : X.seq v.length = v := hXv
      constructor
      · show Y.seq u.length = u
        have e1 := Y.compat u.length (max u.length v.length) (Nat.le_max_left _ _)
        have e2 := X.compat u.length (max u.length v.length) (Nat.le_max_left _ _)
        rw [← e1, hY', e2]
        exact hXu'
      · show Y.seq v.length = v
        have e1 := Y.compat v.length (max u.length v.length) (Nat.le_max_right _ _)
        have e2 := X.compat v.length (max u.length v.length) (Nat.le_max_right _ _)
        rw [← e1, hY', e2]
        exact hXv'
  · ext X
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    exact ⟨cylinder [], ⟨[], rfl⟩, by rw [cylinder_nil]; trivial⟩

/-- The length-`n` window at position `0` is the `n`-prefix. -/
theorem window_zero (X : InfHist) (n : ℕ) : window X 0 n = X.seq n := by
  simp [window]

/-- Windows of the shifted history are later windows of the original. -/
theorem window_shift (X : InfHist) (m n : ℕ) :
    window (shift X) m n = window X (m + 1) n := by
  show (shift^[m] (shift X)).seq n = (shift^[m + 1] X).seq n
  rw [show m + 1 = m.succ from rfl, ← shift_iterate_succ]

/-- Language membership unfolds to shifted prefixes. -/
theorem mem_Lang_iff (X : InfHist) (w : FinHist) :
    w ∈ Lang X ↔ ∃ m, (shift^[m] X).seq w.length = w :=
  Iff.rfl

/-- Shifting can only shrink the finite language. -/
theorem Lang_shift_subset (X : InfHist) : Lang (shift X) ⊆ Lang X := by
  rintro w ⟨m, hm⟩
  exact ⟨m + 1, by rwa [window_shift] at hm⟩

/-- The shifted orbit sits inside the original orbit. -/
theorem orbit_shift_subset (X : InfHist) : orbit (shift X) ⊆ orbit X := by
  rintro Y ⟨m, rfl⟩
  exact ⟨m.succ, (Function.iterate_succ_apply shift m X).symm⟩

/-- The shifted orbit hull sits inside the original orbit hull. -/
theorem orbitHull_shift_subset (X : InfHist) :
    orbitHull (shift X) ⊆ orbitHull X :=
  closure_mono (orbit_shift_subset X)

/-- Every history lies in its own orbit hull. -/
theorem mem_orbitHull_self (X : InfHist) : X ∈ orbitHull X :=
  subset_closure ⟨0, by simp⟩

/-- Being born at the boundary is topological density of the orbit. -/
theorem bornAtBoundary_iff_dense (X : InfHist) :
    BornAtBoundary X ↔ Dense (orbit X) := by
  simp [BornAtBoundary, orbitHull, dense_iff_closure_eq]

end InfHist

end PrimeMother
