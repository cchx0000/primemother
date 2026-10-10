/-
Prime-Distribution Birth Mother — infinite boundary model (P2.3).

Formalizes the inverse-limit / cylinder picture behind the paper's boundary
section: Proposition `prop:finite-not-boundary`, Definition
`def:source-transitive-birth`, Lemma `lem:finite-language-criterion` and
Theorem `thm:transitive-existence`.

* finite histories are finite words `FinHist = List ℕ`;
* `trunc w n` is the length-`n` prefix of `w`;
* an infinite history `InfHist` is a compatible family `seq n` of length-`n`
  prefixes (the inverse limit of the finite history spaces);
* `cylinder w` is the set of infinite histories whose length-`|w|` prefix is
  exactly `w` (the cylinder basis of the boundary topology).

This unit: the inverse-limit model and the truncation-compatibility lemmas.
-/

import Mathlib.Data.List.Basic

namespace PrimeMother

/-- Finite histories: finite words over `ℕ` (labels of an atomic path history). -/
abbrev FinHist := List ℕ

/-- Truncation: the length-`n` prefix of a finite word. -/
def trunc (w : FinHist) (n : ℕ) : FinHist := w.take n

/-- Truncation is idempotent up to `min`: truncating twice is one truncation. -/
theorem trunc_trunc (w : FinHist) (n m : ℕ) :
    trunc (trunc w m) n = trunc w (min n m) := by
  simp [trunc, List.take_take]

/-- Length of a truncation. -/
theorem trunc_length (w : FinHist) (n : ℕ) :
    (trunc w n).length = min n w.length := by
  simp [trunc, List.length_take]

/-- Infinite path histories as compatible sequences of finite prefixes: the
inverse limit of the finite history spaces.  `seq n` is the length-`n` prefix,
and truncating a longer prefix recovers the shorter one. -/
structure InfHist where
  seq : ℕ → FinHist
  length_eq : ∀ n, (seq n).length = n
  compat : ∀ n m, n ≤ m → (seq m).take n = seq n

namespace InfHist

/-- Two infinite histories with the same prefixes are equal. -/
@[ext]
theorem ext {X Y : InfHist} (h : ∀ n, X.seq n = Y.seq n) : X = Y := by
  obtain ⟨sx, _, _⟩ := X
  obtain ⟨sy, _, _⟩ := Y
  have hs : sx = sy := funext h
  subst hs
  rfl

/-- The length-`n` prefix of `X.seq n` is itself. -/
theorem take_self (X : InfHist) (n : ℕ) : (X.seq n).take n = X.seq n := by
  conv_lhs => rw [← X.length_eq n]
  exact List.take_length _

/-- The length-`0` prefix is empty. -/
theorem seq_zero (X : InfHist) : X.seq 0 = [] := by
  have h := X.length_eq 0
  match e : X.seq 0 with
  | [] => rfl
  | _ :: _ => simp [e] at h

/-- Truncating any longer prefix to length `n` gives `X.seq n`. -/
theorem trunc_seq (X : InfHist) (n m : ℕ) (h : n ≤ m) :
    trunc (X.seq m) n = X.seq n :=
  X.compat n m h

/-- The `n`-prefix of the `m`-prefix is the `min n m`-prefix. -/
theorem take_seq_min (X : InfHist) (n m : ℕ) :
    (X.seq m).take n = X.seq (min n m) := by
  rcases le_total n m with h | h
  · rw [min_eq_left h]; exact X.compat n m h
  · rw [min_eq_right h]
    conv_lhs => rw [← X.length_eq m]
    exact List.take_length _

/-- The cylinder set of a finite word: infinite histories whose length-`|w|`
prefix is exactly `w`.  Cylinders form the basis of the boundary topology. -/
def cylinder (w : FinHist) : Set InfHist := {X | X.seq w.length = w}

theorem mem_cylinder_iff (X : InfHist) (w : FinHist) :
    X ∈ cylinder w ↔ X.seq w.length = w :=
  Iff.rfl

/-- The empty word's cylinder is the whole space. -/
theorem cylinder_nil : cylinder [] = Set.univ := by
  ext X
  simp [cylinder, X.seq_zero]

/-- A cylinder determines all its prefix cylinders. -/
theorem cylinder_take_of_mem (X : InfHist) {w : FinHist} (hX : X ∈ cylinder w)
    {n : ℕ} (hn : n ≤ w.length) : X ∈ cylinder (w.take n) := by
  have h1 : X.seq w.length = w := hX
  have h2 : (X.seq w.length).take n = X.seq n := X.compat n w.length hn
  rw [h1] at h2
  show X.seq (w.take n).length = w.take n
  rw [List.length_take, min_eq_left hn]
  exact h2.symm

/-- Build an infinite history from an infinite atom stream: `seq n` is the
first `n` atoms. -/
def ofStream (s : ℕ → ℕ) : InfHist where
  seq := fun n => (List.range n).map s
  length_eq := fun n => by simp
  compat := fun n m h => by
    show ((List.range m).map s).take n = (List.range n).map s
    rw [List.map_take, List.take_range, min_eq_left h]

/-- The `n`-prefix of a streamed history is the mapped range. -/
theorem ofStream_seq (s : ℕ → ℕ) (n : ℕ) :
    (ofStream s).seq n = (List.range n).map s :=
  rfl

end InfHist

end PrimeMother
