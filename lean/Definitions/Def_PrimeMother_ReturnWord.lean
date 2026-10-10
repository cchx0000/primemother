/-
Prime-Distribution Birth Mother — Finite return source, part A (P2.1a).

Formalizes paper §"The universal unlabelled path-history source",
Proposition (Canonical normal form of the return source)
`prop:return-normal-form`:

Length-n objects of R_ret are in bijection with words c_0...c_n with
  c_i ∈ Nat, c_0 = 0, c_i ≤ 1 + max_{j<i} c_j, c_i ≠ c_{i-1}.

This file: the word predicate (inductive: base [0], each step appends
a label ≤ running max + 1 different from the last label) and its basic
theory. A "new" label (above the running max) is forced to be exactly
max + 1, which is the first-occurrence normalization. The bijection
with unlabelled histories is P2.1b.
-/

namespace PrimeMother

/-- Running maximum of a label list (0 for empty). -/
def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => max x (listMax xs)

@[simp] theorem listMax_nil : listMax [] = 0 := rfl
@[simp] theorem listMax_cons (x : Nat) (xs : List Nat) :
    listMax (x :: xs) = max x (listMax xs) := rfl

theorem listMax_append_single (w : List Nat) (c : Nat) :
    listMax (w ++ [c]) = max (listMax w) c := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append]
    rw [listMax_cons, listMax_cons, ih]
    omega

/-- Every element is bounded by the list max. -/
theorem le_listMax {w : List Nat} {x : Nat} (hx : x ∈ w) :
    x ≤ listMax w := by
  induction w with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [listMax_cons]
    simp at hx
    rcases hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

/-- Normalized return words: class-label sequences of finite unlabelled
    path histories. Base [0]; each extension appends a label c with
    c ≠ last label and c ≤ (running max) + 1 (paper's
    c_i ≤ 1 + max_{j<i} c_j and c_i ≠ c_{i-1}). -/
inductive IsReturnWord : List Nat → Prop
  | base : IsReturnWord [0]
  | step : ∀ (w : List Nat) (c : Nat), IsReturnWord w →
      w.getLast? ≠ some c →
      c ≤ listMax w + 1 →
      IsReturnWord (w ++ [c])

/-- Every return word is nonempty. -/
theorem returnWord_nonempty {w : List Nat} (h : IsReturnWord w) :
    w ≠ [] := by
  cases h with
  | base => simp
  | step w c _ _ _ => simp

/-- The first label is 0. -/
theorem returnWord_head_zero {w : List Nat} (h : IsReturnWord w) :
    w.head? = some 0 := by
  induction h with
  | base => rfl
  | step w c hw _ _ ih =>
    have hne : w ≠ [] := returnWord_nonempty hw
    -- (w ++ [c]).head? = w.head?
    have : (w ++ [c]).head? = w.head? := by
      cases w with
      | nil => exact absurd rfl hne
      | cons x xs => rfl
    rw [this]
    exact ih

/-- A genuinely new label must be exactly max + 1 (first-occurrence
    normalization): labels are natural numbers, so "above the max but
    ≤ max + 1" forces equality. -/
theorem returnWord_new_label_eq {w : List Nat}
    {c : Nat} (hc : listMax w < c) (hle : c ≤ listMax w + 1) :
    c = listMax w + 1 := by
  omega

/-- The running max never exceeds the word length (each step adds at
    most one new class, starting from [0]). -/
theorem returnWord_max_le_length {w : List Nat} (h : IsReturnWord w) :
    listMax w ≤ w.length := by
  induction h with
  | base => simp
  | step w c hw _ hle ih =>
    rw [listMax_append_single]
    simp only [List.length_append, List.length_singleton]
    omega

/-- Every label is bounded by the word length. -/
theorem returnWord_label_le_length {w : List Nat} (h : IsReturnWord w)
    {x : Nat} (hx : x ∈ w) : x ≤ w.length :=
  Nat.le_trans (le_listMax hx) (returnWord_max_le_length h)

end PrimeMother
