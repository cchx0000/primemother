/-
Prime-Distribution Birth Mother — Finite return source, part C (P2.1c).

Paper Theorem (Arbitrary finite distinct-prime return birth)
`thm:return-combination`, direction (ii).

Step 1: the "fresh spine" [0, 1, ..., n] (defined recursively) is a
return word with max n. This is the backbone for prime blocks.
-/

import Definitions.Def_PrimeMother_ReturnPacket
import Mathlib.Tactic

namespace PrimeMother

/-- Fresh spine [0, 1, ..., n], by recursion. -/
def spine : Nat → List Nat
  | 0 => [0]
  | n + 1 => spine n ++ [n + 1]

/-- Spine max is n. -/
theorem listMax_spine (n : Nat) : listMax (spine n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show listMax (spine n ++ [n + 1]) = n + 1
    rw [listMax_append_single, ih]
    omega

/-- Spine length is n + 1. -/
theorem spine_length (n : Nat) : (spine n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (spine n ++ [n + 1]).length = n + 1 + 1
    simp only [List.length_append, List.length_singleton, ih]

/-- Last label of the spine is n. -/
theorem getLast?_spine (n : Nat) : (spine n).getLast? = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((spine n ++ [n + 1]).getLast?) = some (n + 1)
    rw [List.getLast?_append, List.getLast?_singleton, ih]
    rfl

/-- The spine is a return word (each new label is max + 1, ≠ last). -/
theorem isReturnWord_spine (n : Nat) : IsReturnWord (spine n) := by
  induction n with
  | zero => exact IsReturnWord.base
  | succ n ih =>
    show IsReturnWord (spine n ++ [n + 1])
    refine IsReturnWord.step (spine n) (n + 1) ih ?_ ?_
    · rw [getLast?_spine]
      simp
    · rw [listMax_spine]

/-- Single-prime return word: spine p with a return to label 1.
    Word: [0, 1, ..., p, 1]. Label 1 spans p atomic edges. -/
def singlePrimeWord (p : Nat) : List Nat := spine p ++ [1]

/-- It's a return word (for p ≥ 2): 1 ≠ last label (p), 1 ≤ max + 1. -/
theorem isReturnWord_singlePrime (p : Nat) (hp : 2 ≤ p) :
    IsReturnWord (singlePrimeWord p) := by
  unfold singlePrimeWord
  refine IsReturnWord.step (spine p) 1 (isReturnWord_spine p) ?_ ?_
  · rw [getLast?_spine]
    simp
    omega
  · rw [listMax_spine]
    omega

/-- Spine index 1 is always label 1 (for n ≥ 1). -/
theorem spine_one_at_one (n : Nat) (hn : 1 ≤ n) :
    (spine n)[1]? = some 1 := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
    simp only [spine]
    by_cases hn1 : n = 0
    · subst hn1
      simp only [spine]
      rfl
    · have hn' : 1 ≤ n := by omega
      rw [List.getElem?_append_left (by
        have h := spine_length n
        omega)]
      exact ih hn'

/-- Label 1 occurs at position 1. -/
theorem singlePrimeWord_one_at_one (p : Nat) (hp : 1 ≤ p) :
    (singlePrimeWord p)[1]? = some 1 := by
  unfold singlePrimeWord
  rw [List.getElem?_append_left (by
    have h := spine_length p
    omega)]
  exact spine_one_at_one p hp

end PrimeMother
