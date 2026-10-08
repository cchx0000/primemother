/-
Prime-Distribution Birth Mother — Regression tests (P0.4).

Proof-style examples covering unit exclusion, first primes, composites,
and squares. `birth` is noncomputable, so these are proved equalities
rather than `#eval` outputs.
-/

import Theorems.Thm_PrimeMother_PrimeBirth

namespace PrimeMother

/-- 0 is not a birth (unit exclusion). -/
example : birth 0 = false := birth_root

/-- 1 is not a birth (unit exclusion). -/
example : birth 1 = false := birth_E

/-- Helper: no m < 2 is a birth. -/
private theorem no_birth_lt_two : ¬ Exists (fun m : Nat =>
    m < 2 /\ birth m = true /\ HasRegAtlas 2 m) := by
  rintro ⟨m, hm, hbm, _⟩
  have : m = 0 ∨ m = 1 := by omega
  rcases this with rfl | rfl
  · have h0 : birth 0 = false := birth_root
    rw [h0] at hbm
    exact absurd hbm (by decide)
  · have h1 : birth 1 = false := birth_E
    rw [h1] at hbm
    exact absurd hbm (by decide)

/-- 2 is born (first prime). -/
example : birth 2 = true := by
  have h : birth (0 + 2) = true := by
    rw [birth_succ_succ, if_neg no_birth_lt_two]
  simpa using h

/-- 3 is born (prime): 2 is a birth but 2 * r = 3 has no solution with r ≥ 2. -/
example : birth 3 = true := by
  have h2 : birth 2 = true := by
    rw [show (2 : Nat) = 0 + 2 from rfl, birth_succ_succ, if_neg no_birth_lt_two]
  have h : birth (1 + 2) = true := by
    rw [birth_succ_succ]
    apply if_neg
    rintro ⟨m, hm, hbm, hatlas⟩
    have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases this with rfl | rfl | rfl
    · have h0 : birth 0 = false := birth_root
      rw [h0] at hbm; exact absurd hbm (by decide)
    · have h1 : birth 1 = false := birth_E
      rw [h1] at hbm; exact absurd hbm (by decide)
    · -- m = 2, birth 2 = true, but ¬ HasRegAtlas 3 2
      obtain ⟨r, hr2, heq⟩ := hatlas
      unfold rk at heq
      omega
  simpa using h

/-- 4 is not born (composite): 2 is an earlier birth with atlas (r = 2). -/
example : birth 4 = false := by
  have h2 : birth 2 = true := by
    rw [show (2 : Nat) = 0 + 2 from rfl, birth_succ_succ, if_neg no_birth_lt_two]
  have h : birth (2 + 2) = false := by
    rw [birth_succ_succ, if_pos]
    exact ⟨2, by omega, h2, ⟨2, by omega, by unfold rk; rfl⟩⟩
  simpa using h

/-- 6 is not born (composite): 2 is an earlier birth with atlas (r = 3). -/
example : birth 6 = false := by
  have h2 : birth 2 = true := by
    rw [show (2 : Nat) = 0 + 2 from rfl, birth_succ_succ, if_neg no_birth_lt_two]
  have h : birth (4 + 2) = false := by
    rw [birth_succ_succ, if_pos]
    exact ⟨2, by omega, h2, ⟨3, by omega, by unfold rk; rfl⟩⟩
  simpa using h

/-- 9 is not born (square): 3 is an earlier birth with atlas (r = 3). -/
example : birth 9 = false := by
  have h3 : birth 3 = true := by
    have h2 : birth 2 = true := by
      rw [show (2 : Nat) = 0 + 2 from rfl, birth_succ_succ, if_neg no_birth_lt_two]
    have h : birth (1 + 2) = true := by
      rw [birth_succ_succ]
      apply if_neg
      rintro ⟨m, hm, hbm, hatlas⟩
      have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases this with rfl | rfl | rfl
      · have h0 : birth 0 = false := birth_root
        rw [h0] at hbm; exact absurd hbm (by decide)
      · have h1 : birth 1 = false := birth_E
        rw [h1] at hbm; exact absurd hbm (by decide)
      · obtain ⟨r, hr2, heq⟩ := hatlas
        unfold rk at heq
        omega
    simpa using h
  have h : birth (7 + 2) = false := by
    rw [birth_succ_succ, if_pos]
    exact ⟨3, by omega, h3, ⟨3, by omega, by unfold rk; rfl⟩⟩
  simpa using h

/-- 25 is not born (square of prime): 5 is a birth with atlas (r = 5). -/
example : birth 25 = false := by
  have h5 : birth 5 = true :=
    (birth_iff_prime 5 (by omega)).mpr (by decide)
  have h : birth (23 + 2) = false := by
    rw [birth_succ_succ, if_pos]
    exact ⟨5, by omega, h5, ⟨5, by omega, by unfold rk; rfl⟩⟩
  simpa using h

end PrimeMother
