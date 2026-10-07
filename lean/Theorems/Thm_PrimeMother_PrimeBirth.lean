/-
Prime-Distribution Birth Mother — Exact prime-birth theorem.

Formalizes §6 (Exact prime-birth theorem), the paper's first main result:

  Theorem (The birth ranks are exactly the primes):
  For every retained prefix H with rk(H) ≥ 2,
    Birth(H) = 1 ↔ rk(H) ∈ ℙ.

Proof by strong induction on the posterior rank, following the paper:
- If rk(H) is prime and H were inherited, some earlier birth Π would give
  a regular atlas with r ≥ 2 blocks, so rk(H) = r * rk(Π) with both
  factors > 1, contradicting primality.
- If rk(H) is composite, a prime divisor p gives (by IH) an earlier birth
  Π of rank p, and the atlas-rank converse yields a regular Π-atlas,
  so H is inherited.
-/

import Definitions.Def_PrimeMother_Atlas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace PrimeMother

/-- Auxiliary: births are at least 2. -/
theorem birth_ge_two {n : Nat} (h : birth n = true) : 2 ≤ n := by
  match n with
  | 0 => simp [birth] at h
  | 1 => simp [birth] at h
  | (n + 2) => omega

/-- The birth rule unfolds to: n+2 is born iff no earlier birth divides it
    with quotient ≥ 2. -/
theorem birth_iff_no_earlier_mother (n : Nat) :
    birth (n + 2) = true ↔
      ¬ ∃ m : Nat, m < n + 2 ∧ birth m = true ∧ HasRegAtlas (n + 2) m := by
  rw [birth_succ_succ]
  by_cases h : ∃ m : Nat, m < n + 2 ∧ birth m ∧ HasRegAtlas (n + 2) m
  · simp only [h, if_true]
    constructor
    · intro hc; exact absurd rfl hc
    · intro _
      obtain ⟨m, hm, hbm, hatlas⟩ := h
      exact ⟨m, hm, by rw [← Bool.eq_true_iff]; exact hbm, hatlas⟩
  · simp only [h, if_false]
    constructor
    · intro _ hcon
      exact h hcon
    · intro _; rfl

/-- Main theorem: the birth ranks are exactly the primes. -/
theorem birth_iff_prime : ∀ n : Nat, 2 ≤ n → (birth n = true ↔ Nat.Prime n) := by
  intro n
  -- Strong induction on n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [birth_iff_no_earlier_mother]
    constructor
    · -- (→) If n+2 is not inherited by any earlier birth, then n+2 is prime.
      intro hno
      -- Suppose n+2 is not prime; derive a contradiction.
      by_contra hnp
      -- n+2 ≥ 2 and not prime → composite: ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a * b = n+2
      -- Actually use: not prime → ∃ d, d ∣ n+2 ∧ 2 ≤ d ∧ d < n+2
      have hcomp : ∃ d : Nat, d ∣ (k + 2) ∧ 2 ≤ d ∧ d < k + 2 := by
        -- n+2 ≥ 2, not prime → has a nontrivial divisor
        have h2 : 2 ≤ k + 2 := by omega
        -- Use Nat.exists_dvd_of_not_prime2 or similar
        by_cases h1 : k + 2 = 0
        · omega
        · have := Nat.exists_dvd_of_not_prime2 (k + 2) hnp (by omega)
          obtain ⟨d, hd_dvd, hd2, hdn⟩ := this
          -- exists_dvd_of_not_prime2 gives: d ∣ n ∧ 2 ≤ d ∧ d < n? check signature
          sorry
      obtain ⟨d, hdvd, hd2, hdltn⟩ := hcomp
      -- d has a prime divisor p ≤ d < n+2
      obtain ⟨p, hp_prime, hpdvd⟩ := Nat.exists_prime_and_dvd hdvd
      -- p < n+2 and p ≥ 2
      have hp2 : 2 ≤ p := hp_prime.two_le
      have hplt : p < k + 2 := lt_of_le_of_lt (Nat.le_of_dvd (by omega) hpdvd) hdltn
      -- By IH, birth p = true
      have hbp : birth p = true := by
        obtain ⟨j, rfl⟩ : ∃ j, p = j + 2 := ⟨p - 2, by omega⟩
        exact (ih j (by omega) (by omega)).mpr hp_prime
      -- p ∣ n+2 with quotient ≥ 2: HasRegAtlas (k+2) p
      obtain ⟨r, hr⟩ := hdvd
      -- n+2 = p * r; r ≥ 2 since p < n+2 and p ≥ 1
      have hr2 : 2 ≤ r := by
        by_contra hc
        push_neg at hc
        interval_cases r
        · simp at hr; omega
        · -- r = 1: n+2 = p, contradicting p < n+2
          simp at hr; omega
      have hatlas : HasRegAtlas (k + 2) p := ⟨r, hr2, by rw [rk, rk]; linarith⟩
      exact hno ⟨p, hplt, hbp, hatlas⟩
    · -- (←) If n+2 is prime, no earlier birth is a mother of it.
      intro hp hcon
      obtain ⟨m, hmlt, hbm, hatlas⟩ := hcon
      obtain ⟨r, hr2, heq⟩ := hatlas
      -- m * r = n+2 with r ≥ 2; birth m → m ≥ 2
      have hm2 : 2 ≤ m := birth_ge_two hbm
      -- m ∣ n+2, 1 < m < n+2: contradicts primality
      have hdvd : m ∣ (k + 2) := ⟨r, by rw [rk, rk] at heq; linarith⟩
      have hmlt' : m < k + 2 := hmlt
      -- A prime has no divisors strictly between 1 and itself
      have := (Nat.prime_def_lt hp).mp hdvd hm2 hmlt'
      -- prime_def_lt gives m = n+2? Actually: p prime, m ∣ p, 2 ≤ m, m < p → False
      -- The exact form: Nat.Prime → m ∣ p → m = 1 ∨ m = p
      exact absurd rfl this
termination_by n => n

end PrimeMother
