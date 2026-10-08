/-
Prime-Distribution Birth Mother — Exact prime-birth theorem.

Formalizes the paper's Exact prime-birth theorem (paper §5):

  Theorem (The birth ranks are exactly the primes):
  For every retained prefix H with rk(H) ≥ 2,
    Birth(H) = 1 ↔ rk(H) ∈ ℙ.

Proof by strong induction on the posterior rank, following the paper.
-/

import Definitions.Def_PrimeMother_Atlas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace PrimeMother

/-- Auxiliary: births are at least 2.
    Uses birth_root and birth_E for the 0/1 cases. -/
theorem birth_ge_two {n : Nat} (h : birth n = true) : 2 ≤ n := by
  match n with
  | 0 =>
    -- birth 0 = birth root = false, contradiction with h
    have : birth 0 = false := birth_root
    rw [this] at h
    exact absurd h (by decide)
  | 1 =>
    have : birth 1 = false := birth_E
    rw [this] at h
    exact absurd h (by decide)
  | (n + 2) => omega

/-- The birth rule unfolds to: n+2 is born iff no earlier birth divides it
    with quotient ≥ 2. -/
theorem birth_iff_no_earlier_mother (n : Nat) :
    birth (n + 2) = true ↔
      ¬ Exists (fun m : Nat => m < n + 2 /\ birth m = true /\ HasRegAtlas (n + 2) m) := by
  rw [birth_succ_succ]
  by_cases h : Exists (fun m : Nat => m < n + 2 /\ birth m = true /\ HasRegAtlas (n + 2) m)
  · -- If such an m exists, the if gives false, so LHS is false = true (False),
    -- and RHS is ¬Exists which is False. Both sides are False.
    rw [if_pos h]
    constructor
    · intro hc
      -- hc : false = true, contradiction
      exact absurd hc (by decide)
    · intro hno
      exact absurd h (hno)
  · -- If no such m, the if gives true, so LHS is true = true (True),
    -- and RHS is ¬Exists which is True.
    rw [if_neg h]
    constructor
    · intro _; exact h
    · intro _; rfl

/-- Main theorem: the birth ranks are exactly the primes. -/
theorem birth_iff_prime : ∀ n : Nat, 2 ≤ n → (birth n = true ↔ Nat.Prime n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [birth_iff_no_earlier_mother]
    constructor
    · -- (→) If k+2 has no earlier mother birth, then k+2 is prime.
      intro hno
      by_contra hnp
      -- k+2 ≥ 2 and not prime: get a nontrivial divisor d.
      -- Nat.exists_dvd_of_not_prime2 : 2 ≤ n → ¬Nat.Prime n → ∃ d, d ∣ n ∧ 2 ≤ d ∧ d < n
      have h2 : 2 ≤ k + 2 := by omega
      obtain ⟨d, hdvd, hd2, hdltn⟩ := Nat.exists_dvd_of_not_prime2 h2 hnp
      -- d ≠ 1 since 2 ≤ d; get a prime divisor p of d.
      -- Nat.exists_prime_and_dvd : n ≠ 1 → ∃ p, p.Prime ∧ p ∣ n
      have hd1 : d ≠ 1 := by omega
      obtain ⟨p, hp_prime, hpdvd⟩ := Nat.exists_prime_and_dvd hd1
      -- p ∣ k+2 via p ∣ d ∣ k+2
      have hpdvd_n : p ∣ (k + 2) := dvd_trans hpdvd hdvd
      have hp2 : 2 ≤ p := hp_prime.two_le
      -- p ≤ d < k+2, so p < k+2
      have hplt : p < k + 2 :=
        lt_of_le_of_lt (Nat.le_of_dvd (by omega) hpdvd) hdltn
      -- By IH applied at p (written as j+2): birth p = true.
      -- ih (j+2) h1 h2' : (birth (j+2) = true ↔ Nat.Prime (j+2))
      have hbp : birth p = true := by
        obtain ⟨j, rfl⟩ : ∃ j, p = j + 2 := ⟨p - 2, by omega⟩
        have h1 : j + 2 < k + 2 := by omega
        have h2' : 2 ≤ j + 2 := by omega
        exact (ih (j + 2) h1 h2').mpr hp_prime
      -- Build HasRegAtlas (k+2) p: p ∣ k+2, write k+2 = p * r', show 2 ≤ r'.
      obtain ⟨r', hr'⟩ := hpdvd_n
      -- k+2 = p * r'; r' ≥ 2 because p < k+2 and p ≥ 2.
      -- If r' = 0 then k+2 = 0 (contra); if r' = 1 then k+2 = p (contra).
      have hr'2 : 2 ≤ r' := by
        rcases Nat.eq_zero_or_pos r' with rfl | hpos
        · -- r' = 0: hr' : k + 2 = p * 0 = 0, contradiction
          simp at hr'
        · by_cases h1 : r' = 1
          · subst h1
            -- hr' : k + 2 = p * 1 = p, but p < k+2
            simp at hr'
            omega
          · omega
      have hatlas : HasRegAtlas (k + 2) p := ⟨r', hr'2, by unfold rk; omega⟩
      exact hno ⟨p, hplt, hbp, hatlas⟩
    · -- (←) If k+2 is prime, no earlier birth is a mother of it.
      intro hp hcon
      obtain ⟨m, hmlt, hbm, hatlas⟩ := hcon
      obtain ⟨r, hr2, heq⟩ := hatlas
      have hm2 : 2 ≤ m := birth_ge_two hbm
      -- m ∣ k+2 from the atlas equation
      have hdvd : m ∣ (k + 2) := ⟨r, by unfold rk at heq; omega⟩
      -- Nat.prime_def_lt : Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1
      have hm1 : m = 1 := (Nat.prime_def_lt.mp hp).2 m hmlt hdvd
      omega

end PrimeMother
