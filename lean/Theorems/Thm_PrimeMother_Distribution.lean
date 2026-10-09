/-
Prime-Distribution Birth Mother — Unary distribution results (P1.3).

Formalizes paper §5 (The resulting prime distribution):
  - Corollary (Relabelling invariance)
  - Proposition (Path-sieve identity)
  - Theorem (Exact distribution identity): B_M(x) = π(x)

Scope note: the paper states the counting identity for real x ≥ 2.
What is formalized here is the Nat truncation: birth-counting up to n
equals Nat.primeCounting n. The real-parameter version is not claimed.
These are support-set / counting identities; no new prime-gap estimates
are claimed.
-/

import Theorems.Thm_PrimeMother_PrimeBirth
import Mathlib.NumberTheory.PrimeCounting

namespace PrimeMother

/-! ## Relabelling invariance (Corollary) -/

/-- A relabelling is an automorphism of the unlabelled source:
    it fixes the origin and commutes with the atomic successor step. -/
def IsChainIso (e : Chain → Chain) : Prop :=
  e .origin = .origin ∧ ∀ c, e (.step c) = .step (e c)

/-- Relabellings preserve posterior rank, hence every rank-model
    definition (HasRegAtlas, Mother, birth, QualifiedMother,
    BirthLedger) is independent of names assigned to source states:
    they are all computed from crk alone. -/
theorem chainIso_preserves_crk {e : Chain → Chain} (h : IsChainIso e)
    (c : Chain) : crk (e c) = crk c := by
  induction c with
  | origin => simp [crk, h.1]
  | step c ih =>
    rw [h.2, crk, crk, ih]

/-! ## Mother cones and the path sieve (Proposition) -/

/-- The future mother cone of a primitive prefix Π (paper §5):
    all H admitting a regular Π-atlas. -/
def MotherCone (Pi : Prefix) : Set Prefix := {H | Mother Pi H}

/-- Cone membership is the rank equation (atlas-rank lemma). -/
theorem mem_cone_iff {Pi H : Prefix} :
    H ∈ MotherCone Pi ↔ ∃ r : Nat, 2 ≤ r ∧ rk H = r * rk Pi := by
  constructor
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, hr, by unfold rk at heq ⊢; rw [Nat.mul_comm]; exact heq.symm⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, hr, by unfold rk at heq ⊢; rw [Nat.mul_comm]; exact heq.symm⟩

/-- Path-sieve identity: the union of all earlier mother cones at rank n
    contains the rank-n prefix exactly when n is composite.
    (For n ≥ 2; births are exactly the primes by birth_iff_prime.) -/
theorem path_sieve_identity (n : Nat) (h2 : 2 ≤ n) :
    (∃ Pi, birth Pi = true ∧ Pi < n ∧ Mother Pi n) ↔ (¬ Nat.Prime n) := by
  constructor
  · -- a mother-cone witness gives a proper divisor, so n is not prime
    rintro ⟨Pi, hbirth, hlt, hmother⟩
    obtain ⟨r, hr, heq⟩ := hmother
    have hPi2 : 2 ≤ Pi := by
      have hgt := birth_ge_two hbirth
      simpa using hgt
    have hdvd : Pi ∣ n := ⟨r, by unfold rk at heq; omega⟩
    intro hprime
    obtain ⟨_, hdiv⟩ := Nat.prime_def_lt.mp hprime
    -- every divisor of n below n is 1; but 2 ≤ Pi < n
    have hPi1 : Pi = 1 := hdiv Pi hlt hdvd
    omega
  · -- n composite: a prime divisor is a qualified mother
    intro hnotprime
    have hn1 : n ≠ 1 := by omega
    obtain ⟨p, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hn1
    have hp2 : 2 ≤ p := hprime.two_le
    have hplt : p < n := by
      -- p ∣ n and p prime; if p = n then n prime, contradiction
      by_contra hcon
      push Not at hcon
      have hle : p ≤ n := Nat.le_of_dvd (by omega) hdvd
      have heq : p = n := by omega
      rw [heq] at hprime
      exact hnotprime hprime
    have hbirth : birth p = true := (birth_iff_prime p hp2).mpr hprime
    obtain ⟨r, hrfl⟩ := hdvd
    have hr2 : 2 ≤ r := by
      by_contra hcon
      push Not at hcon
      interval_cases r <;> omega
    exact ⟨p, hbirth, hplt, r, hr2, by unfold rk; omega⟩

/-! ## Exact distribution identity (Theorem) -/

/-- Birth-counting function (paper's B_M, Nat truncation):
    number of births m with 2 ≤ m ≤ x. -/
noncomputable def birthCount (x : Nat) : Nat :=
  ((Finset.range (x + 1)).filter (fun m => decide (2 ≤ m ∧ birth m = true))).card

/-- Exact distribution identity (Nat form): the birth count up to x
    equals the prime-counting function π(x).
    The paper states this for real x ≥ 2; here x : Nat. -/
theorem birthCount_eq_primeCounting (x : Nat) :
    birthCount x = Nat.primeCounting x := by
  have hset : ((Finset.range (x + 1)).filter
      (fun m => decide (2 ≤ m ∧ birth m = true)))
      = ((Finset.range (x + 1)).filter Nat.Prime) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨hmx, hm2, hbirth⟩
      exact ⟨hmx, (birth_iff_prime m hm2).mp hbirth⟩
    · rintro ⟨hmx, hprime⟩
      have hm2 := hprime.two_le
      exact ⟨hmx, hm2, (birth_iff_prime m hm2).mpr hprime⟩
  unfold birthCount Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, hset]

/-- Support identity: the births are exactly the primes (paper's
    supp(μ_M) = PP, Nat form). -/
theorem birth_support_eq_primes :
    {m : Nat | 2 ≤ m ∧ birth m = true} = {m : Nat | Nat.Prime m} := by
  ext m
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hm2, hbirth⟩
    exact (birth_iff_prime m hm2).mp hbirth
  · intro hprime
    exact ⟨hprime.two_le, (birth_iff_prime m hprime.two_le).mpr hprime⟩

end PrimeMother
