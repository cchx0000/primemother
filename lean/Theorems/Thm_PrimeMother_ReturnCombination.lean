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

/-- Word length is p + 2. -/
theorem singlePrimeWord_length (p : Nat) :
    (singlePrimeWord p).length = p + 2 := by
  unfold singlePrimeWord
  simp only [List.length_append, List.length_singleton, spine_length]

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

/-- Label 1 occurs at the final position p+1. -/
theorem singlePrimeWord_one_at_end (p : Nat) :
    (singlePrimeWord p)[p + 1]? = some 1 := by
  unfold singlePrimeWord
  have hlen : (spine p).length = p + 1 := spine_length p
  rw [List.getElem?_append_right (by omega)]
  simp [hlen]

/-- Spine position k holds label k. -/
theorem spine_get (n k : Nat) (hk : k ≤ n) : (spine n)[k]? = some k := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  | succ n ih =>
    simp only [spine]
    by_cases hk2 : k ≤ n
    · rw [List.getElem?_append_left (by
        have hl := spine_length n
        omega)]
      exact ih hk2
    · have hk3 : k = n + 1 := by omega
      subst hk3
      have hlen : (spine n).length = n + 1 := spine_length n
      rw [List.getElem?_append_right (by omega), hlen]
      simp

/-- The single-prime word has an elementary return of support length p:
    label 1 at positions 1 and p+1, nothing in between. -/
theorem singlePrimeWord_elementary (p : Nat) (hp : 2 ≤ p) :
    IsElementaryReturn (singlePrimeWord p) 1 1 (p + 1) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · have h := singlePrimeWord_length p
    omega
  · exact singlePrimeWord_one_at_one p (by omega)
  · exact singlePrimeWord_one_at_end p
  · intro k hk1 hk2
    -- 1 < k < p+1, so (singlePrimeWord p)[k]? = (spine p)[k]? = some k ≠ some 1
    have hkle : k ≤ p := by omega
    have hget : (singlePrimeWord p)[k]? = (spine p)[k]? := by
      unfold singlePrimeWord
      rw [List.getElem?_append_left (by
        have hl := spine_length p
        omega)]
    rw [hget, spine_get p k hkle]
    simp
    omega

/-!
P2.1c(iii): multi-prime packet word — paper `thm:return-combination`, part (ii).

The paper writes the primes increasingly p₁<…<pₖ and sets
  a₁ = 0, b₁ = p₁,   aᵢ = bᵢ₋₁ − 1, bᵢ = aᵢ + pᵢ  (i ≥ 2),
making {aᵢ, bᵢ} a two-element class and every other vertex a singleton.

As a *normalized* return word we cannot use vertex indices as labels: a
fresh vertex j would receive label j, violating c ≤ (running max)+1.
Instead we thread a fresh-label counter `next`: genuinely new singleton
vertices receive labels next, next+1, … (each exactly (running max)+1),
while the new right endpoint bᵢ reuses the label of vertex aᵢ = bᵢ₋₁−1.

Threaded state:
  w     — word built so far (covers vertices 0..b),
  b     — current last vertex,
  next  — next fresh label (= listMax w + 1),
  lprev — label of vertex b−1 (left endpoint of the next pair),
  llast — label of vertex b (last label of w).
-/

/-- Packet word builder following the paper's endpoint recursion. -/
def packetWordAux : List Nat → List Nat → Nat → Nat → Nat → Nat → List Nat
  | [], w, _, _, _, _ => w
  | p :: ps, w, b, next, lprev, llast =>
    let seg := List.range' next (p - 2) ++ [lprev]
    let lprev' := if p = 2 then llast else next + (p - 3)
    packetWordAux ps (w ++ seg) (b - 1 + p) (next + (p - 2)) lprev' lprev

/-- The multi-prime packet word for a list of primes (each ≥ 2). -/
def packetWord : List Nat → List Nat
  | [] => [0]
  | p :: ps => packetWordAux (p :: ps) [0, 1] 1 2 0 1

/-- Loop invariant of the packet-word builder.
    The 9th conjunct tracks the left-endpoint label: `lprev` is the label of
    vertex `b - 1`, so each new block's closing `lprev` is a genuine return
    to that vertex's label (the geometric endpoint data for the packet). -/
def PacketInv (w : List Nat) (b next lprev llast : Nat) : Prop :=
  IsReturnWord w ∧ w.length = b + 1 ∧ listMax w = next - 1 ∧ 2 ≤ next ∧ 1 ≤ b ∧
  w.getLast? = some llast ∧ lprev ≤ next - 1 ∧ lprev ≠ llast ∧
  w[b - 1]? = some lprev

/-- A word's last label never exceeds its running max. -/
theorem last_le_listMax {w : List Nat} {l : Nat} (h : w.getLast? = some l) :
    l ≤ listMax w :=
  le_listMax (List.mem_of_getLast? h)

/-- Appending a run of fresh labels keeps the return-word property and
    raises the running max by the run length. -/
theorem isReturnWord_append_fresh {w : List Nat} (hw : IsReturnWord w) (k : Nat) :
    IsReturnWord (w ++ List.range' (listMax w + 1) k) ∧
    listMax (w ++ List.range' (listMax w + 1) k) = listMax w + k := by
  induction k generalizing w with
  | zero =>
    have h0 : List.range' (listMax w + 1) 0 = [] := List.range'_zero
    rw [h0, List.append_nil]
    exact ⟨hw, by omega⟩
  | succ k ih =>
    set m := listMax w with hm
    have hstep : IsReturnWord (w ++ [m + 1]) := by
      apply IsReturnWord.step _ _ hw _ _
      · intro hcon
        have hle := last_le_listMax hcon
        omega
      · omega
    have hmax1 : listMax (w ++ [m + 1]) = m + 1 := by
      rw [listMax_append_single]
      omega
    have hsplit : List.range' (m + 1) (k + 1) = [m + 1] ++ List.range' (m + 1 + 1) k :=
      List.range'_succ
    rw [hsplit, ← List.append_assoc]
    have hih := ih hstep
    rw [hmax1] at hih
    have h2 := hih.2
    exact ⟨hih.1, by omega⟩

/-- Last label after appending a nonempty run of fresh labels. -/
theorem getLast?_append_fresh (w : List Nat) (m k : Nat) (hk : 1 ≤ k) :
    (w ++ List.range' m k).getLast? = some (m + k - 1) := by
  induction k generalizing w m with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      show (w ++ List.range' m 1).getLast? = some (m + 1 - 1)
      have hr : List.range' m 1 = [m] := rfl
      have hm : m + 1 - 1 = m := by omega
      rw [hr, List.getLast?_concat, hm]
    | succ n' =>
      have hsplit : List.range' m (n' + 1 + 1) = [m] ++ List.range' (m + 1) (n' + 1) :=
        List.range'_succ
      rw [hsplit, ← List.append_assoc]
      have hih := ih (w ++ [m]) (m + 1) (by omega)
      rw [show m + 1 + (n' + 1) - 1 = m + (n' + 1 + 1) - 1 from by omega] at hih
      exact hih

/-- One builder step preserves the invariant. -/
theorem packetStep_invariant {w : List Nat} {b next lprev llast p : Nat}
    (hp : 2 ≤ p) (hinv : PacketInv w b next lprev llast) :
    PacketInv (w ++ (List.range' next (p - 2) ++ [lprev]))
      (b - 1 + p) (next + (p - 2))
      (if p = 2 then llast else next + (p - 3)) lprev := by
  obtain ⟨hrw, hlen, hmax, hnext, hb, hlast, hlprev_le, hlprev_ne, hwprev⟩ := hinv
  have hnext1 : listMax w + 1 = next := by omega
  have hfresh := isReturnWord_append_fresh hrw (p - 2)
  rw [hnext1] at hfresh
  have hmaxw : listMax (w ++ List.range' next (p - 2)) = next + (p - 2) - 1 := by
    have h2 := hfresh.2
    omega
  by_cases hp2 : p = 2
  · subst hp2
    rw [if_pos rfl]
    have hseg : List.range' next (2 - 2) ++ [lprev] = [lprev] := by simp
    rw [hseg]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply IsReturnWord.step _ _ hrw _ _
      · intro hcon
        rw [hlast] at hcon
        exact hlprev_ne (Option.some_inj.mp hcon).symm
      · omega
    · simp only [List.length_append, List.length_singleton]
      omega
    · rw [listMax_append_single, hmax]
      have h1 : next + (2 - 2) - 1 = next - 1 := by omega
      rw [h1]
      exact Nat.max_eq_left hlprev_le
    · omega
    · omega
    · exact List.getLast?_concat
    · have hll := last_le_listMax hlast
      omega
    · exact hlprev_ne.symm
    · -- new left-endpoint tracking: vertex b - 1 + 2 - 1 = b holds llast
      have hbeq : b - 1 + 2 - 1 = w.length - 1 := by omega
      rw [hbeq, List.getElem?_append_left (by omega : w.length - 1 < w.length),
        ← List.getLast?_eq_getElem?]
      exact hlast
  · have hp3 : 3 ≤ p := by omega
    rw [if_neg hp2]
    have hgl : (w ++ List.range' next (p - 2)).getLast? = some (next + (p - 2) - 1) :=
      getLast?_append_fresh w next (p - 2) (by omega)
    have hlen2 : (w ++ List.range' next (p - 2)).length = b + 1 + (p - 2) := by
      simp only [List.length_append, List.length_range', hlen]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← List.append_assoc]
      apply IsReturnWord.step _ _ hfresh.1 _ _
      · intro hcon
        rw [hgl] at hcon
        have heq : lprev = next + (p - 2) - 1 := Option.some_inj.mp hcon.symm
        omega
      · rw [hmaxw]
        omega
    · simp only [List.length_append, List.length_range', List.length_singleton]
      omega
    · rw [← List.append_assoc, listMax_append_single, hmaxw]
      exact Nat.max_eq_left (by omega)
    · omega
    · omega
    · rw [← List.append_assoc]
      exact List.getLast?_concat
    · omega
    · intro hcon
      omega
    · -- new left-endpoint tracking: vertex b - 1 + p - 1 is the last fresh label
      have hpos : b - 1 + p - 1 = (w ++ List.range' next (p - 2)).length - 1 := by
        omega
      rw [← List.append_assoc, hpos,
        List.getElem?_append_left (by omega : (w ++ List.range' next (p - 2)).length - 1
          < (w ++ List.range' next (p - 2)).length),
        ← List.getLast?_eq_getElem?, hgl,
        show next + (p - 2) - 1 = next + (p - 3) by omega]

/-- The builder invariant holds after processing the whole prime list. -/
theorem packetWordAux_invariant (ps : List Nat) (w : List Nat) (b next lprev llast : Nat)
    (hall : ∀ p ∈ ps, 2 ≤ p) (hinv : PacketInv w b next lprev llast) :
    ∃ b' next' lprev' llast',
      PacketInv (packetWordAux ps w b next lprev llast) b' next' lprev' llast' := by
  induction ps generalizing w b next lprev llast with
  | nil =>
    exact ⟨b, next, lprev, llast, hinv⟩
  | cons p ps ih =>
    have hp2 : 2 ≤ p := hall p (by simp)
    have hps : ∀ q ∈ ps, 2 ≤ q := fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hstep := packetStep_invariant hp2 hinv
    obtain ⟨_b₂, _next₂, _lprev₂, _llast₂, hrest⟩ := ih _ _ _ _ _ hps hstep
    exact ⟨_b₂, _next₂, _lprev₂, _llast₂, hrest⟩

/-- Each builder step creates an elementary return with support length `p`:
    the left-endpoint label `lprev` (label of vertex `b - 1`) reappears at the
    new right endpoint `b - 1 + p`, and nowhere strictly in between (the
    interior positions hold the last label `llast ≠ lprev` at `b` and fresh
    labels `≥ next > lprev` afterwards). This is the per-block position
    record for the packet geometry. -/
theorem packetStep_elementary {w : List Nat} {b next lprev llast p : Nat}
    (hp : 2 ≤ p) (hinv : PacketInv w b next lprev llast) :
    IsElementaryReturn (w ++ (List.range' next (p - 2) ++ [lprev]))
      lprev (b - 1) (b - 1 + p) := by
  obtain ⟨hrw, hlen, hmax, hnext, hb, hlast, hlprev_le, hlprev_ne, hwprev⟩ := hinv
  have hseglen : (List.range' next (p - 2) ++ [lprev]).length = p - 1 := by
    simp only [List.length_append, List.length_range', List.length_singleton]
    omega
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · -- b - 1 + p < (w ++ seg).length
    simp only [List.length_append, hseglen, hlen]
    omega
  · -- (w ++ seg)[b - 1]? = some lprev: left endpoint label is tracked
    rw [List.getElem?_append_left (by omega : b - 1 < w.length)]
    exact hwprev
  · -- (w ++ seg)[b - 1 + p]? = some lprev: the closing label of the segment
    have h1 : b - 1 + p = w.length + (p - 2) := by omega
    have hrl : (List.range' next (p - 2)).length = p - 2 := List.length_range'
    rw [h1, List.getElem?_append_right (by omega : w.length ≤ w.length + (p - 2)),
      show w.length + (p - 2) - w.length = p - 2 by omega,
      List.getElem?_append_right (by omega : (List.range' next (p - 2)).length ≤ p - 2),
      show p - 2 - (List.range' next (p - 2)).length = 0 by omega]
    rfl
  · -- no occurrence of lprev strictly between the endpoints
    intro k hk1 hk2
    by_cases hkb : k ≤ b
    · -- k = b: the old last label llast ≠ lprev
      have hkb2 : k = b := by omega
      have h1 : (w ++ (List.range' next (p - 2) ++ [lprev]))[k]? = w[k]? :=
        List.getElem?_append_left (by omega)
      rw [h1, hkb2, show b = w.length - 1 by omega, ← List.getLast?_eq_getElem?, hlast]
      exact fun hcon => hlprev_ne.symm (Option.some_inj.mp hcon)
    · -- b + 1 ≤ k: fresh labels are ≥ next > lprev
      have hkb2 : b + 1 ≤ k := by omega
      have h3 : (w ++ (List.range' next (p - 2) ++ [lprev]))[k]?
          = ((List.range' next (p - 2)) ++ [lprev])[k - w.length]? :=
        List.getElem?_append_right (by omega)
      have hrl : (List.range' next (p - 2)).length = p - 2 := List.length_range'
      have h4 : k - w.length < (List.range' next (p - 2)).length := by omega
      rw [h3, List.getElem?_append_left h4]
      intro hcon
      have hmem := List.mem_of_getElem? hcon
      rw [List.mem_range'_1] at hmem
      omega

/-- The multi-prime packet word is a valid return word. This is the
    forward-construction half of paper `thm:return-combination` (ii):
    every list of primes ≥ 2 is realized by a return word. -/
theorem isReturnWord_packetWord (ps : List Nat) (h : ∀ p ∈ ps, 2 ≤ p) :
    IsReturnWord (packetWord ps) := by
  cases ps with
  | nil =>
    show IsReturnWord [0]
    exact IsReturnWord.base
  | cons p ps =>
    have hbase : PacketInv [0, 1] 1 2 0 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply IsReturnWord.step _ _ IsReturnWord.base _ _
        · decide
        · decide
      · rfl
      · rfl
      · decide
      · decide
      · rfl
      · decide
      · decide
      · rfl
    obtain ⟨_b', _next', _lprev', _llast', hinv⟩ :=
      packetWordAux_invariant (p :: ps) [0, 1] 1 2 0 1 h hbase
    exact hinv.1

/-- Old elementary returns survive appending any segment: positions below
    w.length keep their labels, and the "no occurrence between" only
    inspects positions < b < w.length. -/
theorem elementaryReturn_append_preserved {w seg : List Nat} {c a b : Nat}
    (h : IsElementaryReturn w c a b) :
    IsElementaryReturn (w ++ seg) c a b := by
  obtain ⟨hab, hblen, ha, hb, hmid⟩ := h
  refine ⟨hab, ?_, ?_, ?_, ?_⟩
  · -- b < (w ++ seg).length
    simp only [List.length_append]
    omega
  · -- (w ++ seg)[a]? = w[a]? = some c
    rw [List.getElem?_append_left (by omega : a < w.length)]
    exact ha
  · -- (w ++ seg)[b]? = w[b]? = some c
    rw [List.getElem?_append_left (by omega : b < w.length)]
    exact hb
  · -- no c strictly between a and b in w ++ seg
    intro k hk1 hk2
    -- k < b < w.length, so (w ++ seg)[k]? = w[k]? ≠ some c
    rw [List.getElem?_append_left (by omega : k < w.length)]
    exact hmid k hk1 hk2

/-- Singleton packet word unfolds to the explicit block. -/
theorem packetWord_singleton (p : Nat) :
    packetWord [p] = [0, 1] ++ (List.range' 2 (p - 2) ++ [0]) := by
  unfold packetWord packetWordAux
  rfl

/-- Singleton packet word length: 2 + (p - 1) = p + 1. -/
theorem packetWord_singleton_length (p : Nat) (hp : 2 ≤ p) :
    (packetWord [p]).length = p + 1 := by
  rw [packetWord_singleton]
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_range']
  omega

/-- Regression: packetWord [2,2] = [0,1,0,1]. Repeated prime 2 gives
    repeated support length 2 (both labels span 2 edges) — this is why
    the forward construction needs DISTINCT primes. -/
theorem packetWord_two_two : packetWord [2, 2] = [0, 1, 0, 1] := by
  unfold packetWord packetWordAux
  rfl

/-!
P2.1c(iv): the [2,3] two-prime packet regression — the smallest
nontrivial distinct-prime case, mirroring `packetWord_two_two`.

`packetWord [2,3]` unfolds to `[0,1,0,2,1]`: class 0 (prime 2's class)
has the elementary return at endpoints 0, 2 (support length 2), class 1
(prime 3's class) at endpoints 1, 4 (support length 3). Each occurs
exactly twice, the packet is exactly {0, 1}, no class occurs three or
more times, every elementary return is one of the two, and the two
returns overlap (so the overlap graph is the path graph on 2 vertices).
-/

/-- Regression: packetWord [2,3] = [0,1,0,2,1]. -/
theorem packetWord_two_three : packetWord [2, 3] = [0, 1, 0, 2, 1] := by
  unfold packetWord packetWordAux
  rfl

/-- Class 0 (prime 2's class) has an elementary return at endpoints 0, 2:
    support length 2. -/
theorem packetWord_two_three_return_two :
    IsElementaryReturn (packetWord [2, 3]) 0 0 2 := by
  rw [packetWord_two_three]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro k hk1 hk2
  have hk : k = 1 := by omega
  subst hk
  decide

/-- Class 1 (prime 3's class) has an elementary return at endpoints 1, 4:
    support length 3. -/
theorem packetWord_two_three_return_three :
    IsElementaryReturn (packetWord [2, 3]) 1 1 4 := by
  rw [packetWord_two_three]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro k hk1 hk2
  interval_cases k <;> decide

/-- Class 0 occurs exactly twice. -/
theorem packetWord_two_three_occ_two :
    (occurrences (packetWord [2, 3]) 0).card = 2 := by
  rw [packetWord_two_three]
  decide

/-- Class 1 occurs exactly twice. -/
theorem packetWord_two_three_occ_three :
    (occurrences (packetWord [2, 3]) 1).card = 2 := by
  rw [packetWord_two_three]
  decide

/-- The complete return packet of `packetWord [2,3]` is exactly the two
    classes {0, 1}: no other class occurs twice. -/
theorem packetWord_two_three_packet :
    ReturnPacket (packetWord [2, 3]) = {0, 1} := by
  rw [packetWord_two_three]
  decide

/-- No class of `packetWord [2,3]` occurs three or more times. -/
theorem packetWord_two_three_simpleReturn :
    IsSimpleReturn (packetWord [2, 3]) := by
  rw [packetWord_two_three]
  intro c hc
  have hpos : 0 < (occurrences [0, 1, 0, 2, 1] c).card := by
    unfold IsRecurrent at hc
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [occurrences, Finset.mem_filter] at hi
  have hmem : c ∈ [0, 1, 0, 2, 1] := List.mem_of_getElem? hi.2
  have hle : c ≤ 2 := by
    have h := le_listMax hmem
    have hmax : listMax [0, 1, 0, 2, 1] = 2 := rfl
    omega
  interval_cases c
  · decide
  · decide
  · have h2 : (occurrences [0, 1, 0, 2, 1] 2).card = 1 := by decide
    unfold IsRecurrent at hc
    omega

/-- No extra elementary returns: every elementary return of
    `packetWord [2,3]` is one of the two prime-class returns. -/
theorem packetWord_two_three_classify {c a b : Nat}
    (h : IsElementaryReturn (packetWord [2, 3]) c a b) :
    (c = 0 ∧ a = 0 ∧ b = 2) ∨ (c = 1 ∧ a = 1 ∧ b = 4) := by
  rw [packetWord_two_three] at h
  obtain ⟨hab, hblen, ha, hb, -⟩ := h
  have hmem_a : a ∈ occurrences [0, 1, 0, 2, 1] c := by
    simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ha⟩
  have hmem_b : b ∈ occurrences [0, 1, 0, 2, 1] c := by
    simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    exact ⟨hblen, hb⟩
  have hle : c ≤ 2 := by
    rw [occurrences, Finset.mem_filter] at hmem_a
    have hmem : c ∈ [0, 1, 0, 2, 1] := List.mem_of_getElem? hmem_a.2
    have h := le_listMax hmem
    have hmax : listMax [0, 1, 0, 2, 1] = 2 := rfl
    omega
  interval_cases c
  · have hocc : occurrences [0, 1, 0, 2, 1] 0 = {0, 2} := by decide
    rw [hocc] at hmem_a hmem_b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem_a hmem_b
    rcases hmem_a with rfl | rfl <;> rcases hmem_b with rfl | rfl <;> omega
  · have hocc : occurrences [0, 1, 0, 2, 1] 1 = {1, 4} := by decide
    rw [hocc] at hmem_a hmem_b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem_a hmem_b
    rcases hmem_a with rfl | rfl <;> rcases hmem_b with rfl | rfl <;> omega
  · have hocc : occurrences [0, 1, 0, 2, 1] 2 = {3} := by decide
    rw [hocc] at hmem_a hmem_b
    simp only [Finset.mem_singleton] at hmem_a hmem_b
    omega

/-- The two class returns have distinct support lengths 2 and 3 — the
    input primes — feeding the sector bridge
    `sector_of_distinct_support_lengths`. -/
theorem packetWord_two_three_distinct_support {a b a' b' : Nat}
    (h1 : IsElementaryReturn (packetWord [2, 3]) 0 a b)
    (h2 : IsElementaryReturn (packetWord [2, 3]) 1 a' b') :
    (b - a) ≠ (b' - a') := by
  have hc := packetWord_two_three_classify h1
  have hc' := packetWord_two_three_classify h2
  rcases hc with ⟨-, rfl, rfl⟩ | ⟨h01, -, -⟩
  · rcases hc' with ⟨h10, -, -⟩ | ⟨-, rfl, rfl⟩
    · omega
    · decide
  · omega

/-- The two prime-class returns overlap: their open supports (0,2) and
    (1,4) intersect, so the packet overlap graph is the single edge —
    the path graph on the two vertices. -/
theorem packetWord_two_three_adjacent :
    PacketAdjacent (packetWord [2, 3]) 0 1 :=
  ⟨by decide, 0, 2, 1, 4, packetWord_two_three_return_two,
    packetWord_two_three_return_three, by unfold ReturnsOverlap; decide⟩

/-!
P2.1c(v): the singleton packet word's complete classification — paper
`thm:return-combination`, part (ii), the one-prime case.

For p ≥ 2, `packetWord [p] = [0,1] ++ (List.range' 2 (p-2) ++ [0])`:
label 0 occurs at positions 0 and p (the elementary return of support
length p), label 1 occurs once at position 1, and every other label is
fresh and occurs exactly once. Hence the complete return packet is
exactly {0} and the word is simple-return.
-/

/-- Interior positions of the singleton packet word carry their own
    index as label: position i (2 ≤ i < p) holds the fresh label i. -/
theorem packetWord_singleton_get_interior (p i : Nat) (hp : 2 ≤ p)
    (h2 : 2 ≤ i) (hilt : i < p) :
    ([0, 1] ++ (List.range' 2 (p - 2) ++ [0]))[i]? = some i := by
  have h1 : ([0, 1] : List Nat).length ≤ i := by simp; omega
  rw [List.getElem?_append_right h1]
  have hsub : i - ([0, 1] : List Nat).length = i - 2 := by simp
  rw [hsub]
  have hlen1 : (List.range' 2 (p - 2)).length = p - 2 := List.length_range'
  have h2' : i - 2 < (List.range' 2 (p - 2)).length := by omega
  rw [List.getElem?_append_left h2']
  have hr : (List.range' 2 (p - 2))[i - 2]? = some (2 + 1 * (i - 2)) :=
    List.getElem?_range' (by omega)
  rw [hr]
  have heq : 2 + 1 * (i - 2) = i := by omega
  rw [heq]

/-- Position p of the singleton packet word holds the closing label 0. -/
theorem packetWord_singleton_get_p (p : Nat) (hp : 2 ≤ p) :
    ([0, 1] ++ (List.range' 2 (p - 2) ++ [0]))[p]? = some 0 := by
  have h1 : ([0, 1] : List Nat).length ≤ p := by simp; omega
  rw [List.getElem?_append_right h1]
  have hsub : p - ([0, 1] : List Nat).length = p - 2 := by simp
  rw [hsub]
  have hlen1 : (List.range' 2 (p - 2)).length = p - 2 := List.length_range'
  have h2 : (List.range' 2 (p - 2)).length ≤ p - 2 := by omega
  rw [List.getElem?_append_right h2]
  have hsub2 : p - 2 - (List.range' 2 (p - 2)).length = 0 := by omega
  rw [hsub2]
  decide

/-- Every position of the singleton packet word is classified: label 0 at
    position 0, label 1 at position 1, label 0 at position p, and every
    other position 2 ≤ i < p carries label i. -/
theorem packetWord_singleton_label (p i : Nat) (hp : 2 ≤ p) (hi : i < p + 1) :
    (([0, 1] ++ (List.range' 2 (p - 2) ++ [0]))[i]? = some 0 ∧ i = 0) ∨
    (([0, 1] ++ (List.range' 2 (p - 2) ++ [0]))[i]? = some 1 ∧ i = 1) ∨
    (([0, 1] ++ (List.range' 2 (p - 2) ++ [0]))[i]? = some 0 ∧ i = p) ∨
    (([0, 1] ++ (List.range' 2 (p - 2) ++ [0]))[i]? = some i ∧ 2 ≤ i ∧ i < p) := by
  rcases eq_or_ne i 0 with rfl | h0
  · refine Or.inl ⟨?_, rfl⟩
    simp
  · rcases eq_or_ne i 1 with rfl | h1
    · refine Or.inr (Or.inl ⟨?_, rfl⟩)
      simp
    · rcases eq_or_ne i p with hpi | hpi
      · refine Or.inr (Or.inr (Or.inl ⟨?_, hpi⟩))
        rw [hpi]
        exact packetWord_singleton_get_p p hp
      · refine Or.inr (Or.inr (Or.inr ⟨?_, by omega, by omega⟩))
        exact packetWord_singleton_get_interior p i hp (by omega) (by omega)

/-- Two occurrences of a nonzero class in the singleton packet word
    coincide: every nonzero class occurs at most once. -/
theorem packetWord_singleton_occ_unique (p c : Nat) (hp : 2 ≤ p) (hc : c ≠ 0)
    (i j : Nat)
    (hi : i ∈ occurrences (packetWord [p]) c)
    (hj : j ∈ occurrences (packetWord [p]) c) :
    i = j := by
  rw [packetWord_singleton] at hi hj
  simp only [occurrences, Finset.mem_filter, Finset.mem_range] at hi hj
  obtain ⟨hilt, hgeti⟩ := hi
  obtain ⟨hjlt, hgetj⟩ := hj
  have hlen : (([0, 1] ++ (List.range' 2 (p - 2) ++ [0])) : List Nat).length = p + 1 := by
    have h := packetWord_singleton_length p hp
    rw [packetWord_singleton] at h
    exact h
  have hleni : i < p + 1 := by omega
  have hlenj : j < p + 1 := by omega
  have hzero : ∀ x : Nat, (some (0 : Nat) = some x) → x = 0 :=
    fun x h => (Option.some_inj.mp h).symm
  rcases packetWord_singleton_label p i hp hleni with h | h | h | h
  · obtain ⟨hgi, rfl⟩ := h
    rw [hgi] at hgeti
    exact absurd (hzero c hgeti) hc
  · obtain ⟨hgi, rfl⟩ := h
    rw [hgi] at hgeti
    have hci : c = 1 := (Option.some_inj.mp hgeti).symm
    rcases packetWord_singleton_label p j hp hlenj with h' | h' | h' | h'
    · obtain ⟨hgj, rfl⟩ := h'
      rw [hgj] at hgetj
      exact absurd (hzero c hgetj) hc
    · obtain ⟨hgj, rfl⟩ := h'
      rfl
    · obtain ⟨hgj, rfl⟩ := h'
      rw [hgj] at hgetj
      exact absurd (hzero c hgetj) hc
    · obtain ⟨hgj, -, -⟩ := h'
      rw [hgj] at hgetj
      have hcj : j = c := Option.some_inj.mp hgetj
      omega
  · obtain ⟨hgi, rfl⟩ := h
    rw [hgi] at hgeti
    exact absurd (hzero c hgeti) hc
  · obtain ⟨hgi, -, -⟩ := h
    rw [hgi] at hgeti
    have hci : i = c := Option.some_inj.mp hgeti
    rcases packetWord_singleton_label p j hp hlenj with h' | h' | h' | h'
    · obtain ⟨hgj, rfl⟩ := h'
      rw [hgj] at hgetj
      exact absurd (hzero c hgetj) hc
    · obtain ⟨hgj, rfl⟩ := h'
      rw [hgj] at hgetj
      have hcj : (1 : Nat) = c := Option.some_inj.mp hgetj
      omega
    · obtain ⟨hgj, rfl⟩ := h'
      rw [hgj] at hgetj
      exact absurd (hzero c hgetj) hc
    · obtain ⟨hgj, -, -⟩ := h'
      rw [hgj] at hgetj
      have hcj : j = c := Option.some_inj.mp hgetj
      omega

/-- The singleton packet word has the elementary return of support length
    p: label 0 at endpoints 0 and p, nothing in between. -/
theorem packetWord_singleton_elementary (p : Nat) (hp : 2 ≤ p) :
    IsElementaryReturn (packetWord [p]) 0 0 p := by
  rw [packetWord_singleton]
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_range', List.length_cons,
      List.length_nil]
    omega
  · simp
  · exact packetWord_singleton_get_p p hp
  · intro k hk1 hk2
    by_cases hk : k = 1
    · subst hk
      rw [List.getElem?_append_left (by simp : (1 : Nat) < ([0, 1] : List Nat).length)]
      decide
    · have h2 : 2 ≤ k := by omega
      rw [packetWord_singleton_get_interior p k hp h2 hk2]
      intro hcon
      have hkk := Option.some_inj.mp hcon
      omega

/-- Class 0 occurs exactly at the two endpoints in the singleton packet
    word. -/
theorem packetWord_singleton_occ_zero (p : Nat) (hp : 2 ≤ p) :
    (occurrences (packetWord [p]) 0) = {0, p} := by
  ext i
  rw [packetWord_singleton]
  simp only [occurrences, Finset.mem_filter, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hilt, hget⟩
    have hlen : (([0, 1] ++ (List.range' 2 (p - 2) ++ [0])) : List Nat).length = p + 1 := by
      have h := packetWord_singleton_length p hp
      rw [packetWord_singleton] at h
      exact h
    have hleni : i < p + 1 := by omega
    rcases packetWord_singleton_label p i hp hleni with h | h | h | h
    · obtain ⟨-, rfl⟩ := h
      left
      rfl
    · obtain ⟨hgi, rfl⟩ := h
      rw [hgi] at hget
      have h10 : (1 : Nat) = 0 := Option.some_inj.mp hget
      omega
    · obtain ⟨-, rfl⟩ := h
      right
      rfl
    · obtain ⟨hgi, h2, -⟩ := h
      rw [hgi] at hget
      have hi0 : i = 0 := Option.some_inj.mp hget
      omega
  · intro h
    rcases h with rfl | hpi
    · refine ⟨?_, ?_⟩
      · have hlen := packetWord_singleton_length p hp
        rw [packetWord_singleton] at hlen
        omega
      · simp
    · rw [hpi]
      refine ⟨?_, ?_⟩
      · have hlen := packetWord_singleton_length p hp
        rw [packetWord_singleton] at hlen
        omega
      · exact packetWord_singleton_get_p p hp

/-- The complete return packet of the singleton packet word is exactly
    {0}: no other class occurs twice. -/
theorem packetWord_singleton_packet (p : Nat) (hp : 2 ≤ p) :
    ReturnPacket (packetWord [p]) = {0} := by
  ext c
  simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · intro ⟨_, hcard⟩
    by_cases hc : c = 0
    · exact hc
    · have h2 : 1 < (occurrences (packetWord [p]) c).card := by omega
      rw [Finset.one_lt_card] at h2
      obtain ⟨i, hi, j, hj, hne⟩ := h2
      have heq := packetWord_singleton_occ_unique p c hp hc i j hi hj
      exact absurd heq hne
  · intro hc
    subst hc
    have hne : p ≠ 0 := by omega
    have h02 : (({0, p} : Finset Nat)).card = 2 := by
      rw [Finset.card_insert_of_notMem (fun h => hne (Finset.mem_singleton.mp h).symm),
        Finset.card_singleton]
    refine ⟨?_, ?_⟩
    · simp
    · rw [packetWord_singleton_occ_zero p hp]
      exact h02

/-- The singleton packet word is simple-return: every recurrent class
    occurs exactly twice. -/
theorem packetWord_singleton_simpleReturn (p : Nat) (hp : 2 ≤ p) :
    IsSimpleReturn (packetWord [p]) := by
  intro c hrec
  unfold IsRecurrent at hrec
  by_cases hc : c = 0
  · subst hc
    have hne : p ≠ 0 := by omega
    have h02 : (({0, p} : Finset Nat)).card = 2 := by
      rw [Finset.card_insert_of_notMem (fun h => hne (Finset.mem_singleton.mp h).symm),
        Finset.card_singleton]
    rw [packetWord_singleton_occ_zero p hp]
    exact h02
  · have h2 : 1 < (occurrences (packetWord [p]) c).card := by omega
    rw [Finset.one_lt_card] at h2
    obtain ⟨i, hi, j, hj, hne⟩ := h2
    have heq := packetWord_singleton_occ_unique p c hp hc i j hi hj
    exact absurd heq hne

/-!
P2.1c(v): per-block geometric records for the multi-prime packet word.

`blockRecordsAux` threads the same state as `packetWordAux` and records,
for each prime block, the triple `(c, a, b)` = (left-endpoint label, left
endpoint, right endpoint). The results below show that every recorded block
is an elementary return of the final packet word
(`packetWordAux_blocks_elementary`, `packetWord_blocks_elementary`) and that
the support length `b - a` of each block is exactly the corresponding input
prime (`blockRecordsAux_support`). Together with `isReturnWord_packetWord`,
this is the per-block geometric data for the forward construction of paper
`thm:return-combination` (ii).
-/

/-- Per-block geometric records threaded alongside `packetWordAux`: each
    record `(c, a, b)` is the left-endpoint label, the left endpoint, and
    the right endpoint of one prime block's elementary return. The state
    threading is identical to `packetWordAux`, so the records line up with
    the blocks of the final packet word. -/
def blockRecordsAux : List Nat → Nat → Nat → Nat → Nat → List (Nat × Nat × Nat)
  | [], _, _, _, _ => []
  | p :: ps, b, next, lprev, llast =>
    let lprev' := if p = 2 then llast else next + (p - 3)
    (lprev, b - 1, b - 1 + p) ::
      blockRecordsAux ps (b - 1 + p) (next + (p - 2)) lprev' lprev

/-- The packet-word builder only ever appends: its output is the input word
    followed by a suffix. Technical lemma so that per-step elementary
    returns (proved on `w ++ seg`) promote to the final word. -/
theorem packetWordAux_append_suffix (ps : List Nat) (w : List Nat)
    (b next lprev llast : Nat) :
    ∃ suffix, packetWordAux ps w b next lprev llast = w ++ suffix := by
  induction ps generalizing w b next lprev llast with
  | nil =>
    exact ⟨[], by simp [packetWordAux]⟩
  | cons p ps ih =>
    -- One builder step, definitionally:
    -- `packetWordAux (p::ps) w … = packetWordAux ps (w ++ seg) (b-1+p) … lprev`.
    show ∃ suffix, packetWordAux ps (w ++ (List.range' next (p - 2) ++ [lprev]))
      (b - 1 + p) (next + (p - 2)) (if p = 2 then llast else next + (p - 3)) lprev
      = w ++ suffix
    obtain ⟨suf, hsuf⟩ := ih (w ++ (List.range' next (p - 2) ++ [lprev]))
      (b - 1 + p) (next + (p - 2)) (if p = 2 then llast else next + (p - 3)) lprev
    exact ⟨(List.range' next (p - 2) ++ [lprev]) ++ suf,
      hsuf.trans (List.append_assoc _ _ _)⟩

/-- Every recorded block is an elementary return of the final packet word.
    The head record comes from `packetStep_elementary` on `w ++ seg` and
    survives the remaining suffix by `elementaryReturn_append_preserved`;
    tail records come from the induction hypothesis via `packetStep_invariant`.
    This is the geometric heart of the forward construction of paper
    `thm:return-combination` (ii): each input prime contributes one
    elementary return. -/
theorem packetWordAux_blocks_elementary (ps : List Nat) (w : List Nat)
    (b next lprev llast : Nat) (hall : ∀ p ∈ ps, 2 ≤ p)
    (hinv : PacketInv w b next lprev llast) :
    ∀ r ∈ blockRecordsAux ps b next lprev llast,
      IsElementaryReturn (packetWordAux ps w b next lprev llast) r.1 r.2.1 r.2.2 := by
  induction ps generalizing w b next lprev llast with
  | nil =>
    intro r hr
    simp [blockRecordsAux] at hr
  | cons p ps ih =>
    intro r hr
    have hp2 : 2 ≤ p := hall p (by simp)
    have hps : ∀ q ∈ ps, 2 ≤ q := fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hstep := packetStep_invariant hp2 hinv
    -- Unfold one step of the record builder (definitional, as for `packetWordAux`).
    have hrec : blockRecordsAux (p :: ps) b next lprev llast =
        (lprev, b - 1, b - 1 + p) ::
          blockRecordsAux ps (b - 1 + p) (next + (p - 2))
            (if p = 2 then llast else next + (p - 3)) lprev := rfl
    rw [hrec, List.mem_cons] at hr
    rcases hr with rfl | hmem
    · -- Head record: the step's elementary return, promoted past the suffix.
      obtain ⟨suf, hsuf⟩ := packetWordAux_append_suffix ps
        (w ++ (List.range' next (p - 2) ++ [lprev])) (b - 1 + p) (next + (p - 2))
        (if p = 2 then llast else next + (p - 3)) lprev
      have hbase := packetStep_elementary hp2 hinv
      have hprom := elementaryReturn_append_preserved (seg := suf) hbase
      rw [← hsuf] at hprom
      exact hprom
    · -- Tail records: induction hypothesis at the stepped state.
      exact ih _ _ _ _ _ hps hstep _ hmem

/-- The support length `b - a` of each recorded block equals the
    corresponding input prime: the packet's elementary returns have exactly
    the prescribed support lengths. Used in the forward construction of
    paper `thm:return-combination` (ii) to read the prime list off the
    geometry. -/
theorem blockRecordsAux_support (ps : List Nat) (b next lprev llast : Nat) :
    List.map (fun r => r.2.2 - r.2.1) (blockRecordsAux ps b next lprev llast)
      = ps := by
  induction ps generalizing b next lprev llast with
  | nil =>
    simp [blockRecordsAux]
  | cons p ps ih =>
    have hrec : blockRecordsAux (p :: ps) b next lprev llast =
        (lprev, b - 1, b - 1 + p) ::
          blockRecordsAux ps (b - 1 + p) (next + (p - 2))
            (if p = 2 then llast else next + (p - 3)) lprev := rfl
    have hdiff : (b - 1 + p) - (b - 1) = p := by omega
    rw [hrec, List.map_cons, ih _ _ _ _]
    show ((b - 1 + p) - (b - 1)) :: ps = p :: ps
    rw [hdiff]

/-- Public version for `packetWord`: every block record of the multi-prime
    packet word is an elementary return of that word. Packages
    `packetWordAux_blocks_elementary` at the base state `[0, 1]`, completing
    the per-block geometric data for the forward construction of paper
    `thm:return-combination` (ii). -/
theorem packetWord_blocks_elementary (ps : List Nat) (h : ∀ p ∈ ps, 2 ≤ p) :
    ∀ r ∈ blockRecordsAux ps 1 2 0 1,
      IsElementaryReturn (packetWord ps) r.1 r.2.1 r.2.2 := by
  cases ps with
  | nil =>
    intro r hr
    simp [blockRecordsAux] at hr
  | cons p ps =>
    have hbase : PacketInv [0, 1] 1 2 0 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply IsReturnWord.step _ _ IsReturnWord.base _ _
        · decide
        · decide
      · rfl
      · rfl
      · decide
      · decide
      · rfl
      · decide
      · decide
      · rfl
    -- `packetWord (p::ps)` is definitionally `packetWordAux (p::ps) [0,1] 1 2 0 1`.
    exact packetWordAux_blocks_elementary (p :: ps) [0, 1] 1 2 0 1 h hbase

/-!
P2.1c(vi): block-record class labels strictly increase for strictly
increasing input.

Paper `thm:return-combination` (ii) realizes "every nonempty finite set of
distinct primes" — after increasing sort. For a strictly increasing prime
list, the per-block class labels (`lprev` values) are pairwise distinct: no
two blocks share a class. This is the combinatorial prerequisite for the
exact-packet theorem (each block class then occurs exactly twice, with no
extra returns). The increasing sort is essential: e.g.
`packetWord [3, 2, 5] = [0, 1, 2, 0, 2, 3, 4, 5, 0]` reuses class 0 three
times, because a `p = 2` block swaps `lprev`/`llast` (see `packetWordAux`).
-/

/-- Lower bound: every block-record class is at least the current `lprev`.
    The `p = 2` step swaps `lprev`/`llast`, so it needs `lprev < llast` when
    the head is `2`; with a strictly increasing list, a later head can never
    be `2` again, so the condition is only ever needed at the top level. -/
theorem blockRecordsAux_classes_lb (ps : List Nat) (w : List Nat)
    (b next lprev llast : Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p)
    (hinv : PacketInv w b next lprev llast)
    (hhead : ps.head? = some 2 → lprev < llast) :
    ∀ r ∈ blockRecordsAux ps b next lprev llast, lprev ≤ r.1 := by
  induction ps generalizing w b next lprev llast with
  | nil =>
    intro r hr
    simp [blockRecordsAux] at hr
  | cons p ps ih =>
    have hp2 : 2 ≤ p := hall p (by simp)
    have hsort' : ps.SortedLT :=
      List.Pairwise.sortedLT
        (List.pairwise_cons.mp (List.SortedLT.pairwise hsort)).2
    have hall' : ∀ q ∈ ps, 2 ≤ q := fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hstep := packetStep_invariant hp2 hinv
    have hrec : blockRecordsAux (p :: ps) b next lprev llast =
        (lprev, b - 1, b - 1 + p) ::
          blockRecordsAux ps (b - 1 + p) (next + (p - 2))
            (if p = 2 then llast else next + (p - 3)) lprev := rfl
    obtain ⟨_, _, _, hnext2, _, _, hlprev_le, _, _⟩ := hinv
    -- the next state's `lprev` is at least the current one
    have hle : lprev ≤ (if p = 2 then llast else next + (p - 3)) := by
      by_cases hpeq : p = 2
      · subst hpeq
        rw [if_pos rfl]
        exact le_of_lt (hhead rfl)
      · rw [if_neg hpeq]
        have h3 : 3 ≤ p := by omega
        omega
    -- the tail's head can never be `2` again
    have hhead' : ps.head? = some 2 →
        (if p = 2 then llast else next + (p - 3)) < lprev := by
      intro h2head
      have h2mem : 2 ∈ ps := List.mem_of_mem_head? (by simp [h2head])
      have hpw := List.pairwise_cons.mp (List.SortedLT.pairwise hsort)
      have hpq : p < 2 := hpw.1 2 h2mem
      omega
    intro r hr
    rw [hrec, List.mem_cons] at hr
    rcases hr with rfl | hmem
    · exact le_refl lprev
    · exact le_trans hle
        (ih _ _ _ _ _ hsort' hall' hstep hhead' _ hmem)

/-- For a strictly increasing prime list, the block-record class labels are
    strictly increasing — hence pairwise distinct. With
    `blockRecordsAux_support` (support lengths = the input list) this says
    distinct blocks have distinct classes and distinct support lengths, the
    input data for the exact-packet theorem of paper
    `thm:return-combination` (ii). -/
theorem blockRecordsAux_classes_sorted (ps : List Nat) (w : List Nat)
    (b next lprev llast : Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p)
    (hinv : PacketInv w b next lprev llast)
    (hhead : ps.head? = some 2 → lprev < llast) :
    (List.map (fun r : Nat × Nat × Nat => r.1)
      (blockRecordsAux ps b next lprev llast)).SortedLT := by
  induction ps generalizing w b next lprev llast with
  | nil =>
    have hnil : (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux [] b next lprev llast)).Pairwise (· < ·) := by
      simp [blockRecordsAux]
    exact List.Pairwise.sortedLT hnil
  | cons p ps ih =>
    have hp2 : 2 ≤ p := hall p (by simp)
    have hsort' : ps.SortedLT :=
      List.Pairwise.sortedLT
        (List.pairwise_cons.mp (List.SortedLT.pairwise hsort)).2
    have hall' : ∀ q ∈ ps, 2 ≤ q := fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hstep := packetStep_invariant hp2 hinv
    have hrec : blockRecordsAux (p :: ps) b next lprev llast =
        (lprev, b - 1, b - 1 + p) ::
          blockRecordsAux ps (b - 1 + p) (next + (p - 2))
            (if p = 2 then llast else next + (p - 3)) lprev := rfl
    obtain ⟨_, _, _, hnext2, _, _, hlprev_le, _, _⟩ := hinv
    have hlt : lprev < (if p = 2 then llast else next + (p - 3)) := by
      by_cases hpeq : p = 2
      · subst hpeq
        rw [if_pos rfl]
        exact hhead rfl
      · rw [if_neg hpeq]
        have h3 : 3 ≤ p := by omega
        omega
    have hhead' : ps.head? = some 2 →
        (if p = 2 then llast else next + (p - 3)) < lprev := by
      intro h2head
      have h2mem : 2 ∈ ps := List.mem_of_mem_head? (by simp [h2head])
      have hpw := List.pairwise_cons.mp (List.SortedLT.pairwise hsort)
      have hpq : p < 2 := hpw.1 2 h2mem
      omega
    rw [hrec, List.map_cons]
    apply List.Pairwise.sortedLT
    rw [List.pairwise_cons]
    refine ⟨?_, List.SortedLT.pairwise
      (ih _ _ _ _ _ hsort' hall' hstep hhead')⟩
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    have hlb := blockRecordsAux_classes_lb ps
      (w ++ (List.range' next (p - 2) ++ [lprev]))
      (b - 1 + p) (next + (p - 2))
      (if p = 2 then llast else next + (p - 3)) lprev
      hsort' hall' hstep hhead' r hr
    exact lt_of_lt_of_le hlt hlb

/-- Public version at the `packetWord` base state: for a strictly increasing
    list of primes `≥ 2`, the block classes of the multi-prime packet word
    are strictly increasing. -/
theorem packetWord_classes_sorted (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p) :
    (List.map (fun r : Nat × Nat × Nat => r.1)
      (blockRecordsAux ps 1 2 0 1)).SortedLT := by
  cases ps with
  | nil =>
    have hnil : (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux [] 1 2 0 1)).Pairwise (· < ·) := by
      simp [blockRecordsAux]
    exact List.Pairwise.sortedLT hnil
  | cons p ps =>
    have hbase : PacketInv [0, 1] 1 2 0 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply IsReturnWord.step _ _ IsReturnWord.base _ _
        · decide
        · decide
      · rfl
      · rfl
      · decide
      · decide
      · rfl
      · decide
      · decide
      · rfl
    have hhead : (p :: ps).head? = some 2 → 0 < 1 := fun _ => Nat.zero_lt_one
    exact blockRecordsAux_classes_sorted (p :: ps) [0, 1] 1 2 0 1
      hsort hall hbase hhead

/-- The block support lengths are strictly increasing for strictly increasing
    input — the distinct-length input for `sector_of_distinct_support_lengths`. -/
theorem packetWord_blocks_support_sorted (ps : List Nat) (hsort : ps.SortedLT) :
    (List.map (fun r : Nat × Nat × Nat => r.2.2 - r.2.1)
      (blockRecordsAux ps 1 2 0 1)).SortedLT := by
  have hsup := blockRecordsAux_support ps 1 2 0 1
  rw [hsup]
  exact hsort

/-!
### Exact-packet counting infrastructure (P2.1)

For a strictly increasing list of primes `≥ 2`, the complete return packet
of `packetWord ps` is exactly the set of block-record classes: each occurs
twice (its block's elementary-return endpoints) and no other class occurs
twice. The proof is a counting argument: the `n` recorded classes are
pairwise distinct (strictly increasing) with `≥ 2` occurrences each, every
other class `0..max` occurs `≥ 1` time (return-word coverage), and the word
length equals `(max + 1) + n` — forcing equality everywhere.
-/

/-- Builder output length: each block appends `p - 1` positions. -/
theorem packetWordAux_length (ps : List Nat) (w : List Nat)
    (b next lprev llast : Nat) (hall : ∀ p ∈ ps, 2 ≤ p) :
    (packetWordAux ps w b next lprev llast).length
      = w.length + (ps.map (fun p => p - 1)).sum := by
  induction ps generalizing w b next lprev llast with
  | nil =>
    have h0 : packetWordAux [] w b next lprev llast = w := rfl
    rw [h0]
    simp
  | cons p ps ih =>
    have hp2 : 2 ≤ p := hall p (by simp)
    have hps : ∀ q ∈ ps, 2 ≤ q := fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hrec : packetWordAux (p :: ps) w b next lprev llast =
        packetWordAux ps (w ++ (List.range' next (p - 2) ++ [lprev])) (b - 1 + p)
          (next + (p - 2)) (if p = 2 then llast else next + (p - 3)) lprev := rfl
    rw [hrec, ih _ _ _ _ _ hps]
    simp only [List.length_append, List.length_range', List.length_singleton,
      List.map_cons, List.sum_cons]
    omega

/-- Builder max: `listMax + 1` grows by `p - 2` per block (the invariant
    carries the max, so no direct segment-max computation is needed). -/
theorem packetWordAux_listMax_succ (ps : List Nat) (w : List Nat)
    (b next lprev llast : Nat)
    (hall : ∀ p ∈ ps, 2 ≤ p) (hinv : PacketInv w b next lprev llast) :
    listMax (packetWordAux ps w b next lprev llast) + 1
      = next + (ps.map (fun p => p - 2)).sum := by
  induction ps generalizing w b next lprev llast with
  | nil =>
    obtain ⟨_, _, hmax, hnext2, _, _, _, _, _⟩ := hinv
    have h0 : packetWordAux [] w b next lprev llast = w := rfl
    rw [h0, hmax]
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  | cons p ps ih =>
    have hp2 : 2 ≤ p := hall p (by simp)
    have hps : ∀ q ∈ ps, 2 ≤ q := fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hstep := packetStep_invariant hp2 hinv
    have hrec : packetWordAux (p :: ps) w b next lprev llast =
        packetWordAux ps (w ++ (List.range' next (p - 2) ++ [lprev])) (b - 1 + p)
          (next + (p - 2)) (if p = 2 then llast else next + (p - 3)) lprev := rfl
    rw [hrec, ih _ _ _ _ _ hps hstep]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Every label `≤ listMax` of a return word occurs in it (first-occurrence
    normalization: new labels are forced to be exactly `max + 1`). -/
theorem returnWord_mem_of_le_max {w : List Nat} (h : IsReturnWord w)
    {c : Nat} (hc : c ≤ listMax w) : c ∈ w := by
  induction h with
  | base =>
    have hc0 : c = 0 := by
      simp only [listMax_cons, listMax_nil] at hc
      omega
    subst hc0
    simp
  | step w l hw _ _ ih =>
    rw [listMax_append_single] at hc
    by_cases hcl : c = l
    · subst hcl
      exact List.mem_append_right w (by simp)
    · have hc' : c ≤ listMax w := by omega
      exact List.mem_append_left [l] (ih hc')

/-- A label occurring in `w` has positive occurrence count. -/
theorem one_le_card_occurrences_of_mem {w : List Nat} {c : Nat} (h : c ∈ w) :
    1 ≤ (occurrences w c).card := by
  obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem h
  have hmem : i ∈ occurrences w c := by
    simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    exact ⟨hi, by rw [List.getElem?_eq_getElem hi, hiw]⟩
  exact Finset.card_pos.mpr ⟨i, hmem⟩

/-- Occurrence counts partition the word: they sum to its length. -/
theorem sum_card_occurrences_eq_length (w : List Nat) :
    (Finset.range (listMax w + 1)).sum (fun c => (occurrences w c).card)
      = w.length := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (listMax w + 1)))
      (fun c => occurrences w c) := by
    intro c _ c' _ hne
    simp only [Finset.disjoint_left, occurrences, Finset.mem_filter,
      Finset.mem_range]
    intro i hi hi'
    exact hne (Option.some_inj.mp (hi.2.symm.trans hi'.2))
  have hunion : (Finset.range (listMax w + 1)).biUnion (fun c => occurrences w c)
      = Finset.range w.length := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_range, occurrences,
      Finset.mem_filter]
    constructor
    · rintro ⟨c, -, hi, -⟩
      exact hi
    · intro hi
      refine ⟨w[i], Nat.lt_succ_of_le (le_listMax (List.getElem_mem hi)), hi, ?_⟩
      rw [List.getElem?_eq_getElem hi]
  rw [← Finset.card_biUnion hdisj, hunion, Finset.card_range]

/-!
### Exact packet for sorted input (P2.1)

For a strictly increasing list `ps` with every term `≥ 2`, the complete
return packet of `packetWord ps` is exactly the set of block-record classes:
each occurs twice (its block's elementary-return endpoints) and no other
class occurs twice. Paper fidelity: the hypotheses are exactly
strict-sortedness + `≥ 2` — no primality needed, and unsorted input like
`[3,2,5]` is excluded (there class `0` occurs three times).
-/

/-- `Σ (p - 1) = Σ (p - 2) + #ps` for a list with all terms `≥ 2`. -/
theorem sum_pred_eq {ps : List Nat} (hall : ∀ p ∈ ps, 2 ≤ p) :
    (ps.map (fun p => p - 1)).sum = (ps.map (fun p => p - 2)).sum + ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp2 : 2 ≤ p := hall p (by simp)
    have hps : ∀ q ∈ ps, 2 ≤ q := fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hih := ih hps
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- The counting identity: the packet word's length is `(max + 1) + #blocks`. -/
theorem packetWord_length_eq (ps : List Nat) (hall : ∀ p ∈ ps, 2 ≤ p) :
    (packetWord ps).length = listMax (packetWord ps) + 1 + ps.length := by
  cases ps with
  | nil =>
    show [0].length = listMax [0] + 1 + ([] : List Nat).length
    rfl
  | cons p ps' =>
    have hbase : PacketInv [0, 1] 1 2 0 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply IsReturnWord.step _ _ IsReturnWord.base _ _
        · decide
        · decide
      · rfl
      · rfl
      · decide
      · decide
      · rfl
      · decide
      · decide
      · rfl
    have hWeq : packetWord (p :: ps') = packetWordAux (p :: ps') [0, 1] 1 2 0 1 :=
      rfl
    have hlen := packetWordAux_length (p :: ps') [0, 1] 1 2 0 1 hall
    have hmax := packetWordAux_listMax_succ (p :: ps') [0, 1] 1 2 0 1 hall hbase
    have hsum := sum_pred_eq hall
    have h2 : ([0, 1] : List Nat).length = 2 := rfl
    rw [hWeq]
    omega

/-- Recorded block classes never exceed the final word's max. -/
theorem blockRecordsAux_classes_le_listMax (ps : List Nat) (w : List Nat)
    (b next lprev llast : Nat)
    (hall : ∀ p ∈ ps, 2 ≤ p) (hinv : PacketInv w b next lprev llast) :
    ∀ r ∈ blockRecordsAux ps b next lprev llast,
      r.1 ≤ listMax (packetWordAux ps w b next lprev llast) := by
  induction ps generalizing w b next lprev llast with
  | nil =>
    intro r hr
    simp [blockRecordsAux] at hr
  | cons p ps ih =>
    have hp2 : 2 ≤ p := hall p (by simp)
    have hps : ∀ q ∈ ps, 2 ≤ q := fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hstep := packetStep_invariant hp2 hinv
    have hrec : blockRecordsAux (p :: ps) b next lprev llast =
        (lprev, b - 1, b - 1 + p) ::
          blockRecordsAux ps (b - 1 + p) (next + (p - 2))
            (if p = 2 then llast else next + (p - 3)) lprev := rfl
    have hW : packetWordAux (p :: ps) w b next lprev llast =
        packetWordAux ps (w ++ (List.range' next (p - 2) ++ [lprev])) (b - 1 + p)
          (next + (p - 2)) (if p = 2 then llast else next + (p - 3)) lprev := rfl
    obtain ⟨_, _, _, hnext2, _, _, hlprev_le, _, _⟩ := hinv
    have hnext_le : next ≤
        listMax (packetWordAux (p :: ps) w b next lprev llast) + 1 := by
      rw [hW, packetWordAux_listMax_succ _ _ _ _ _ _ hps hstep]
      have hnn : 0 ≤ (ps.map (fun p => p - 2)).sum := Nat.zero_le _
      omega
    intro r hr
    rw [hrec, List.mem_cons] at hr
    rcases hr with rfl | hmem
    · show lprev ≤ listMax (packetWordAux (p :: ps) w b next lprev llast)
      omega
    · rw [hW]
      exact ih _ _ _ _ _ hps hstep _ hmem

/-- An elementary return's class occurs at least twice. -/
theorem two_le_card_occurrences_of_elementary {w : List Nat} {c a b : Nat}
    (h : IsElementaryReturn w c a b) : 2 ≤ (occurrences w c).card := by
  obtain ⟨hab, hblen, ha, hb, -⟩ := h
  have ha' : a ∈ occurrences w c := by
    simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ha⟩
  have hb' : b ∈ occurrences w c := by
    simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hb⟩
  have hsub : ({a, b} : Finset Nat) ⊆ occurrences w c := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha'
    · exact hb'
  have hcard : ({a, b} : Finset Nat).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
      Finset.card_singleton]
  calc 2 = ({a, b} : Finset Nat).card := hcard.symm
    _ ≤ (occurrences w c).card := Finset.card_le_card hsub

/-- If every term of a finset sum is `≥ k` and the sum equals `k * card`,
    every term equals `k`. -/
theorem forall_eq_of_sum_eq_card_mul {s : Finset Nat} {f : Nat → Nat} {k : Nat}
    (hge : ∀ x ∈ s, k ≤ f x) (hsum : s.sum f = k * s.card) :
    ∀ x ∈ s, f x = k := by
  have hdecomp : s.sum f = s.sum (fun x => (f x - k) + k) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (Nat.sub_add_cancel (hge x hx)).symm
  rw [Finset.sum_add_distrib] at hdecomp
  have hk_sum : s.sum (fun _ => k) = k * s.card := by
    simp [Finset.sum_const, mul_comm]
  rw [hsum, hk_sum] at hdecomp
  have hzero : s.sum (fun x => f x - k) = 0 := by omega
  have hall0 := (Finset.sum_eq_zero_iff_of_nonneg
    (s := s) (f := fun x => f x - k) (fun x _ => Nat.zero_le _)).mp hzero
  intro x hx
  have h0 := hall0 x hx
  have hkx := hge x hx
  omega

/-- `k * card ≤ sum` from pointwise `k ≤ f`, with the `•` resolved. -/
theorem card_le_sum_of_forall_le {s : Finset Nat} {f : Nat → Nat} {k : Nat}
    (h : ∀ x ∈ s, k ≤ f x) : k * s.card ≤ s.sum f := by
  have h' := Finset.card_nsmul_le_sum s f k h
  rw [nsmul_eq_mul, Nat.cast_id, mul_comm] at h'
  exact h'

/-- Counting master lemma: for strictly increasing `ps` (all `≥ 2`), every
    block-record class of `packetWord ps` occurs exactly twice, lies `≤ max`,
    and every other class `≤ max` occurs exactly once. -/
theorem packetWord_class_card (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p) :
    (∀ c ∈ (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux ps 1 2 0 1)).toFinset,
      (occurrences (packetWord ps) c).card = 2) ∧
    (∀ c ∈ (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux ps 1 2 0 1)).toFinset,
      c ≤ listMax (packetWord ps)) ∧
    (∀ c, c ≤ listMax (packetWord ps) →
      c ∉ (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux ps 1 2 0 1)).toFinset →
      (occurrences (packetWord ps) c).card = 1) := by
  -- The block classes are strictly increasing, hence distinct.
  have hsorted : (List.map (fun r : Nat × Nat × Nat => r.1)
      (blockRecordsAux ps 1 2 0 1)).SortedLT :=
    packetWord_classes_sorted ps hsort hall
  have hnodup : (List.map (fun r : Nat × Nat × Nat => r.1)
      (blockRecordsAux ps 1 2 0 1)).Nodup :=
    List.nodup_iff_pairwise_ne.mpr
      ((List.SortedLT.pairwise hsorted).imp (fun h => ne_of_lt h))
  have hcard_cls : (List.map (fun r : Nat × Nat × Nat => r.1)
      (blockRecordsAux ps 1 2 0 1)).toFinset.card = ps.length := by
    rw [List.toFinset_card_of_nodup hnodup, List.length_map]
    have hsup := blockRecordsAux_support ps 1 2 0 1
    have hlen := congrArg List.length hsup
    simp only [List.length_map] at hlen
    exact hlen
  cases ps with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      simp [blockRecordsAux] at hc
    · intro c hc
      simp [blockRecordsAux] at hc
    · intro c hc _
      have hc0 : c = 0 := by
        have hmax0 : listMax (packetWord []) = 0 := rfl
        omega
      subst hc0
      decide
  | cons p ps' =>
    have hW : packetWord (p :: ps') =
        packetWordAux (p :: ps') [0, 1] 1 2 0 1 := rfl
    have hbase : PacketInv [0, 1] 1 2 0 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply IsReturnWord.step _ _ IsReturnWord.base _ _
        · decide
        · decide
      · rfl
      · rfl
      · decide
      · decide
      · rfl
      · decide
      · decide
      · rfl
    -- Every recorded class occurs ≥ 2 (its block's elementary return).
    have hge2 : ∀ c ∈ (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset,
        2 ≤ (occurrences (packetWord (p :: ps')) c).card := by
      intro c hc
      rw [List.mem_toFinset, List.mem_map] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      exact two_le_card_occurrences_of_elementary
        (packetWord_blocks_elementary (p :: ps') hall r hr)
    -- Every recorded class is ≤ max.
    have hle_max : ∀ c ∈ (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset,
        c ≤ listMax (packetWord (p :: ps')) := by
      intro c hc
      rw [List.mem_toFinset, List.mem_map] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      rw [hW]
      exact blockRecordsAux_classes_le_listMax (p :: ps') [0, 1] 1 2 0 1
        hall hbase r hr
    -- Every class ≤ max occurs ≥ 1 (return-word coverage).
    have hge1 : ∀ c, c ≤ listMax (packetWord (p :: ps')) →
        1 ≤ (occurrences (packetWord (p :: ps')) c).card := fun c hc =>
      one_le_card_occurrences_of_mem
        (returnWord_mem_of_le_max (isReturnWord_packetWord (p :: ps') hall) hc)
    have hsub : (List.map (fun r : Nat × Nat × Nat => r.1)
          (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset
          ⊆ Finset.range (listMax (packetWord (p :: ps')) + 1) := by
      intro c hc
      simp only [Finset.mem_range]
      have := hle_max c hc
      omega
    -- Split the total count into recorded classes vs. the rest.
    have hsplit := Finset.sum_sdiff (s₁ := (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset)
      (s₂ := Finset.range (listMax (packetWord (p :: ps')) + 1))
      (f := fun c => (occurrences (packetWord (p :: ps')) c).card) hsub
    have hsum_total := sum_card_occurrences_eq_length (packetWord (p :: ps'))
    have hlen_eq := packetWord_length_eq (p :: ps') hall
    have hcard_rest' : (Finset.range (listMax (packetWord (p :: ps')) + 1) \
        (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset).card +
        (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset.card =
        listMax (packetWord (p :: ps')) + 1 := by
      have hsd := Finset.card_sdiff (s := (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset)
        (t := Finset.range (listMax (packetWord (p :: ps')) + 1))
      rw [Finset.inter_eq_left.mpr hsub, Finset.card_range] at hsd
      have hle := Finset.card_le_card hsub
      simp only [Finset.card_range] at hle
      omega
    have hge1_rest : ∀ c ∈ Finset.range (listMax (packetWord (p :: ps')) + 1) \
        (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset,
        1 ≤ (occurrences (packetWord (p :: ps')) c).card := by
      intro c hc
      obtain ⟨hcr, -⟩ := Finset.mem_sdiff.mp hc
      simp only [Finset.mem_range] at hcr
      exact hge1 c (by omega)
    -- Forcing equality: recorded classes sum to exactly `2n`, rest to `1` each.
    have hforce : ((List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset).sum
        (fun c => (occurrences (packetWord (p :: ps')) c).card)
        = 2 * (p :: ps').length := by
      have h1 := card_le_sum_of_forall_le
        (s := (List.map (fun r : Nat × Nat × Nat => r.1)
          (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset)
        (f := fun c => (occurrences (packetWord (p :: ps')) c).card)
        (k := 2) (fun c hc => hge2 c hc)
      have h2 := card_le_sum_of_forall_le
        (s := Finset.range (listMax (packetWord (p :: ps')) + 1) \
          (List.map (fun r : Nat × Nat × Nat => r.1)
          (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset)
        (f := fun c => (occurrences (packetWord (p :: ps')) c).card)
        (k := 1) hge1_rest
      rw [hcard_cls] at h1
      omega
    have heq_cls : ((List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset).sum
        (fun c => (occurrences (packetWord (p :: ps')) c).card)
        = 2 * (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset.card := by
      rw [hcard_cls]
      exact hforce
    have hexact2 := forall_eq_of_sum_eq_card_mul (fun c hc => hge2 c hc) heq_cls
    have heq_rest : (Finset.range (listMax (packetWord (p :: ps')) + 1) \
        (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset).sum
        (fun c => (occurrences (packetWord (p :: ps')) c).card)
        = 1 * (Finset.range (listMax (packetWord (p :: ps')) + 1) \
        (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset).card := by
      have h2 := card_le_sum_of_forall_le
        (s := Finset.range (listMax (packetWord (p :: ps')) + 1) \
          (List.map (fun r : Nat × Nat × Nat => r.1)
          (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset)
        (f := fun c => (occurrences (packetWord (p :: ps')) c).card)
        (k := 1) hge1_rest
      omega
    have hexact1 := forall_eq_of_sum_eq_card_mul hge1_rest heq_rest
    refine ⟨?_, hle_max, ?_⟩
    · intro c hc
      exact hexact2 c hc
    · intro c hc hnc
      have hmem : c ∈ Finset.range (listMax (packetWord (p :: ps')) + 1) \
          (List.map (fun r : Nat × Nat × Nat => r.1)
          (blockRecordsAux (p :: ps') 1 2 0 1)).toFinset := by
        rw [Finset.mem_sdiff]
        simp only [Finset.mem_range]
        exact ⟨by omega, hnc⟩
      exact hexact1 c hmem

/-- Exact packet: for strictly increasing `ps` (all `≥ 2`), the complete
    return packet of `packetWord ps` is exactly the set of block-record
    classes — no more, no fewer. Each class corresponds to one input prime:
    `blockRecordsAux_support` gives the class's elementary return support
    length `ps[k]`, the bidirectional correspondence of paper
    `thm:return-combination` (ii). -/
theorem packetWord_packet_exact (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p) :
    ReturnPacket (packetWord ps) =
      (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux ps 1 2 0 1)).toFinset := by
  obtain ⟨h2, hle, h1⟩ := packetWord_class_card ps hsort hall
  ext c
  simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hc_lt, hc_card⟩
    by_contra hcon
    have h1c := h1 c (by omega) hcon
    omega
  · intro hc
    exact ⟨by have := hle c hc; omega, h2 c hc⟩

/-- Every recurrent class of the sorted packet word occurs exactly twice
    (count-only simple-return for the general packet). -/
theorem isSimpleReturn_packetWord (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p) :
    IsSimpleReturn (packetWord ps) := by
  obtain ⟨h2, -, h1⟩ := packetWord_class_card ps hsort hall
  intro c hc
  unfold IsRecurrent at hc
  by_cases hmax : c ≤ listMax (packetWord ps)
  · by_cases hmem : c ∈ (List.map (fun r : Nat × Nat × Nat => r.1)
        (blockRecordsAux ps 1 2 0 1)).toFinset
    · exact h2 c hmem
    · have h1c := h1 c hmax hmem
      omega
  · -- `c` exceeds the max: no occurrences at all.
    have hempty : occurrences (packetWord ps) c = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      simp only [occurrences, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hi_len, hi_eq⟩ := hi
      rw [List.getElem?_eq_getElem hi_len] at hi_eq
      have hcc : (packetWord ps)[i] = c := Option.some_inj.mp hi_eq
      have hmem : (packetWord ps)[i] ∈ packetWord ps := List.getElem_mem hi_len
      have hle := le_listMax hmem
      omega
    rw [hempty] at hc
    simp at hc

/-!
### Endpoint iff-classification of elementary returns (P2.1)

For a strictly increasing input list (all `≥ 2`), every elementary return
of the final packet word is one of the per-block records: the endpoints
give a full iff-classification (`packetWord_elementary_iff`). The reverse
direction is `packetWord_blocks_elementary`; the forward direction uses the
exact-packet theorem (`packetWord_packet_exact`): an elementary return's
class is recurrent, hence a record class, and its two endpoints must be the
record's endpoints because each record class occurs exactly twice.
-/

/-- Endpoint iff-classification: every elementary return of the general
    packet word is exactly one of the block records (class, left endpoint,
    right endpoint). -/
theorem packetWord_elementary_iff (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p) (c a b : Nat) :
    IsElementaryReturn (packetWord ps) c a b ↔
      ∃ r ∈ blockRecordsAux ps 1 2 0 1, (c, a, b) = (r.1, r.2.1, r.2.2) := by
  constructor
  · intro h
    have hmem := elementaryReturn_mem_occs h
    obtain ⟨hab, hblen, ha, hb, -⟩ := h
    have hne : a ≠ b := by omega
    have hsub : ({a, b} : Finset Nat) ⊆ occurrences (packetWord ps) c := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hmem.1
      · exact hmem.2
    have hcard_ab : ({a, b} : Finset Nat).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have hrec : IsRecurrent (packetWord ps) c := by
      unfold IsRecurrent
      have hle := Finset.card_le_card hsub
      omega
    have hcard2 : (occurrences (packetWord ps) c).card = 2 :=
      isSimpleReturn_packetWord ps hsort hall c hrec
    -- `c` is a record class, by the exact-packet theorem.
    have hc_pkt : c ∈ ReturnPacket (packetWord ps) := by
      simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range]
      have hwa : (packetWord ps)[a] = c := by
        have h1 := List.getElem?_eq_getElem (by omega : a < (packetWord ps).length)
        rw [h1] at ha
        exact Option.some_inj.mp ha
      have hle := le_listMax (List.getElem_mem (by omega : a < (packetWord ps).length))
      refine ⟨by omega, hcard2⟩
    rw [packetWord_packet_exact ps hsort hall] at hc_pkt
    rw [List.mem_toFinset, List.mem_map] at hc_pkt
    obtain ⟨r, hr, hrc⟩ := hc_pkt
    -- The record's elementary return has the same endpoints.
    have hrel : IsElementaryReturn (packetWord ps) c r.2.1 r.2.2 := by
      have hbase := packetWord_blocks_elementary ps hall r hr
      rwa [hrc] at hbase
    have hmem' := elementaryReturn_mem_occs hrel
    have heq : ({a, b} : Finset Nat) = occurrences (packetWord ps) c :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have e1 : r.2.1 ∈ ({a, b} : Finset Nat) := by rw [heq]; exact hmem'.1
    have e2 : r.2.2 ∈ ({a, b} : Finset Nat) := by rw [heq]; exact hmem'.2
    obtain ⟨hrab, -, hra, hrb, -⟩ := hrel
    simp only [Finset.mem_insert, Finset.mem_singleton] at e1 e2
    -- `r.2.1 = a`: it cannot be `b`, since `r.2.1 < r.2.2 ∈ {a, b}`.
    have hra_eq : r.2.1 = a := by
      rcases e1 with h | h
      · exact h
      · exfalso
        rcases e2 with h2 | h2 <;> omega
    have hrb_eq : r.2.2 = b := by
      rcases e2 with h2 | h2
      · omega
      · exact h2
    refine ⟨r, hr, ?_⟩
    exact Prod.ext hrc.symm (Prod.ext hra_eq.symm hrb_eq.symm)
  · rintro ⟨r, hr, hrfl⟩
    have h := packetWord_blocks_elementary ps hall r hr
    have e1 : c = r.1 := congrArg Prod.fst hrfl
    have e2 : a = r.2.1 := congrArg (Prod.fst ∘ Prod.snd) hrfl
    have e3 : b = r.2.2 := congrArg (Prod.snd ∘ Prod.snd) hrfl
    rw [e1, e2, e3]
    exact h

/-!
### Record endpoint distinctness and support-length correspondence (P2.1)

Different block records have different endpoint pairs
(`packetWord_records_endpoints_nodup`): equal endpoint pairs would force
equal classes (both endpoints carry their class label), contradicting the
strictly increasing classes. The `i`-th record's endpoints `(a, b)` satisfy
`b - a = ps[i]` (`packetWord_records_endpoint_support`), the explicit
endpoint-pair form of `blockRecordsAux_support`. Together with the
endpoint iff-classification, this is the bridge from the packet geometry
to the sector condition: distinct-class elementary returns have distinct
support lengths.
-/

/-- Distinct records have distinct endpoint pairs. -/
theorem packetWord_records_endpoints_nodup (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p) :
    ((blockRecordsAux ps 1 2 0 1).map
      (fun r : Nat × Nat × Nat => (r.2.1, r.2.2))).Nodup := by
  have hel : ∀ r ∈ blockRecordsAux ps 1 2 0 1,
      IsElementaryReturn (packetWord ps) r.1 r.2.1 r.2.2 :=
    packetWord_blocks_elementary ps hall
  have hcls : ((blockRecordsAux ps 1 2 0 1).map
      (fun r : Nat × Nat × Nat => r.1)).Pairwise (· < ·) :=
    List.SortedLT.pairwise (packetWord_classes_sorted ps hsort hall)
  have key : ∀ l' : List (Nat × Nat × Nat),
      (∀ r ∈ l', IsElementaryReturn (packetWord ps) r.1 r.2.1 r.2.2) →
      (l'.map (fun r : Nat × Nat × Nat => r.1)).Pairwise (· < ·) →
      (l'.map (fun r : Nat × Nat × Nat => (r.2.1, r.2.2))).Pairwise
        (· ≠ ·) := by
    intro l'
    induction l' with
    | nil => intro _ _; exact List.Pairwise.nil
    | cons x xs ih =>
      intro hel' hcls'
      simp only [List.map_cons] at hcls'
      rw [List.pairwise_cons] at hcls'
      obtain ⟨hx_lt, hcls''⟩ := hcls'
      have ih' := ih (fun r hr => hel' r (List.mem_cons_of_mem x hr)) hcls''
      simp only [List.map_cons]
      rw [List.pairwise_cons]
      refine ⟨?_, ih'⟩
      intro y hy heq
      rw [List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hlt : x.1 < z.1 :=
        hx_lt z.1 (by rw [List.mem_map]; exact ⟨z, hz, rfl⟩)
      have hx_el := hel' x List.mem_cons_self
      have hz_el := hel' z (List.mem_cons_of_mem x hz)
      -- Equal endpoint pairs force equal classes: both left endpoints
      -- carry their class label.
      have hxa : (packetWord ps)[z.2.1]? = some x.1 := by
        have hpos : x.2.1 = z.2.1 := congrArg Prod.fst heq
        rw [← hpos]; exact hx_el.2.2.1
      have hcc : x.1 = z.1 := Option.some_inj.mp (hxa.symm.trans hz_el.2.2.1)
      omega
  rw [List.nodup_iff_pairwise_ne]
  exact key _ hel hcls

/-- Explicit endpoint/support-length correspondence: the `i`-th record's
    endpoints `(a, b)` satisfy `b - a = ps[i]`. -/
theorem packetWord_records_endpoint_support (ps : List Nat)
    (i : Nat) (hi : i < ps.length) :
    ((blockRecordsAux ps 1 2 0 1)[i]?.map
      (fun r : Nat × Nat × Nat => r.2.2 - r.2.1)) = some ps[i] := by
  have hsup := blockRecordsAux_support ps 1 2 0 1
  have h1 : ((blockRecordsAux ps 1 2 0 1).map
      (fun r : Nat × Nat × Nat => r.2.2 - r.2.1))[i]? = ps[i]? := by
    rw [hsup]
  rw [List.getElem?_map] at h1
  have h2 : ps[i]? = some ps[i] := List.getElem?_eq_getElem hi
  rw [h2] at h1
  exact h1

/-!
### General sector bridge (P2.1)

The endpoint iff-classification plus the support-length correspondence
give distinct edge counts for distinct-class elementary returns of the
general packet word (`packetWord_elementary_edge_counts_ne`). Feeding this
into the sector bridges yields the cut-open sector theorem
(`isSimpleReturnSectorCutOpen_packetWord`, the paper-faithful
`prop:return-normal-form` condition) and the legacy raw-pattern sector
theorem (`isSimpleReturnSector_packetWord`, via
`sector_of_distinct_support_lengths`).
-/

/-- Distinct-class elementary returns of the general packet word have
    distinct edge counts: classification pins each return to a record, and
    the records sit at distinct input positions with distinct values
    (the input list is strictly increasing). -/
theorem packetWord_elementary_edge_counts_ne (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p)
    {c a b c' a' b' : Nat}
    (hc : IsElementaryReturn (packetWord ps) c a b)
    (hc' : IsElementaryReturn (packetWord ps) c' a' b')
    (hne : c ≠ c') :
    b - a ≠ b' - a' := by
  rw [packetWord_elementary_iff ps hsort hall] at hc hc'
  obtain ⟨r, hr, hrfl⟩ := hc
  obtain ⟨r', hr', hrfl'⟩ := hc'
  have e1 : c = r.1 := congrArg Prod.fst hrfl
  have e2 : a = r.2.1 := congrArg (Prod.fst ∘ Prod.snd) hrfl
  have e3 : b = r.2.2 := congrArg (Prod.snd ∘ Prod.snd) hrfl
  have e1' : c' = r'.1 := congrArg Prod.fst hrfl'
  have e2' : a' = r'.2.1 := congrArg (Prod.fst ∘ Prod.snd) hrfl'
  have e3' : b' = r'.2.2 := congrArg (Prod.snd ∘ Prod.snd) hrfl'
  -- Record indices in the record list.
  obtain ⟨i, hri⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨j, hrj⟩ := List.mem_iff_getElem?.mp hr'
  have hlen : (blockRecordsAux ps 1 2 0 1).length = ps.length := by
    have h := congrArg List.length (blockRecordsAux_support ps 1 2 0 1)
    simpa only [List.length_map] using h
  obtain ⟨hi_l, -⟩ := List.getElem_of_getElem? hri
  obtain ⟨hj_l, -⟩ := List.getElem_of_getElem? hrj
  have hi_ps : i < ps.length := by omega
  have hj_ps : j < ps.length := by omega
  -- Support lengths read off the input list.
  have hsup_i := packetWord_records_endpoint_support ps i hi_ps
  have hsup_j := packetWord_records_endpoint_support ps j hj_ps
  rw [hri] at hsup_i
  rw [hrj] at hsup_j
  simp only [Option.map_some] at hsup_i hsup_j
  have esup_i : r.2.2 - r.2.1 = ps[i] := Option.some_inj.mp hsup_i
  have esup_j : r'.2.2 - r'.2.1 = ps[j] := Option.some_inj.mp hsup_j
  -- Different classes sit at different input positions ...
  have hcc : r.1 ≠ r'.1 := by
    have hne' := hne
    rwa [e1, e1'] at hne'
  have hij : i ≠ j := by
    intro heq
    subst heq
    have hrr : r = r' := Option.some_inj.mp (hri.symm.trans hrj)
    have h11 : r.1 = r'.1 := congrArg Prod.fst hrr
    exact hcc h11
  -- ... with different input values (strictly increasing input).
  have hps : ps[i] ≠ ps[j] := by
    have hpw := List.SortedLT.pairwise hsort
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have h := (List.pairwise_iff_getElem.mp hpw) i j hi_ps hj_ps hlt
      omega
    · have h := (List.pairwise_iff_getElem.mp hpw) j i hj_ps hi_ps hlt
      omega
  rw [e2, e3, e2', e3', esup_i, esup_j]
  exact hps

/-- General cut-open sector theorem: the packet word of a strictly
    increasing `≥ 2` list satisfies the paper's simple-return sector
    condition (`prop:return-normal-form`) under the cut-open semantics —
    the `sectorCutOpen_of_distinct_edge_counts` bridge applied to the
    general `packetWord`. -/
theorem isSimpleReturnSectorCutOpen_packetWord (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p) :
    IsSimpleReturnSectorCutOpen (packetWord ps) :=
  sectorCutOpen_of_distinct_edge_counts
    (isSimpleReturn_packetWord ps hsort hall)
    (fun _ _ _ _ _ _ hc hc' hne =>
      packetWord_elementary_edge_counts_ne ps hsort hall hc hc' hne)

/-- The general packet word also satisfies the legacy raw-pattern sector
    condition, via the `sector_of_distinct_support_lengths` bridge:
    distinct edge counts give distinct support vertex counts. -/
theorem isSimpleReturnSector_packetWord (ps : List Nat)
    (hsort : ps.SortedLT) (hall : ∀ p ∈ ps, 2 ≤ p) :
    IsSimpleReturnSector (packetWord ps) := by
  apply sector_of_distinct_support_lengths
  · exact isSimpleReturn_packetWord ps hsort hall
  · intro c a b c' a' b' hc hc' hne
    have hne2 := packetWord_elementary_edge_counts_ne ps hsort hall hc hc' hne
    obtain ⟨hab, -, -, -, -⟩ := hc
    obtain ⟨hab', -, -, -, -⟩ := hc'
    omega

end PrimeMother
