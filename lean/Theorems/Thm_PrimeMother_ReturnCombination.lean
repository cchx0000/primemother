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

end PrimeMother
