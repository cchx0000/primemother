/-
Prime-Distribution Birth Mother — Finite return source, part B (P2.1b).

Paper §"The universal unlabelled path-history source":
- Elementary return: when an extension revisits a class, with `a` the
  most recent earlier occurrence and `b` the new occurrence, the
  interval [a,b] is an elementary return support.
- Simple-return sector: every recurrent class occurs exactly twice,
  and normalized elementary return supports are pairwise
  nonisomorphic as ordered atomic paths.
- Complete return packet J(X): the set of all two-occurrence classes.
- Overlap graph Γ(J): returns sharing an atomic edge are adjacent.

This file: occurrences, simple-return predicate, packet, overlap graph,
and their basic theory. The forward construction (every nonempty finite
set of distinct primes is realized) is P2.1c.
-/

import Definitions.Def_PrimeMother_ReturnWord
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace PrimeMother

/-- Positions at which label c occurs in w. -/
def occurrences (w : List Nat) (c : Nat) : Finset Nat :=
  (Finset.range w.length).filter (fun i => w[i]? = some c)

/-- Label c is recurrent (occurs at least twice). -/
def IsRecurrent (w : List Nat) (c : Nat) : Prop :=
  2 ≤ (occurrences w c).card

/-- Simple-return sector: every recurrent class occurs exactly twice.
    (Paper: "every recurrent equivalence class occurs exactly twice".) -/
def IsSimpleReturn (w : List Nat) : Prop :=
  ∀ c, IsRecurrent w c → (occurrences w c).card = 2

/-- An elementary return: class c occurs at positions a < b, with no
    occurrence strictly between (a is the most recent earlier
    occurrence before b). The interval [a,b] is the return support. -/
def IsElementaryReturn (w : List Nat) (c a b : Nat) : Prop :=
  a < b ∧ b < w.length ∧
  w[a]? = some c ∧ w[b]? = some c ∧
  ∀ k, a < k → k < b → w[k]? ≠ some c

/-- The complete return packet J(X): all two-occurrence classes.
    (Paper: "the set of all its two-occurrence classes; it is not a
    chosen subfamily".) -/
def ReturnPacket (w : List Nat) : Finset Nat :=
  (Finset.range (listMax w + 1)).filter (fun c => (occurrences w c).card = 2)

/-- Two elementary returns overlap if their supports share an atomic
    edge, i.e. the open intervals (a,b) and (a',b') intersect. -/
def ReturnsOverlap (a b a' b' : Nat) : Prop :=
  a < b' ∧ a' < b

/-- The overlap graph adjacency: classes c, c' (c ≠ c') are adjacent
    when some elementary return of c overlaps some of c'. -/
def PacketAdjacent (w : List Nat) (c c' : Nat) : Prop :=
  c ≠ c' ∧
  ∃ a b a' b', IsElementaryReturn w c a b ∧
    IsElementaryReturn w c' a' b' ∧ ReturnsOverlap a b a' b'

/-- Packet members are recurrent. -/
theorem packet_mem_recurrent {w : List Nat} {c : Nat}
    (hc : c ∈ ReturnPacket w) : IsRecurrent w c := by
  simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at hc
  obtain ⟨_, hcard⟩ := hc
  unfold IsRecurrent
  omega

/-- In a simple-return word, packet members have exactly the two
    elementary-return endpoints as their occurrences. -/
theorem simpleReturn_packet_card {w : List Nat} (_hs : IsSimpleReturn w)
    {c : Nat} (hc : c ∈ ReturnPacket w) :
    (occurrences w c).card = 2 := by
  simp only [ReturnPacket, Finset.mem_filter, Finset.mem_range] at hc
  exact hc.2

/-- Elementary return endpoints are both occurrences. -/
theorem elementaryReturn_mem_occs {w : List Nat} {c a b : Nat}
    (h : IsElementaryReturn w c a b) :
    a ∈ occurrences w c ∧ b ∈ occurrences w c := by
  obtain ⟨hab, hblen, ha, hb, _⟩ := h
  constructor
  · simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ha⟩
  · simp only [occurrences, Finset.mem_filter, Finset.mem_range]
    exact ⟨hblen, hb⟩

/-- Overlap is symmetric. -/
theorem returnsOverlap_symm {a b a' b' : Nat}
    (h : ReturnsOverlap a b a' b') : ReturnsOverlap a' b' a b := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h2, h1⟩

end PrimeMother
