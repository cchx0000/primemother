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

/-- Simple-return sector, **count-only part**: every recurrent class occurs
    exactly twice. (Paper: "every recurrent equivalence class occurs
    exactly twice".) The paper's full sector condition additionally
    requires the normalized elementary return supports to be pairwise
    nonisomorphic as ordered atomic paths — see `IsSimpleReturnSector`
    below. -/
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

/-!
P2.1 semantic-condition repair: the paper's simple-return sector
(`prop:return-normal-form`) is *not* just the count condition — it also
requires the normalized elementary return supports to be pairwise
nonisomorphic as ordered atomic paths. `IsSimpleReturn` above is kept
as the count-only part; the accurate condition and its
distinct-length bridge are defined here.
-/

/-- Raw label slice of the elementary return spanning positions `[a, b]`:
    the label sequence `w[a], …, w[b]`.

    NOTE (P2.1 cut-open repair): this raw slice is **not** automatically
    first-occurrence normalized. E.g. `[0,1,0,2,1]` is a legal return word,
    but its `[1,4]` slice `[1,0,2,1]` is not the first-occurrence numbering
    `[0,1,2,0]`. Hence the raw slice cannot serve as the paper's normalized
    support: the paper (L994–997) defines unary normalization as the cut-open
    ordered path `N(J) := J`, which drops the quotient vertex-identification
    data — see `cutOpenPath`, `CutOpenPathIso` and
    `IsSimpleReturnSectorCutOpen` below. -/
def returnSupport (w : List Nat) (a b : Nat) : List Nat :=
  (w.drop a).take (b + 1 - a)

/-- The support of `[a, b]` has `b + 1 - a` labels. -/
theorem returnSupport_length {w : List Nat} {a b : Nat} (hle : a ≤ b)
    (hlt : b < w.length) :
    (returnSupport w a b).length = b + 1 - a := by
  unfold returnSupport
  rw [List.length_take, List.length_drop]
  have hle' : b + 1 - a ≤ w.length - a := by omega
  exact Nat.min_eq_left hle'

/-- Ordered-atomic-path isomorphism of two label sequences: equal length
    and identical equality pattern. The pattern is stated with `get?`, so
    out-of-range positions contribute `none` on both sides, which agrees
    exactly when the lengths are equal. -/
def SupportIso (s s' : List Nat) : Prop :=
  s.length = s'.length ∧ ∀ i j : Nat, (s[i]? = s[j]?) ↔ (s'[i]? = s'[j]?)

/-- Different lengths are nonisomorphic. This is the bridge from
    support-length data (e.g. distinct prime lengths) to the paper's
    nonisomorphism requirement. -/
theorem not_supportIso_of_length_ne {s s' : List Nat} (h : s.length ≠ s'.length) :
    ¬ SupportIso s s' :=
  fun hs => h hs.1

/-- The paper's full simple-return sector condition
    (`prop:return-normal-form`, simple-return sector): the count condition
    plus pairwise nonisomorphic normalized elementary return supports
    ("normalized elementary return supports are pairwise nonisomorphic
    as ordered atomic paths"). -/
def IsSimpleReturnSector (w : List Nat) : Prop :=
  IsSimpleReturn w ∧ ∀ c a b c' a' b',
    IsElementaryReturn w c a b → IsElementaryReturn w c' a' b' →
    c ≠ c' → ¬ SupportIso (returnSupport w a b) (returnSupport w a' b')

/-- Bridge into the sector condition: a simple-return word whose
    elementary returns have pairwise distinct support lengths (for
    distinct classes) satisfies the full sector condition. This keeps the
    semantic condition (this file) separate from the
    prime-distinctness theorems, which supply the distinct lengths. -/
theorem sector_of_distinct_support_lengths {w : List Nat}
    (hs : IsSimpleReturn w)
    (hd : ∀ c a b c' a' b', IsElementaryReturn w c a b →
      IsElementaryReturn w c' a' b' → c ≠ c' → (b + 1 - a) ≠ (b' + 1 - a')) :
    IsSimpleReturnSector w := by
  refine ⟨hs, fun c a b c' a' b' hc hc' hne hso => ?_⟩
  obtain ⟨⟨hab, hblen, -, -, -⟩, ⟨hab', hblen', -, -, -⟩⟩ :
    IsElementaryReturn w c a b ∧ IsElementaryReturn w c' a' b' := ⟨hc, hc'⟩
  have hl1 := returnSupport_length (a := a) (b := b) (by omega) hblen
  have hl2 := returnSupport_length (a := a') (b := b') (by omega) hblen'
  have hne2 := hd c a b c' a' b' hc hc' hne
  have hlen : (returnSupport w a b).length ≠ (returnSupport w a' b').length := by omega
  exact not_supportIso_of_length_ne hlen hso

/-!
P2.1 cut-open semantic repair (paper L994–997, L1220–1224).

The paper defines the unary normalization of a return support `J = [a, b]`
as the *cut-open ordered path* `N(J) := J`: the interval itself, viewed as
an ordered atomic path. In particular, the vertex-identification data of the
quotient trace `q` — which the raw label equality pattern retained by
`SupportIso` records — is *not* carried into the normalized path. Two
normalized elementary return supports are therefore isomorphic as ordered
atomic paths exactly when they have the same number of atomic edges;
posteriorly, the sector's nonisomorphism condition is exactly that the
return ranks are distinct (paper L1220–1224). `IsSimpleReturnSector` and
`sector_of_distinct_support_lengths` above are kept unchanged;
`IsSimpleReturnSectorCutOpen` is the paper-faithful version, strictly
narrower than the old sector condition.
-/

/-- The cut-open ordered path of the elementary return support `[a, b]`
    (paper L994–997: `N(J) := J`). It is the plain vertex list
    `[0, …, b - a]` with `b - a` atomic edges — the same vertex count as the
    raw slice `returnSupport w a b` (see `cutOpenPath_length_eq`), but
    carrying no label-equality pattern, unlike the raw slice compared by
    `SupportIso`. The word is kept as an explicit parameter (unused in the
    vertex list itself, which is the point: the cut-open path drops all
    label data) so that cut-open paths are indexed by the same support
    they normalize. -/
def cutOpenPath (_w : List Nat) (a b : Nat) : List Nat :=
  List.range (b + 1 - a)

/-- Isomorphism of cut-open ordered atomic paths: the cut-open version of
    `SupportIso` (paper L1220–1224). An ordered atomic path is determined up
    to isomorphism by its number of atomic edges — the order-preserving
    vertex bijection exists exactly when the two paths have the same number
    of vertices — so isomorphism is stated directly via equal length. -/
def CutOpenPathIso (p p' : List Nat) : Prop :=
  p.length = p'.length

/-- The cut-open path keeps the raw support's vertex count while dropping
    all label data. -/
theorem cutOpenPath_length_eq {w : List Nat} {a b : Nat}
    (hle : a ≤ b) (hlt : b < w.length) :
    (cutOpenPath w a b).length = (returnSupport w a b).length := by
  unfold cutOpenPath
  rw [List.length_range, returnSupport_length hle hlt]

/-- Paper L1220–1224, both directions: two cut-open paths are isomorphic
    exactly when the supports have the same edge count (rank). -/
theorem cutOpenPathIso_iff_rank {w w' : List Nat} {a b a' b' : Nat}
    (hab : a ≤ b) (hab' : a' ≤ b') :
    CutOpenPathIso (cutOpenPath w a b) (cutOpenPath w' a' b') ↔
      b - a = b' - a' := by
  unfold CutOpenPathIso cutOpenPath
  simp only [List.length_range]
  omega

/-- Forward direction: equal return ranks give isomorphic cut-open paths. -/
theorem cutOpenPathIso_of_rank_eq {w w' : List Nat} {a b a' b' : Nat}
    (hab : a ≤ b) (hab' : a' ≤ b') (h : b - a = b' - a') :
    CutOpenPathIso (cutOpenPath w a b) (cutOpenPath w' a' b') :=
  (cutOpenPathIso_iff_rank hab hab').mpr h

/-- Reverse direction: isomorphic cut-open paths have equal return ranks. -/
theorem rank_eq_of_cutOpenPathIso {w w' : List Nat} {a b a' b' : Nat}
    (hab : a ≤ b) (hab' : a' ≤ b')
    (h : CutOpenPathIso (cutOpenPath w a b) (cutOpenPath w' a' b')) :
    b - a = b' - a' :=
  (cutOpenPathIso_iff_rank hab hab').mp h

/-- The paper's simple-return sector condition under the cut-open semantics
    (paper L994–997, L1220–1224): the count condition plus pairwise
    *cut-open* nonisomorphism of elementary return supports. Posteriorly the
    second condition is exactly that the return ranks are distinct. This is
    the semantically accurate replacement for `IsSimpleReturnSector`, whose
    raw-pattern `SupportIso` retained the quotient vertex-identification
    data and was therefore too wide (it accepts e.g.
    `w = [0,1,2,3,1,0,4,2]`, whose support edge counts are `5, 3, 5`). -/
def IsSimpleReturnSectorCutOpen (w : List Nat) : Prop :=
  IsSimpleReturn w ∧ ∀ c a b c' a' b',
    IsElementaryReturn w c a b → IsElementaryReturn w c' a' b' →
    c ≠ c' → ¬ CutOpenPathIso (cutOpenPath w a b) (cutOpenPath w a' b')

/-- Cut-open sector bridge, forward direction: distinct return ranks (edge
    counts) plus the count condition give the cut-open sector condition.
    This is the semantically accurate version of
    `sector_of_distinct_support_lengths`. -/
theorem sectorCutOpen_of_distinct_edge_counts {w : List Nat}
    (hs : IsSimpleReturn w)
    (hd : ∀ c a b c' a' b', IsElementaryReturn w c a b →
      IsElementaryReturn w c' a' b' → c ≠ c' → b - a ≠ b' - a') :
    IsSimpleReturnSectorCutOpen w := by
  refine ⟨hs, fun c a b c' a' b' hc hc' hne hso => ?_⟩
  obtain ⟨⟨hab, -, -, -, -⟩, ⟨hab', -, -, -, -⟩⟩ :
    IsElementaryReturn w c a b ∧ IsElementaryReturn w c' a' b' := ⟨hc, hc'⟩
  exact hd c a b c' a' b' hc hc' hne
    (rank_eq_of_cutOpenPathIso (by omega) (by omega) hso)

/-- Cut-open sector bridge, reverse direction: in the cut-open model the
    sector condition implies distinct return ranks. Together with the forward
    bridge this is the exact rank-distinctness equivalence of paper
    L1220–1224. -/
theorem distinct_edge_counts_of_sectorCutOpen {w : List Nat}
    (hsec : IsSimpleReturnSectorCutOpen w)
    {c a b c' a' b' : Nat}
    (hc : IsElementaryReturn w c a b) (hc' : IsElementaryReturn w c' a' b')
    (hne : c ≠ c') :
    b - a ≠ b' - a' := by
  obtain ⟨-, hpair⟩ := hsec
  obtain ⟨⟨hab, -, -, -, -⟩, ⟨hab', -, -, -, -⟩⟩ :
    IsElementaryReturn w c a b ∧ IsElementaryReturn w c' a' b' := ⟨hc, hc'⟩
  intro heq
  exact hpair c a b c' a' b' hc hc' hne
    (cutOpenPathIso_of_rank_eq (by omega) (by omega) heq)

/-- The cut-open sector condition implies the old raw-pattern sector
    condition: distinct edge counts give distinct vertex counts, hence
    nonisomorphic raw supports. The converse is false (the
    `[0,1,2,3,1,0,4,2]` example), so the cut-open sector is the strictly
    narrower, paper-faithful condition; all consequences of the old sector
    remain available from the new one. -/
theorem sectorCutOpen_imp_sector {w : List Nat}
    (hsec : IsSimpleReturnSectorCutOpen w) : IsSimpleReturnSector w := by
  obtain ⟨hs, hpair⟩ := hsec
  refine ⟨hs, fun c a b c' a' b' hc hc' hne hso => ?_⟩
  obtain ⟨⟨hab, hblen, -, -, -⟩, ⟨hab', hblen', -, -, -⟩⟩ :
    IsElementaryReturn w c a b ∧ IsElementaryReturn w c' a' b' := ⟨hc, hc'⟩
  obtain ⟨hlen, -⟩ := hso
  have hl1 := returnSupport_length (a := a) (b := b) (by omega) hblen
  have hl2 := returnSupport_length (a := a') (b := b') (by omega) hblen'
  have hcut : CutOpenPathIso (cutOpenPath w a b) (cutOpenPath w a' b') := by
    unfold CutOpenPathIso cutOpenPath
    simp only [List.length_range]
    omega
  exact hpair c a b c' a' b' hc hc' hne hcut

end PrimeMother
