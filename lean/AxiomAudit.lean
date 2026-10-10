/-
Prime-Distribution Birth Mother — Axiom audit entry point.

Committed audit input: imports all 5 library modules and runs
`#print axioms` on every public theorem. Run with:
  cd lean && lake env lean AxiomAudit.lean
Expected: every line lists only propext / Classical.choice / Quot.sound
(or no axioms), and no line mentions sorryAx.
-/
import Definitions.Def_PrimeMother_Atlas
import Theorems.Thm_PrimeMother_PrimeBirth
import Theorems.Thm_PrimeMother_Regression
import Theorems.Thm_PrimeMother_Distribution
import Definitions.Def_PrimeMother_ReturnWord
import Definitions.Def_PrimeMother_ReturnPacket
import Theorems.Thm_PrimeMother_ReturnCombination
open PrimeMother
-- Source (6)
#print axioms crk_mono
#print axioms crk_strict_mono
#print axioms crk_chainOf
#print axioms crk_injective
#print axioms clock_iso
#print axioms clock_surjective
-- Atlas: ranks (5)
#print axioms rk_root
#print axioms rk_E
#print axioms clock_reconstruction
#print axioms atlas_rank_fwd
#print axioms atlas_rank_bwd
-- Atlas: birth rule (3)
#print axioms birth_E
#print axioms birth_root
#print axioms birth_succ_succ
-- Atlas: P1.2 tilings (5)
#print axioms block_edge_count
#print axioms block_adjacent_meet
#print axioms block_interior_disjoint
#print axioms block_cover
#print axioms tiling_exists_iff
-- Atlas: P1.2 mothers/provenance (7)
#print axioms qualified_is_mother
#print axioms mother_zero_zero
#print axioms not_qualified_zero
#print axioms mother_one_two
#print axioms not_qualified_one
#print axioms provenance_complete
#print axioms provenance_witness
-- PrimeBirth (3)
#print axioms birth_ge_two
#print axioms birth_iff_no_earlier_mother
#print axioms birth_iff_prime
-- Distribution P1.3 (5)
#print axioms chainIso_preserves_crk
#print axioms mem_cone_iff
#print axioms path_sieve_identity
#print axioms birthCount_eq_primeCounting
#print axioms birth_support_eq_primes
-- Return words P2.1a (7)
#print axioms listMax_append_single
#print axioms le_listMax
#print axioms returnWord_nonempty
#print axioms returnWord_head_zero
#print axioms returnWord_new_label_eq
#print axioms returnWord_max_le_length
#print axioms returnWord_label_le_length
-- Return packet P2.1b + sector semantics (6)
#print axioms packet_mem_recurrent
#print axioms simpleReturn_packet_card
#print axioms elementaryReturn_mem_occs
#print axioms returnsOverlap_symm
#print axioms returnSupport_length
#print axioms not_supportIso_of_length_ne
#print axioms sector_of_distinct_support_lengths
-- Return combination P2.1c (17)
#print axioms listMax_spine
#print axioms spine_length
#print axioms getLast?_spine
#print axioms isReturnWord_spine
#print axioms singlePrimeWord_length
#print axioms isReturnWord_singlePrime
#print axioms spine_one_at_one
#print axioms singlePrimeWord_one_at_one
#print axioms singlePrimeWord_one_at_end
#print axioms spine_get
#print axioms singlePrimeWord_elementary
#print axioms last_le_listMax
#print axioms isReturnWord_append_fresh
#print axioms getLast?_append_fresh
#print axioms packetStep_invariant
#print axioms packetWordAux_invariant
#print axioms isReturnWord_packetWord
