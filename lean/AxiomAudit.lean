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
