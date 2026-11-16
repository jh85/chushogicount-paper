import ChuShogi

/-! Release audit: statements and foundational dependencies, without importing
certification/PrimaryCounts.lean. This file introduces no correctness axioms. -/
set_option pp.fullNames true

#check ChuShogi.Specification.Candidate
#check ChuShogi.Specification.C_r
#check ChuShogi.Specification.C_nr
#check ChuShogi.Specification.promotion_origins_iff
#check ChuShogi.StructuralDecomposition.decompositionIso
#check ChuShogi.SummarySufficiency.stratumIso
#check ChuShogi.OrderedFile.exact_enumeration
#check ChuShogi.OrderedFile.ordinary_length
#check ChuShogi.OrderedFile.goBetween_length
#check ChuShogi.OrderedFile.lance_length
#check ChuShogi.PlainFileGame.reach_iff
#check ChuShogi.GoBetweenCertificate.reach_iff
#check ChuShogi.LanceProvider.concrete_enumeration
#check ChuShogi.LanceProvider.concrete_singleton
#check ChuShogi.IntegerCompletion.division_exact
#check ChuShogi.CachedArithmetic.count
#check ChuShogi.CachedArithmetic.count_C_r
#check ChuShogi.CachedArithmetic.count_C_nr
#check ChuShogi.AllCandidateCodec.count
#check ChuShogi.AllCandidateCodec.count_correct
#check ChuShogi.EfficientBoardCodec.counterEquivalence
#check ChuShogi.EfficientBoardCodec.prepared_rank_unrank
#check ChuShogi.EfficientBoardCodec.prepared_unrank_rank
#check ChuShogi.EfficientBoardCodec.uniform_input
#check ChuShogi.AllCandidateCodec.equivalence
#check ChuShogi.AllCandidateCodec.rank_unrank
#check ChuShogi.AllCandidateCodec.unrank_rank
#check ChuShogi.AllCandidateCodec.uniform_input

#print axioms ChuShogi.Specification.promotion_origins_iff
#print axioms ChuShogi.StructuralDecomposition.decompositionIso
#print axioms ChuShogi.SummarySufficiency.stratumIso
#print axioms ChuShogi.OrderedFile.exact_enumeration
#print axioms ChuShogi.OrderedFile.ordinary_length
#print axioms ChuShogi.OrderedFile.goBetween_length
#print axioms ChuShogi.OrderedFile.lance_length
#print axioms ChuShogi.PlainFileGame.reach_iff
#print axioms ChuShogi.GoBetweenCertificate.reach_iff
#print axioms ChuShogi.LanceProvider.concrete_enumeration
#print axioms ChuShogi.LanceProvider.concrete_singleton
#print axioms ChuShogi.IntegerCompletion.division_exact
#print axioms ChuShogi.CachedArithmetic.count_C_r
#print axioms ChuShogi.CachedArithmetic.count_C_nr
#print axioms ChuShogi.AllCandidateCodec.count_correct
#print axioms ChuShogi.EfficientBoardCodec.counterEquivalence
#print axioms ChuShogi.EfficientBoardCodec.prepared_rank_unrank
#print axioms ChuShogi.EfficientBoardCodec.prepared_unrank_rank
#print axioms ChuShogi.EfficientBoardCodec.uniform_input
#print axioms ChuShogi.AllCandidateCodec.equivalence
#print axioms ChuShogi.AllCandidateCodec.rank_unrank
#print axioms ChuShogi.AllCandidateCodec.unrank_rank
#print axioms ChuShogi.AllCandidateCodec.uniform_input
