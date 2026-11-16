import ChuShogi

/-! Focused audit supplement. Every statement below concerns the existing
specification, group coordinates, or executable codecs. No promotion operation,
Board representation, counting definition, or release source is changed. -/
namespace ChuShogi.PromotionAudit
open Specification Promotion CanonicalGroups GroupConfigurations

/-- All fifteen separate promoted roles differ from every native role. -/
theorem promoted_ne_native (k : Separate) (b : Base) :
    Role.promoted k ≠ Role.native b := by intro h; cases h

/-- The separate promoted tag retains the original piece type. -/
theorem promoted_injective : Function.Injective Role.promoted := by
  intro k l h
  cases h
  rfl

theorem separate_mapping (k : Separate) :
    Specification.promote k.base = some (.promoted k) := by cases k <;> rfl

/-- Exhaustive classification, not just the eight example pairs. -/
theorem separate_output_iff (b : Base) (k : Separate) :
    Specification.promote b = some (.promoted k) ↔ b = k.base := by
  cases b <;> cases k <;> decide

/-- Exactly the agreed three identity merges, and no other native outputs. -/
theorem native_output_iff (b t : Base) :
    Specification.promote b = some (.native t) ↔
      (b = .elephant ∧ t = .king) ∨
      (b = .kirin ∧ t = .lion) ∨ (b = .phoenix ∧ t = .freeKing) := by
  cases b <;> cases t <;> decide

theorem no_output_iff (b : Base) :
    Specification.promote b = none ↔ b = .king ∨ b = .lion ∨ b = .freeKing := by
  cases b <;> decide

/-- Every merged output belongs to a nonpromotable native type. This does not
invent a Role-to-Role promotion API: Specification.promote takes Base. -/
theorem merged_output_terminal (b t : Base)
    (h : Specification.promote b = some (.native t)) :
    Specification.promote t = none := by
  rcases (native_output_iff b t).mp h with h | h | h
  all_goals rcases h with ⟨rfl,rfl⟩; rfl

/-- Promoted roles contribute no royal at an updated square. Other squares
and any royals already there remain arbitrary. -/
theorem royal_count_promoted_update (b : Board) (c : Colour) (q : Square) (k : Separate) :
    number (Function.update b q (some (c,.promoted k))) c (.native .king) =
      number (Function.update b q none) c (.native .king) := by
  unfold number countWhere
  apply congrArg List.length
  apply List.filter_congr
  intro s _
  by_cases h : s = q <;> simp [h]

theorem goBetween_update_nonroyal (b : Board) (c : Colour) (q : Square) :
    hasRoyal (Function.update b q (some (c,.promoted .goBetween))) c ↔
      hasRoyal (Function.update b q none) c := by
  unfold hasRoyal
  rw [royal_count_promoted_update]

/-- I5 queries the go-between pool, not the elephant/royal group. -/
theorem I5_goBetween_pool (b : Board) (h : I5 b) (c : Colour) :
    number b c (.promoted .goBetween) ≤ (nonpawnFiles (unpromoted b) c .goBetween).length :=
  h c .goBetween (by decide)

/-- Every separate type has its own native/promoted inventory inequality. -/
theorem I9_separate_stock (b : Board) (h : I9 b) (c : Colour) (k : Separate) :
    number b c (.native k.base) + number b c (.promoted k) ≤ initialSeparate k :=
  (h c).1 k

/-- In particular promoted gold and native rook use different initial stocks. -/
theorem I9_gold_rook_stocks (b : Board) (h : I9 b) (c : Colour) :
    (number b c (.native .gold) + number b c (.promoted .gold) ≤ 2) ∧
    (number b c (.native .rook) + number b c (.promoted .rook) ≤ 2) ∧
    (number b c (.native .bishop) + number b c (.promoted .bishop) ≤ 2) ∧
    (number b c (.native .dragonHorse) + number b c (.promoted .dragonHorse) ≤ 2) ∧
    (number b c (.native .dragonKing) + number b c (.promoted .dragonKing) ≤ 2) :=
  ⟨(h c).1 .gold,(h c).1 .rook,(h c).1 .bishop,(h c).1 .dragonHorse,(h c).1 .dragonKing⟩

/-- Royal origin assignments exist as witnesses only: one initial king and
one initial elephant, which is either unpromoted or a crown prince. -/
theorem I9_royal_origins (b : Board) (h : I9 b) (c : Colour) :
    ∃ king prince, RoyalOrigin king (number b c (.native .elephant)) prince ∧
      number b c (.native .king) = king + prince :=
  (royal_origins_iff _ _).mp ⟨(h c).2.1,(h c).2.2.1⟩

/-- The same one-native/one-promotable interpretation of the two jumper groups. -/
theorem jumper_origins (small big : Nat) (h : JumperMaterial small big) :
    ∃ native promoted, native ≤ 1 ∧ small + promoted ≤ 1 ∧ big = native + promoted := by
  obtain ⟨native,promoted,ho,he⟩ := (royal_origins_iff big small).mp ⟨h.1,by have := h.2; omega⟩
  exact ⟨native,promoted,ho.1,ho.2,he⟩

/-- Actual group coordinates retain distinct native and promoted stocks. -/
theorem group_separate_coordinates (g : Config r s) (c : Colour) (k : Separate)
    (hk : k ∈ GroupCoverage.ordinary) :
    counts g c (.native k.base) = (g.std c k hk).val.1 ∧
      counts g c (.promoted k) = (g.std c k hk).val.2 := by
  constructor
  · rw [counts_sep]; simp [sep,hk]
  · simp [counts,sep,hk]

theorem group_goBetween_royal_coordinates (g : Config r s) (c : Colour) :
    counts g c (.promoted .goBetween) = g.promoted c .goBetween ∧
    counts g c (.native .elephant) = (g.royal c).val.2 ∧
    counts g c (.native .king) = (g.royal c).val.1 := by
  simp [counts,sep,GroupCoverage.ordinary]

/-- Actual unrestricted alphabet entries preserve every separate promoted role. -/
theorem promoted_unbound (c : Colour) (k : Separate) :
    CanonicalAlphabet.IsUnbound (c,.promoted k) := by
  constructor <;> exact promoted_ne_native k _

/-- Equality is of actual Square -> Option Piece functions, not movement tables. -/
theorem prepared_codec_preserves_square (r : Bool)
    (b : {b : Board // StructuralDecomposition.Stratum r b}) (q : Square) :
    (EfficientBoardCodec.unrank (EfficientBoardCodec.runtime (EfficientBoardCodec.prepare r))
      (EfficientBoardCodec.rank (EfficientBoardCodec.runtime (EfficientBoardCodec.prepare r)) b)).val q = b.val q :=
  congrArg (fun x : {b : Board // StructuralDecomposition.Stratum r b} => x.val q)
    (EfficientBoardCodec.prepared_unrank_rank r b)

/-- Two admissible Boards with the audited status distinction cannot be assigned
one index by the actual prepared executable ranker. -/
theorem prepared_rank_distinguishes (r : Bool)
    (b d : {b : Board // StructuralDecomposition.Stratum r b}) (q : Square)
    (c : Colour) (k : Separate) (t : Base)
    (hb : b.val q = some (c,.promoted k)) (hd : d.val q = some (c,.native t)) :
    EfficientBoardCodec.rank (EfficientBoardCodec.runtime (EfficientBoardCodec.prepare r)) b ≠
      EfficientBoardCodec.rank (EfficientBoardCodec.runtime (EfficientBoardCodec.prepare r)) d := by
  intro h
  have he := congrArg
    (EfficientBoardCodec.unrank (EfficientBoardCodec.runtime (EfficientBoardCodec.prepare r))) h
  rw [EfficientBoardCodec.prepared_unrank_rank r b,
    EfficientBoardCodec.prepared_unrank_rank r d] at he
  have hs := congrArg (fun x : {b : Board // StructuralDecomposition.Stratum r b} => x.val q) he
  rw [hb,hd] at hs
  cases hs

/-- The actual EGF input list keeps both one-native and one-promoted states,
even though their degree and divisor are equal. -/
theorem std_single_survivor_multiplicity :
    FreeEGF.stdInputs.count ⟨⟨1,0,0⟩,1⟩ = 2 := by decide

/-- The two compatible king/prince origins are one canonical count state. -/
theorem royal_single_canonical_state : royalStates.count (1,0) = 1 := by decide

/-- Limited reference-game check: a slot already marked promoted has no move
of its own. This is not a full-game transition theorem. -/
theorem file_promoted_slot_inactive (c : Colour) (k : Kind) :
    FileGame.next [(c,k)] [⟨13,by decide⟩] = [] := by rfl

end ChuShogi.PromotionAudit

set_option pp.fullNames true

/-! Statements and dependencies of the focused lemmas and the existing path. -/
#check ChuShogi.Specification.promote
#print ChuShogi.Specification.promote

#check ChuShogi.PromotionAudit.promoted_ne_native
#print axioms ChuShogi.PromotionAudit.promoted_ne_native

#check ChuShogi.PromotionAudit.promoted_injective
#print axioms ChuShogi.PromotionAudit.promoted_injective

#check ChuShogi.PromotionAudit.separate_mapping
#print axioms ChuShogi.PromotionAudit.separate_mapping

#check ChuShogi.PromotionAudit.separate_output_iff
#print axioms ChuShogi.PromotionAudit.separate_output_iff

#check ChuShogi.PromotionAudit.native_output_iff
#print axioms ChuShogi.PromotionAudit.native_output_iff

#check ChuShogi.PromotionAudit.no_output_iff
#print axioms ChuShogi.PromotionAudit.no_output_iff

#check ChuShogi.PromotionAudit.merged_output_terminal
#print axioms ChuShogi.PromotionAudit.merged_output_terminal

#check ChuShogi.PromotionAudit.royal_count_promoted_update
#print axioms ChuShogi.PromotionAudit.royal_count_promoted_update

#check ChuShogi.PromotionAudit.goBetween_update_nonroyal
#print axioms ChuShogi.PromotionAudit.goBetween_update_nonroyal

#check ChuShogi.PromotionAudit.I5_goBetween_pool
#print axioms ChuShogi.PromotionAudit.I5_goBetween_pool

#check ChuShogi.PromotionAudit.I9_separate_stock
#print axioms ChuShogi.PromotionAudit.I9_separate_stock

#check ChuShogi.PromotionAudit.I9_gold_rook_stocks
#print axioms ChuShogi.PromotionAudit.I9_gold_rook_stocks

#check ChuShogi.PromotionAudit.I9_royal_origins
#print axioms ChuShogi.PromotionAudit.I9_royal_origins

#check ChuShogi.PromotionAudit.jumper_origins
#print axioms ChuShogi.PromotionAudit.jumper_origins

#check ChuShogi.PromotionAudit.group_separate_coordinates
#print axioms ChuShogi.PromotionAudit.group_separate_coordinates

#check ChuShogi.PromotionAudit.group_goBetween_royal_coordinates
#print axioms ChuShogi.PromotionAudit.group_goBetween_royal_coordinates

#check ChuShogi.PromotionAudit.promoted_unbound
#print axioms ChuShogi.PromotionAudit.promoted_unbound

#check ChuShogi.PromotionAudit.prepared_codec_preserves_square
#print axioms ChuShogi.PromotionAudit.prepared_codec_preserves_square

#check ChuShogi.PromotionAudit.prepared_rank_distinguishes
#print axioms ChuShogi.PromotionAudit.prepared_rank_distinguishes

#check ChuShogi.PromotionAudit.std_single_survivor_multiplicity
#print axioms ChuShogi.PromotionAudit.std_single_survivor_multiplicity

#check ChuShogi.PromotionAudit.royal_single_canonical_state
#print axioms ChuShogi.PromotionAudit.royal_single_canonical_state

#check ChuShogi.PromotionAudit.file_promoted_slot_inactive
#print axioms ChuShogi.PromotionAudit.file_promoted_slot_inactive

#check ChuShogi.Specification.promotion_origins_iff
#print axioms ChuShogi.Specification.promotion_origins_iff

#check ChuShogi.Promotion.nonpawn_origin_absent
#print axioms ChuShogi.Promotion.nonpawn_origin_absent

#check ChuShogi.ConfinedMaterial.confined_material
#print axioms ChuShogi.ConfinedMaterial.confined_material

#check ChuShogi.CanonicalGroups.royal_origins_iff
#print axioms ChuShogi.CanonicalGroups.royal_origins_iff

#check ChuShogi.CanonicalGroups.royal_origin_nonunique
#print axioms ChuShogi.CanonicalGroups.royal_origin_nonunique

#check ChuShogi.CanonicalGroups.stdStates_iff
#print axioms ChuShogi.CanonicalGroups.stdStates_iff

#check ChuShogi.GroupCoverage.grouped_iff
#print axioms ChuShogi.GroupCoverage.grouped_iff

#check ChuShogi.GroupConfigurations.valid_compact_unique
#print axioms ChuShogi.GroupConfigurations.valid_compact_unique

#check ChuShogi.GroupConfigurations.counts_ofGrouped
#print axioms ChuShogi.GroupConfigurations.counts_ofGrouped

#check ChuShogi.GroupConfigurations.roundtrip
#print axioms ChuShogi.GroupConfigurations.roundtrip

#check ChuShogi.GroupWeights.divisor_product
#print axioms ChuShogi.GroupWeights.divisor_product

#check ChuShogi.FreeGroupModels.coefficients_model
#print axioms ChuShogi.FreeGroupModels.coefficients_model

#check ChuShogi.FreeCoordinates.coefficients_canonical
#print axioms ChuShogi.FreeCoordinates.coefficients_canonical

#check ChuShogi.CompletionCoefficients.coefficients_canonical
#print axioms ChuShogi.CompletionCoefficients.coefficients_canonical

#check ChuShogi.UnboundInventory.weight_factorials
#print axioms ChuShogi.UnboundInventory.weight_factorials

#check ChuShogi.EvaluatorRefinement.evaluateNat_compact_weight
#print axioms ChuShogi.EvaluatorRefinement.evaluateNat_compact_weight

#check ChuShogi.CanonicalPolynomialFamily.contribution
#print axioms ChuShogi.CanonicalPolynomialFamily.contribution

#check ChuShogi.CanonicalUnrestrictedCodec.unrank_rank
#print axioms ChuShogi.CanonicalUnrestrictedCodec.unrank_rank

#check ChuShogi.ComputedAlphabetRestriction.restrict_extend
#print axioms ChuShogi.ComputedAlphabetRestriction.restrict_extend

#check ChuShogi.CompletionBoardCodec.unrank_rank
#print axioms ChuShogi.CompletionBoardCodec.unrank_rank

#check ChuShogi.EfficientBoardCodec.prepared_unrank_rank
#print axioms ChuShogi.EfficientBoardCodec.prepared_unrank_rank

#check ChuShogi.EfficientBoardCodec.prepared_rank_unrank
#print axioms ChuShogi.EfficientBoardCodec.prepared_rank_unrank

#check ChuShogi.AllCandidateCodec.unrank_rank
#print axioms ChuShogi.AllCandidateCodec.unrank_rank

#check ChuShogi.CachedArithmetic.count_C_r
#print axioms ChuShogi.CachedArithmetic.count_C_r

#check ChuShogi.CachedArithmetic.count_C_nr
#print axioms ChuShogi.CachedArithmetic.count_C_nr

#check ChuShogi.AllCandidateCodec.count_correct
#print axioms ChuShogi.AllCandidateCodec.count_correct

#check ChuShogi.SummaryBridge.I4_I5_summary
#print axioms ChuShogi.SummaryBridge.I4_I5_summary

#check ChuShogi.CompletionProfiles.conditions_iff
#print axioms ChuShogi.CompletionProfiles.conditions_iff

#check ChuShogi.CompletionProfiles.completes_profile
#print axioms ChuShogi.CompletionProfiles.completes_profile

#check ChuShogi.Completion.I9_from_free
#print axioms ChuShogi.Completion.I9_from_free

#check ChuShogi.ComputedDecomposition.equivalence
#print axioms ChuShogi.ComputedDecomposition.equivalence
