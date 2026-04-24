import UserItemFairness.OpposingTypes

/-!
# Paper-Facing Theorems: User-Item Fairness Tradeoffs in Recommendations

This file is the public theorem interface for the user-item fairness
formalization. Detailed LP, symmetry, and utility-preservation lemmas live in
the sibling files.
-/

namespace UserItemFairness
namespace ReductionWitness

/--
Symmetric item-fairness reduction theorem.

The item-fairness values attainable by type-symmetric user-level policies are
exactly the values attainable by the reduced type-level problem.
-/
theorem paper_symmetric_item_fairness_value_set_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricAttainableItemFairnessSet R.data =
      TypeWeightedRecommendationModel.attainableItemFairnessSet R.reduced := by
  exact R.symmetricAttainableItemFairnessSet_eq_reduced reps

/--
Symmetric optimal item-fairness reduction theorem.

The optimum item-fairness value over type-symmetric user-level policies equals
the optimum item-fairness value in the reduced type-level problem.
-/
theorem paper_symmetric_optimal_item_fairness_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricOptimalItemFairness R.data =
      TypeWeightedRecommendationModel.optimalItemFairness R.reduced := by
  exact R.symmetricOptimalItemFairness_eq_reduced reps

/--
Proposition 1 symmetric LP-reduction target.

Every type-symmetric original optimal policy is represented by a reduced
type-level policy. This is the unconditional part of the paper's symmetry
reduction that follows from chosen representatives for each user type.
-/
theorem paper_symmetric_lp_reduction_target
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) :
    LPReductionTarget R γ := by
  exact lpReductionTarget_of_representatives R reps γ

/--
Pointwise form of the symmetric LP-reduction target.

If a user-level optimum is already type-symmetric, then it is exactly the lift
of some type-level policy.
-/
theorem paper_symmetric_original_optimum_has_type_representative
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n, R.liftedPolicy ρK = ρ := by
  exact lpReductionTarget_of_representatives R reps γ ρ ⟨hρ, hopt⟩

/--
Original/reduced optimal user-fairness value reduction.

This replaces the earlier opaque optimal-value equality assumption with the
standard side conditions needed to reason about `sSup` on real-valued feasible
sets: both feasible value sets are nonempty and bounded above.
-/
theorem paper_original_reduced_user_optimal_value_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ)) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
    reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd

/--
Original/reduced optimal user-fairness value reduction with automatic
boundedness.

The remaining side condition is now only nonemptiness of the original and
reduced feasible value sets; row positivity gives the common `≤ 1` upper bound.
-/
theorem paper_original_reduced_user_optimal_value_reduction_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    reps hRow γ hOrigNonempty hRedNonempty

/--
Original/reduced optimal user-fairness value reduction for strict item-fairness
fractions.

Under the paper's positive-utility assumption, the original and reduced
feasible value sets are automatically nonempty for every `γ < 1`; exact
item-fairness optimum attainment is only needed at the maximal boundary
`γ = 1`.
-/
theorem paper_original_reduced_user_optimal_value_reduction_of_gamma_lt_one
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (γ : ℝ) (hγ : γ < 1) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_gamma_lt_one
    reps hPos γ hγ

/--
Baseline original/reduced optimal user-fairness value reduction.

For `γ = 0`, nonnegative utilities automatically make both original and
reduced feasible value sets nonempty; row positivity supplies boundedness.
-/
theorem paper_original_reduced_user_optimal_value_reduction_zero
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg : R.data.model.Nonnegative) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model 0 =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced 0 := by
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model 0).Nonempty :=
    RecommendationModel.attainableUserFairnessAtLevel_zero_nonempty_of_nonnegative
      R.data.model hNonneg
  have hRedWeight : R.reduced.NonnegativeWeights :=
    R.reduced_nonnegativeWeights
  have hRedUtil : R.reduced.NonnegativeUtilities :=
    R.reduced_nonnegativeUtilities_of_nonnegative reps hNonneg
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 0).Nonempty :=
    TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_zero_nonempty_of_nonnegative
      R.reduced hRedWeight hRedUtil
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    reps hRow 0 hOrigNonempty hRedNonempty

/--
Reduced-to-original optimum theorem under the explicit supremum conditions used
by the value-reduction theorem.
-/
theorem paper_reduced_optimum_lifts_to_original
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ))
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
      reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Reduced-to-original optimum theorem with automatic boundedness.

Only nonemptiness of the original and reduced feasible value sets remains
explicit; row positivity supplies the `≤ 1` bounds needed by `sSup`.
-/
theorem paper_reduced_optimum_lifts_to_original_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow γ hOrigNonempty hRedNonempty
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Reduced-to-original optimum theorem with feasible-set nonemptiness discharged
from the supplied reduced optimum.

This version applies at the maximal item-fairness boundary `γ = 1` as soon as
a reduced optimum is available.
-/
theorem paper_reduced_optimum_lifts_to_original_auto_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced_auto_nonempty
    reps hRow γ ρ hopt

/--
Reduced-to-original optimum theorem for strict item-fairness fractions.

For `γ < 1`, positive utilities discharge the feasible-value nonemptiness
conditions used by the value-reduction theorem.
-/
theorem paper_reduced_optimum_lifts_to_original_of_gamma_lt_one
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (γ : ℝ) (hγ : γ < 1) (ρ : TypePolicy K n)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_gamma_lt_one
      reps hPos γ hγ
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Symmetric original-to-reduced optimum theorem under the explicit supremum
conditions used by the value-reduction theorem.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ))
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
      reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Symmetric original-to-reduced optimum theorem with automatic boundedness.

Only nonemptiness of the original and reduced feasible value sets remains
explicit; row positivity supplies the `≤ 1` bounds needed by `sSup`.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow γ hOrigNonempty hRedNonempty
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Symmetric original-to-reduced optimum theorem with feasible-set nonemptiness
discharged from the supplied original optimum.

This version applies at the maximal item-fairness boundary `γ = 1` as soon as a
type-symmetric original optimum is available.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced_auto_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal_auto_nonempty
    reps hRow γ hρ hopt

/--
Symmetric original-to-reduced optimum theorem for strict item-fairness
fractions.

For `γ < 1`, positive utilities discharge the feasible-value nonemptiness
conditions used by the value-reduction theorem.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced_of_gamma_lt_one
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (γ : ℝ) (hγ : γ < 1) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_gamma_lt_one
      reps hPos γ hγ
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

end ReductionWitness

namespace RecommendationModel

/--
Appendix C, Lemma 1: under the paper's strictly positive utility assumption,
the optimal minimum item fairness value is strictly positive.
-/
theorem paper_lemma1_optimal_item_fairness_positive
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive) :
    0 < W.optimalItemFairness := by
  exact W.optimalItemFairness_pos_of_columnHasPositiveDemand
    (W.nonnegative_of_positive hPos)
    (W.columnHasPositiveDemand_of_positive hPos)

/--
Appendix C, Lemma 2 in max-min LP epigraph form.

The LP that maximizes `ell` subject to `ell ≤ I_j(ρ,w)` for every item has the
same optimal value as the paper's item-fairness objective `I^*_min(w)`.
-/
theorem paper_lemma2_item_fairness_lp_value_eq
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    W.optimalItemFairnessLPValue = W.optimalItemFairness := by
  exact W.optimalItemFairnessLPValue_eq_optimalItemFairness_of_nonnegative
    hNonneg

/--
Problem 1 baseline theorem.

With nonnegative utilities and a positive row normalizer for every user, the
unconstrained user-fairness optimum `U^*_min(w)` equals `1`. The witness is the
deterministic policy that recommends a best item to each user.
-/
theorem paper_unconstrained_user_fairness_optimum_eq_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) :
    W.optimalUserFairnessAtLevel 0 = 1 := by
  exact W.optimalUserFairnessAtLevel_zero_eq_one hNonneg hRow

/--
Price-of-fairness identity at an arbitrary item-fairness fraction.

Once the unconstrained optimum is normalized to `1`, the paper's price of
fairness is exactly `1 - U^*_min(γ,w)`.
-/
theorem paper_priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) (γ : ℝ) :
    W.priceOfFairnessAt γ = 1 - W.optimalUserFairnessAtLevel γ := by
  exact W.priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel
    hNonneg hRow γ

/--
Price-of-fairness identity for the maximal item-fairness problem.
-/
theorem paper_priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) :
    W.priceOfFairness = 1 - W.optimalUserFairnessAtLevel 1 := by
  exact W.priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one
    hNonneg hRow

/--
Theorem 3 algebraic monotonicity bridge.

If the maximal-item-fairness constrained optimum increases between two utility
matrices, then the price of fairness decreases. The paper-specific work in
Theorem 3 is therefore the finite LP proof that
`U^*_min(1, α)` increases with preference diversity.
-/
theorem paper_theorem3_price_decreases_from_constrained_optimum_increase
    {m n : ℕ} [NeZero m] [NeZero n]
    (W W' : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem)
    (hNonneg' : W'.Nonnegative) (hRow' : W'.RowHasPositiveItem)
    (hopt :
      W.optimalUserFairnessAtLevel 1 ≤ W'.optimalUserFairnessAtLevel 1) :
    W'.priceOfFairness ≤ W.priceOfFairness := by
  exact W.priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    W' hNonneg hRow hNonneg' hRow' hopt

/--
Strict form of the Theorem 3 algebraic monotonicity bridge.
-/
theorem paper_theorem3_price_strictly_decreases_from_constrained_optimum_increase
    {m n : ℕ} [NeZero m] [NeZero n]
    (W W' : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem)
    (hNonneg' : W'.Nonnegative) (hRow' : W'.RowHasPositiveItem)
    (hopt :
      W.optimalUserFairnessAtLevel 1 < W'.optimalUserFairnessAtLevel 1) :
    W'.priceOfFairness < W.priceOfFairness := by
  exact W.priceOfFairness_lt_of_optimalUserFairnessAtLevel_one_lt
    W' hNonneg hRow hNonneg' hRow' hopt

end RecommendationModel

namespace RecommendationModel.SymmetricData

/--
Proposition 2, part 1: `S_symm` satisfies the paper's symmetric-optimum
existence condition.

Given any optimum for the maximal item-fairness problem, averaging the policy
inside each equal-utility user type produces an optimum in `S_symm`.
-/
theorem paper_proposition2_symmetric_optimum_exists
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hRow : S.model.RowHasPositiveItem)
    {ρ : Policy m n}
    (hopt : RecommendationModel.IsOptimalAtLevel S.model 1 ρ) :
    ∃ ρsym : Policy m n,
      UserTypeAssignment.IsTypeSymmetric S.types ρsym ∧
        RecommendationModel.IsOptimalAtLevel S.model 1 ρsym := by
  exact S.exists_typeSymmetric_isOptimalAtLevel_of_isOptimalAtLevel
    reps hRow hopt

end RecommendationModel.SymmetricData

namespace OpposingTypes

/--
Appendix D, Lemma 9, scalar monotonicity in `α`.

For a fixed opposing item pair with positive utilities, the paper's
`q_j(α)` strictly increases as the mass `α` on the first type increases.
-/
theorem paper_lemma9_typeOneShare_strictly_increases_in_alpha
    {alpha alpha' left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare alpha left right <
      typeOneShare alpha' left right := by
  exact typeOneShare_strictMono_alpha
    halpha0 halpha1 halpha0' halpha1' hlt hleft hright

/--
Appendix E, Lemma 16, scalar midpoint comparison: if the left-side utility is
larger, then the midpoint share is above `1/2`.
-/
theorem paper_lemma16_half_lt_typeOneShare_half_of_right_lt_left
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : right < left) :
    (1 / 2 : ℝ) < typeOneShare (1 / 2) left right := by
  exact half_lt_typeOneShare_half_of_right_lt_left hleft hright hlt

/--
Appendix E, Lemma 16, scalar midpoint comparison: if the left-side utility is
smaller, then the midpoint share is below `1/2`.
-/
theorem paper_lemma16_typeOneShare_half_lt_half_of_left_lt_right
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : left < right) :
    typeOneShare (1 / 2) left right < (1 / 2 : ℝ) := by
  exact typeOneShare_half_lt_half_of_left_lt_right hleft hright hlt

/--
Appendix E, Lemma 16, scalar midpoint comparison: equal opposing utilities
give midpoint share exactly `1/2`.
-/
theorem paper_lemma16_typeOneShare_half_eq_half_of_eq
    {left right : ℝ}
    (hleft : 0 < left) (heq : left = right) :
    typeOneShare (1 / 2) left right = (1 / 2 : ℝ) := by
  exact typeOneShare_half_eq_half_of_eq hleft heq

/--
Appendix D, Lemma 9, indexed form: for each item `j`, the paper's
`q_j(α)` strictly increases as `α` increases.
-/
theorem paper_lemma9_pairShare_strictly_increases_in_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j < pairShare alpha' v j := by
  exact pairShare_strictMono_alpha j
    halpha0 halpha1 halpha0' halpha1' hlt hpos

/--
Appendix E, Lemma 16, indexed form: `q_j(1/2) > 1/2` when item `j` has
higher value than its opposite item.
-/
theorem paper_lemma16_half_lt_pairShare_half_of_reverse_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v (reverseItem j) < v j) :
    (1 / 2 : ℝ) < pairShare (1 / 2) v j := by
  exact half_lt_pairShare_half_of_reverse_lt j hpos hlt

/--
Appendix E, Lemma 16, indexed form: `q_j(1/2) < 1/2` when item `j` has
lower value than its opposite item.
-/
theorem paper_lemma16_pairShare_half_lt_half_of_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v j < v (reverseItem j)) :
    pairShare (1 / 2) v j < (1 / 2 : ℝ) := by
  exact pairShare_half_lt_half_of_lt_reverse j hpos hlt

/--
Appendix E, Lemma 16, indexed form: `q_j(1/2) = 1/2` when item `j` and its
opposite have equal value.
-/
theorem paper_lemma16_pairShare_half_eq_half_of_eq_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (heq : v j = v (reverseItem j)) :
    pairShare (1 / 2) v j = (1 / 2 : ℝ) := by
  exact pairShare_half_eq_half_of_eq_reverse j hpos heq

end OpposingTypes

namespace EstimatedRecommendationModel

/--
Exact-estimation benchmark for the price of misestimation.

If the estimated utilities coincide with the true utilities, then any policy
that solves the estimated problem has zero price of misestimation when evaluated
against the true model.
-/
theorem paper_priceOfMisestimation_exact_estimation_eq_zero
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hutility : E.estimatedUtility = E.trueModel.utility)
    (hopt : E.SolvesEstimatedProblem γ ρhat) :
    E.priceOfMisestimation γ ρhat = 0 := by
  exact E.priceOfMisestimation_eq_zero_of_estimatedUtility_eq_true
    γ ρhat hutility hopt

/--
Appendix E, Theorem 4 final algebraic step.

If the true maximal-fairness optimum is above `1/n` while the estimated
maximal-fairness solution gives true user fairness below `eps/n`, then the
price of misestimation with maximal item-fairness constraints is above
`1 - eps`.
-/
theorem paper_theorem4_misestimation_large_from_bounds
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (eps : ℝ) (ρhat : Policy m n)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (huser :
      RecommendationModel.userFairness E.trueModel ρhat <
        eps / (n : ℝ)) :
    1 - eps < E.priceOfMisestimation 1 ρhat := by
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    eps ρhat heps hbase huser

end EstimatedRecommendationModel

namespace TypePolicy

/--
Proposition 1 sparse shared-item consequence.

If a reduced type-level policy has at most `n + K - 1` active type-item pairs
and every item is recommended by at least one type, then at most `K - 1` items
are shared by multiple user types. This is the finite counting half of the
paper's sparse-support statement, separated from the LP basic-feasible-solution
theorem that supplies the active-pair bound.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound
    {K n : ℕ} [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SharedItemsBound ρ := by
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive hcover

/--
Proposition 1 sparse-shape consequence from active-pair sparsity and item
coverage.
-/
theorem paper_sparse_shape_of_active_pairs_bound
    {K n : ℕ} [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SparseShape ρ := by
  exact sparseShape_of_activePairsBound_of_item_coverage ρ hactive hcover

/--
Proposition 1 sparse shared-item consequence with item coverage discharged from
positive reduced item fairness.

If the reduced type policy has positive minimum normalized item utility, then
every item is recommended by at least one type. Therefore the paper's
basic-feasible-solution active-pair bound implies that at most `K - 1` items
are shared by multiple user types.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound_of_positive_item_fairness
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ) :
    SharedItemsBound ρ := by
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Proposition 1 sparse-shape consequence with item coverage discharged from
positive reduced item fairness.
-/
theorem paper_sparse_shape_of_active_pairs_bound_of_positive_item_fairness
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ) :
    SparseShape ρ := by
  exact sparseShape_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Lemma `IF* > 0` from the paper, in the reduced type-level model.

Strictly positive type weights and utility entries imply that the maximal
reduced item-fairness value is strictly positive; the proof is witnessed by the
uniform policy.
-/
theorem paper_reduced_optimal_item_fairness_positive
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities) :
    0 < TypeWeightedRecommendationModel.optimalItemFairness T := by
  exact TypeWeightedRecommendationModel.optimalItemFairness_pos_of_positive
    T hWeight hUtil

/--
Proposition 1 active-support bound from the LP basic-feasible-solution support
count.

This is the finite arithmetic part of the paper's BFS sparsity proof:
`nK + 1` variables, `n + K` equality constraints, and therefore at least
`nK + 1 - (n + K)` binding nonnegativity constraints imply at most
`n + K - 1` positive type-item pairs.
-/
theorem paper_active_pairs_bound_of_basic_feasible_support
    {K n : ℕ} [NeZero K] [NeZero n]
    (ρ : TypePolicy K n)
    (hcert : BasicFeasibleSupportCertificate ρ) :
    ActivePairsBound ρ := by
  exact activePairsBound_of_basicFeasibleSupportCertificate ρ hcert

/--
Proposition 1 sparse shared-item consequence for a maximal-item-fairness
reduced optimum.

The only remaining hypothesis is the paper's basic-feasible-solution
active-pair bound. Positivity of the item-fairness optimum is discharged from
strictly positive weights/utilities.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hactive : ActivePairsBound ρ)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel T 1 ρ) :
    SharedItemsBound ρ := by
  have hopt_pos :
      0 < TypeWeightedRecommendationModel.optimalItemFairness T :=
    TypeWeightedRecommendationModel.optimalItemFairness_pos_of_positive
      T hWeight hUtil
  have hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ := by
    have hfeas := hopt.1
    unfold TypeWeightedRecommendationModel.feasibleAtLevel at hfeas
    exact lt_of_lt_of_le hopt_pos (by simpa using hfeas)
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Proposition 1 sparse-shape consequence for a maximal-item-fairness reduced
optimum, with positivity discharged from strictly positive data.
-/
theorem paper_sparse_shape_of_active_pairs_bound_of_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hactive : ActivePairsBound ρ)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel T 1 ρ) :
    SparseShape ρ := by
  exact ⟨hactive,
    paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum
      T ρ hWeight hUtil hactive hopt⟩

/--
Proposition 1 sparse shared-item consequence for a maximal-item-fairness
reduced optimum, using the paper's basic-feasible-solution support count
directly.
-/
theorem paper_sparse_shared_items_of_basic_feasible_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hcert : BasicFeasibleSupportCertificate ρ)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel T 1 ρ) :
    SharedItemsBound ρ := by
  exact paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum
    T ρ hWeight hUtil
    (activePairsBound_of_basicFeasibleSupportCertificate ρ hcert) hopt

/--
Proposition 1 sparse-shape consequence for a maximal-item-fairness reduced
optimum, using the paper's basic-feasible-solution support count directly.
-/
theorem paper_sparse_shape_of_basic_feasible_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hcert : BasicFeasibleSupportCertificate ρ)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel T 1 ρ) :
    SparseShape ρ := by
  exact paper_sparse_shape_of_active_pairs_bound_of_maximal_optimum
    T ρ hWeight hUtil
    (activePairsBound_of_basicFeasibleSupportCertificate ρ hcert) hopt

end TypePolicy

end UserItemFairness
