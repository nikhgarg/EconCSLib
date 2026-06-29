import GCG24UserItemFairness.MainTheorems
import GCG24UserItemFairness.Examples
import GCG24UserItemFairness.Assumptions

/-!
# Paper Interface: User-Item Fairness Tradeoffs

This compact interface exposes the main paper definitions and direct named
result statements for the verified user-item fairness development.  The full
LP, symmetry, and misestimation proof layers remain in the sibling Lean files.
-/

namespace GCG24UserItemFairness
namespace PaperInterface

open scoped BigOperators

noncomputable section

/-! ## Paper Definitions -/

/-- Recommendation utility matrix `w_{ij}` for users and items. -/
def recommendationUtility {m n : ℕ} (W : RecommendationModel m n)
    (u : User m) (j : Item n) : ℝ :=
  W.utility u j

/-- Raw user utility `sum_j w_ij rho_ij`. -/
def rawUserUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  EconCSLib.Policy.agentScore ρ W.utility u

/-- Normalized user utility `U_i(rho)`. -/
def normalizedUserUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  rawUserUtility W ρ u / RecommendationModel.bestItemUtility W u

/--
Source status: direct source text
User fairness objective for a recommendation policy.
-/
def userFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  EconCSLib.finiteMin (normalizedUserUtility W ρ)

/-- Raw item utility `sum_i w_ij rho_ij`. -/
def rawItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j * (ρ u j).toReal

/-- Item normalizer `sum_i w_ij`. -/
def itemNormalizer {m n : ℕ}
    (W : RecommendationModel m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j

/-- Normalized item utility `I_j(rho)`. -/
def normalizedItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  let denom := itemNormalizer W j
  if denom = 0 then 0 else rawItemUtility W ρ j / denom

/--
Source status: direct source text
Item fairness objective for a recommendation policy.
-/
def itemFairness {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  EconCSLib.finiteMin (normalizedItemUtility W ρ)

/-- Problem 1: a policy maximizes user fairness subject to item-fairness level `gamma`. -/
def solvesProblemOne {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  RecommendationModel.IsOptimalAtLevel W γ ρ

/-- Price of fairness at item-fairness level `gamma`. -/
def priceOfFairnessAt {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  let base := RecommendationModel.optimalUserFairnessAtLevel W 0
  if base = 0 then 0 else
    (base - RecommendationModel.optimalUserFairnessAtLevel W γ) / base

/-- Price of maximal item fairness. -/
def priceOfFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  priceOfFairnessAt W 1

/-- Price of misestimation for a policy selected on an estimated utility matrix. -/
def priceOfMisestimation {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n) : ℝ :=
  let base := RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ
  if base = 0 then 0 else
    (base - RecommendationModel.userFairness E.trueModel ρhat) / base

/-! ## Named Results -/

/-! ### Example 1 -/

/--
Example 1, diverse-preferences toy instance: recommending each user her
favorite item gives maximal normalized user fairness.
-/
theorem example1_diverse_favorite_policy_user_fairness :
    RecommendationModel.userFairness twoByTwoModel diagonalPolicy = 1 := by
  exact paper_example1_diagonal_userFairness_eq_one

/--
Example 1, diverse-preferences toy instance: the same favorite-item policy
equalizes item utility at the displayed `10 / 11` normalized value.
-/
theorem example1_diverse_favorite_policy_item_fairness :
    RecommendationModel.itemFairness twoByTwoModel diagonalPolicy = (10 : ℝ) / 11 := by
  exact paper_example1_diagonal_itemFairness_eq

/--
Example 1, homogeneous-preferences algebra: the displayed bounds imply the
linear normalized user/item fairness tradeoff `Umin + Imin <= 1 + epsilon`.
-/
theorem example1_homogeneous_tradeoff_bound
    {epsilon rho1 rho2 Umin Imin : ℝ}
    (hrho : rho2 = 1 - rho1)
    (hitem : Imin ≤ rho2)
    (huser : Umin ≤ rho1 + epsilon) :
    Umin + Imin ≤ 1 + epsilon := by
  exact paper_example1_homogeneous_tradeoff_bound hrho hitem huser

/-! ### Appendix lemma review rows -/

/-- Appendix C, Lemma 1: the optimal item-fairness value is positive. -/
abbrev appendix_c_lemma1_item_fairness_positive :=
  @RecommendationModel.paper_lemma1_optimal_item_fairness_positive

/-- Appendix C, Lemma 2: item-fairness LP value characterization. -/
abbrev appendix_c_lemma2_item_fairness_lp_value :=
  @RecommendationModel.paper_lemma2_item_fairness_lp_value_eq

/-- Appendix D, Lemma 3: unconstrained user-fairness baseline. -/
abbrev appendix_d_lemma3_unconstrained_baseline :=
  @RecommendationModel.paper_lemma3_unconstrained_user_fairness_eq_one

/-- Appendix D, Lemma 4: Problem 6 sparse-support structure. -/
abbrev appendix_d_lemma4_problem6_structure :=
  @OpposingTypes.paper_lemma4_problem6_active_pairs_le_n_add_one_of_equalizedBasicOptimal

/-- Appendix D, Lemma 5: Problem 6 closed-form value. -/
abbrev appendix_d_lemma5_problem6_closed_form :=
  @OpposingTypes.paper_lemma5_problem6_closed_value

/-- Appendix D, Lemma 6: mirror inverse-gap algebra. -/
abbrev appendix_d_lemma6_mirror_inverse_gap :=
  @OpposingTypes.paper_lemma6_pairShare_mirror_inverse_gap_eq

/-- Appendix D, Lemma 7: pivot monotonicity. -/
abbrev appendix_d_lemma7_pivot_monotonicity :=
  @OpposingTypes.paper_lemma7_problem6FirstClosedPivot_mono_alpha

/-- Appendix D, Lemma 8: selected-pivot interval stitching. -/
abbrev appendix_d_lemma8_selected_pivot_stitching :=
  @OpposingTypes.paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_alpha_le

/-- Appendix D, Lemma 9: the `q_j`/pair-share algebra. -/
abbrev appendix_d_lemma9_pair_share_algebra :=
  @OpposingTypes.paper_lemma9_pairShare_strictly_increases_in_alpha

/-- Appendix D, Lemma 10: midpoint candidate construction. -/
abbrev appendix_d_lemma10_midpoint_candidate :=
  @OpposingTypes.paper_lemma10_pairShare_half_add_reverse_eq_one

/-- Appendix D, Lemma 11: fixed-pivot denominator monotonicity. -/
abbrev appendix_d_lemma11_denominator_monotonicity :=
  @OpposingTypes.paper_lemma11_fixedPivotDenominator_antitone

/-- Appendix E, Lemma 12: symmetrized estimated policy optimality. -/
abbrev appendix_e_lemma12_symmetrized_policy :=
  @OpposingTypes.paper_lemma12_theorem4_symmetrizedPolicy_isOptimalAtLevel

/-- Appendix E, Lemma 13: Problem 11 pivot-support shape. -/
abbrev appendix_e_lemma13_pivot_support :=
  @OpposingTypes.paper_lemma13_problem11_pivotSupport_no_extremes_of_first_lt

/-- Appendix E, Lemma 14: Problem 11 uniqueness/equality-form policy shape. -/
abbrev appendix_e_lemma14_uniqueness :=
  @OpposingTypes.paper_lemma14_problem11_equalizedBasicOptimal_policy_eq

/-- Appendix E, Lemma 15: Problem 11 closed-form lambda formula. -/
abbrev appendix_e_lemma15_closed_formula :=
  @OpposingTypes.paper_lemma15_problem11_lambda_eq_of_pivot_lt_mirror

/-- Appendix E, Lemma 16: midpoint order algebra for pair shares. -/
abbrev appendix_e_lemma16_midpoint_order_algebra :=
  @OpposingTypes.paper_lemma16_val_lt_reverseItem_iff

/-- Appendix E, Lemma 17: no right-half known-type support in Problem 11. -/
abbrev appendix_e_lemma17_no_right_half_support :=
  @OpposingTypes.paper_lemma17_problem11_typeZero_zero_after_mirror_of_equalizedBasicOptimal

/--
Proposition 1: symmetric LP reduction.  Type-symmetric original optima are
represented by reduced type-level policies.
-/
theorem proposition1_symmetric_lp_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) :
    LPReductionTarget R γ := by
  exact ReductionWitness.paper_proposition1_symmetric_lp_reduction_target
    R reps γ

/--
Proposition 2: under positive utilities, a type-symmetric optimal policy exists
for the maximal item-fairness problem.
-/
theorem proposition2_symmetric_optimum_exists
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hPos : assumption_positive_recommendation_utilities S.model) :
    ∃ ρsym : Policy m n,
      UserTypeAssignment.IsTypeSymmetric S.types ρsym ∧
        RecommendationModel.IsOptimalAtLevel S.model 1 ρsym := by
  exact RecommendationModel.SymmetricData.paper_proposition2_symmetric_optimum_exists_of_positive
    S reps hPos

/--
Theorem 3, first half: in the opposing two-type model, increasing `alpha`
toward `1 / 2` weakly decreases the price of fairness.
-/
theorem theorem3_price_decreases_first_half
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (hred : R.reduced = OpposingTypes.twoTypeReducedModel alpha v)
    (hred' : R'.reduced = OpposingTypes.twoTypeReducedModel alpha' v)
    (hn : assumption_theorem4_at_least_three_items n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hPos : assumption_positive_recommendation_utilities R.data.model)
    (hPos' : assumption_positive_recommendation_utilities R'.data.model) :
    RecommendationModel.priceOfFairness R'.data.model ≤
      RecommendationModel.priceOfFairness R.data.model := by
  have hNonneg : R.data.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive R.data.model hPos
  have hRow : R.data.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive R.data.model hPos
  have hNonneg' : R'.data.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive R'.data.model hPos'
  have hRow' : R'.data.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive R'.data.model hPos'
  exact OpposingTypes.paper_theorem3_price_decreases_firstHalf_of_reduction
    R R' reps reps' hred hred' hn halpha0 halpha1 halpha0' halpha1'
    halpha_le halpha_half halpha_half' hpos hdec hNonneg hRow hNonneg' hRow'

/--
Theorem 3, second half: in the opposing two-type model, increasing `alpha`
away from `1 / 2` weakly increases the price of fairness.
-/
theorem theorem3_price_increases_second_half
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (hred : R.reduced = OpposingTypes.twoTypeReducedModel alpha v)
    (hred' : R'.reduced = OpposingTypes.twoTypeReducedModel alpha' v)
    (hn : assumption_theorem4_at_least_three_items n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : 1 / 2 ≤ alpha)
    (halpha_half' : 1 / 2 ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hPos : assumption_positive_recommendation_utilities R.data.model)
    (hPos' : assumption_positive_recommendation_utilities R'.data.model) :
    RecommendationModel.priceOfFairness R.data.model ≤
      RecommendationModel.priceOfFairness R'.data.model := by
  have hNonneg : R.data.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive R.data.model hPos
  have hRow : R.data.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive R.data.model hPos
  have hNonneg' : R'.data.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive R'.data.model hPos'
  have hRow' : R'.data.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive R'.data.model hPos'
  exact OpposingTypes.paper_theorem3_price_increases_secondHalf_of_reduction
    R R' reps reps' hred hred' hn halpha0 halpha1 halpha0' halpha1'
    halpha_le halpha_half halpha_half' hpos hdec hNonneg hRow hNonneg' hRow'

/--
Theorem 4 final tradeoff, cold-start user whose true row is the first opposing
type: without fairness the misestimation price is at most `1/2`, while with
maximal item fairness some estimated optimum has misestimation price above
`1 - eps`.
-/
theorem theorem4_misestimation_tradeoff_typeZero
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsTrue : UserTypeAssignment.TypeRepresentatives Rtrue.data.types)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ}
    (u : User m)
    (hn : assumption_theorem4_at_least_three_items n)
    (htrue : assumption_theorem4_true_model_reduction E Rtrue)
    (hestimated : assumption_theorem4_estimated_model_reduction E Rest)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0 (Rest.liftedPolicy ρ0) ≤ (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ1) := by
  exact EstimatedRecommendationModel.paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeZero
    E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
    hknown0 hknown1 htrueType hestimatedType heps hbeta hbeta_half

/-- Theorem 4 final tradeoff for the second opposing true type. -/
theorem theorem4_misestimation_tradeoff_typeOne
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsTrue : UserTypeAssignment.TypeRepresentatives Rtrue.data.types)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ}
    (u : User m)
    (hn : assumption_theorem4_at_least_three_items n)
    (htrue : assumption_theorem4_true_model_reduction E Rtrue)
    (hestimated : assumption_theorem4_estimated_model_reduction E Rest)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0 (Rest.liftedPolicy ρ0) ≤ (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ1) := by
  exact EstimatedRecommendationModel.paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeOne
    E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
    hknown0 hknown1 htrueType hestimatedType heps hbeta hbeta_half

end

end PaperInterface
end GCG24UserItemFairness
