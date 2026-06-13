import GCG24UserItemFairness.MainTheorems
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
