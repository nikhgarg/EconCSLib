import GCG24UserItemFairness.MainTheorems

/-!
# Paper Assumptions: GCG24 User-Item Fairness

This file records source model assumptions and paper-statement conditions used
by the compact human-facing interface. These are not proof certificates.
-/

namespace GCG24UserItemFairness

open scoped BigOperators

noncomputable section

/--
The source model uses strictly positive recommendation utilities. This covers
Proposition 2's symmetric model and Theorem 3's two opposing-type models.
-/
-- audit-premise: hPos : S.model.Positive
-- audit-premise: hPos : R.data.model.Positive
-- audit-premise: hPos' : R'.data.model.Positive
abbrev assumption_positive_recommendation_utilities {m n : ℕ}
    (W : RecommendationModel m n) : Prop :=
  W.Positive

/--
Theorem 3 compares two instances of the opposing two-type source model with
the same positive, strictly decreasing value vector.
-/
-- audit-premise: hred : R.reduced = OpposingTypes.twoTypeReducedModel alpha v
-- audit-premise: hred' : R'.reduced = OpposingTypes.twoTypeReducedModel alpha' v
-- audit-premise: hpos : ∀ j : Item n, 0 < v j
-- audit-premise: hdec : OpposingTypes.StrictlyDecreasingByIndex v
abbrev assumption_theorem3_opposing_type_model : Prop := True

/--
Theorem 3 first-half domain: `alpha` moves toward the balanced population from
below.
-/
-- audit-premise: halpha0 : 0 < alpha
-- audit-premise: halpha1 : alpha < 1
-- audit-premise: halpha0' : 0 < alpha'
-- audit-premise: halpha1' : alpha' < 1
-- audit-premise: halpha_le : alpha ≤ alpha'
-- audit-premise: halpha_half : alpha ≤ 1 / 2
-- audit-premise: halpha_half' : alpha' ≤ 1 / 2
abbrev assumption_theorem3_first_half_alpha_domain : Prop := True

/--
Theorem 3 second-half domain: `alpha` moves away from the balanced population
above `1 / 2`.
-/
-- audit-premise: halpha0 : 0 < alpha
-- audit-premise: halpha1 : alpha < 1
-- audit-premise: halpha0' : 0 < alpha'
-- audit-premise: halpha1' : alpha' < 1
-- audit-premise: halpha_le : alpha ≤ alpha'
-- audit-premise: halpha_half : 1 / 2 ≤ alpha
-- audit-premise: halpha_half' : 1 / 2 ≤ alpha'
abbrev assumption_theorem3_second_half_alpha_domain : Prop := True

/--
The Theorem 4 construction uses at least three items.
-/
-- audit-premise: hn : 2 < n
abbrev assumption_theorem4_at_least_three_items (n : ℕ) : Prop :=
  2 < n

/--
The Theorem 4 true model is represented by the two-type reduction witness.
-/
-- audit-premise: htrue : E.trueModel = Rtrue.data.model
abbrev assumption_theorem4_true_model_reduction {m n : ℕ}
    (E : EstimatedRecommendationModel m n) (Rtrue : ReductionWitness m n 2) : Prop :=
  E.trueModel = Rtrue.data.model

/--
The Theorem 4 estimated model is represented by the three-type reduction
witness.
-/
-- audit-premise: hestimated : E.estimatedModel = Rest.data.model
abbrev assumption_theorem4_estimated_model_reduction {m n : ℕ}
    (E : EstimatedRecommendationModel m n) (Rest : ReductionWitness m n 3) : Prop :=
  E.estimatedModel = Rest.data.model

/--
Theorem 4 fixes the true two-type model and the three-type estimated model
through the displayed reduced matrices.
-/
-- audit-premise: hredTrue : Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) (OpposingTypes.theorem4SmallValueVector (n := n) eps)
-- audit-premise: hredEst : Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta (OpposingTypes.theorem4SmallValueVector (n := n) eps)
abbrev assumption_theorem4_displayed_reduced_models : Prop := True

/--
Theorem 4's cold-start row is the estimated third type, whose true type is one
of the two opposing source rows.
-/
-- audit-premise: hknown0 : ∀ u : User m, Rest.data.types.toType u = 0 → Rtrue.data.types.toType u = 0
-- audit-premise: hknown1 : ∀ u : User m, Rest.data.types.toType u = 1 → Rtrue.data.types.toType u = 1
-- audit-premise: htrueType : Rtrue.data.types.toType u = 0
-- audit-premise: htrueType : Rtrue.data.types.toType u = 1
-- audit-premise: hestimatedType : Rest.data.types.toType u = 2
abbrev assumption_theorem4_cold_start_type_wiring : Prop := True

/--
Theorem 4 parameter domain for the arbitrary-large misestimation conclusion.
-/
-- audit-premise: heps : 0 < eps
-- audit-premise: hbeta : (n : ℝ)⁻¹ < beta
-- audit-premise: hbeta_half : beta < 1 / 2
abbrev assumption_theorem4_parameter_domain : Prop := True

end

end GCG24UserItemFairness
