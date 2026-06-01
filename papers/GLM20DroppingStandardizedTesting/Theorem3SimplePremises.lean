import GLM20DroppingStandardizedTesting.MainTheorems

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/-!
# Theorem 3 Simple Premises

Small bridges for the concrete two-group paper names already present in the
GLM20 files.

There is currently no corresponding concrete two-school source object in the
paper files.  In particular, the Theorem 3 wrappers still quantify over
`{School : Type*} {J1 J2 : School}` and take `hJ1_ne_J2 : J1 ≠ J2` explicitly;
no declarations named like `GLM20School`, `glm20J1`, or `glm20J2` exist to
discharge that premise here.
-/

/-- The paper's two named groups are distinct. -/
theorem glm20GroupA_ne_groupB :
    GLM20Group.groupA ≠ GLM20Group.groupB := by
  decide

/-- The paper's two named groups are distinct, in the reverse direction. -/
theorem glm20GroupB_ne_groupA :
    GLM20Group.groupB ≠ GLM20Group.groupA := by
  decide

/-- Paper schools used by the two-school strategic Theorem 3 surface. -/
inductive GLM20School where
  | J1
  | J2
deriving DecidableEq, Repr

/-- Paper notation for the first school in Theorem 3. -/
def glm20SchoolJ1 : GLM20School :=
  GLM20School.J1

/-- Paper notation for the second school in Theorem 3. -/
def glm20SchoolJ2 : GLM20School :=
  GLM20School.J2

/-- The paper's two named schools are distinct. -/
theorem glm20SchoolJ1_ne_J2 :
    glm20SchoolJ1 ≠ glm20SchoolJ2 := by
  decide

/--
The paper's usual population-share notation as a named row: group A has share
`1 - pi`, while group B has share `pi`.
-/
def glm20Theorem3PopulationShare (pi : ℝ) : GLM20Group → ℝ
  | GLM20Group.groupA => 1 - pi
  | GLM20Group.groupB => pi

/--
The paper's usual population-share notation, specialized to the concrete
`GLM20Group` names: group A has share `1 - pi`, group B has share `pi`.
-/
theorem glm20GroupA_populationShare_pos_of_pi_lt_one
    {pi : ℝ} (hpi_lt_one : pi < 1) :
    0 <
      (fun g : GLM20Group =>
        match g with
        | GLM20Group.groupA => 1 - pi
        | GLM20Group.groupB => pi) GLM20Group.groupA := by
  simp
  linarith

/--
The paper's usual population-share notation gives positive group-B share from
the source assumption `0 < pi`.
-/
theorem glm20GroupB_populationShare_pos_of_pi_pos
    {pi : ℝ} (hpi_pos : 0 < pi) :
    0 <
      (fun g : GLM20Group =>
        match g with
        | GLM20Group.groupA => 1 - pi
        | GLM20Group.groupB => pi) GLM20Group.groupB := by
  simpa

/--
Bundled positive-share premises for Theorem 3 routes when the abstract group
parameters are instantiated by `GLM20Group.groupA` and `GLM20Group.groupB`.
-/
theorem glm20Group_populationShare_pos_of_pi_mem_Ioo
    {pi : ℝ} (hpi : pi ∈ Set.Ioo (0 : ℝ) 1) :
    0 <
        (fun g : GLM20Group =>
          match g with
          | GLM20Group.groupA => 1 - pi
          | GLM20Group.groupB => pi) GLM20Group.groupA ∧
      0 <
        (fun g : GLM20Group =>
          match g with
          | GLM20Group.groupA => 1 - pi
          | GLM20Group.groupB => pi) GLM20Group.groupB := by
  exact
    ⟨glm20GroupA_populationShare_pos_of_pi_lt_one hpi.2,
      glm20GroupB_populationShare_pos_of_pi_pos hpi.1⟩

/--
The named Theorem 3 population-share row supplies positive shares for the
paper's two groups from `0 < pi < 1`.
-/
theorem glm20Theorem3PopulationShare_pos_of_pi_mem_Ioo
    {pi : ℝ} (hpi : pi ∈ Set.Ioo (0 : ℝ) 1) :
    0 < glm20Theorem3PopulationShare pi GLM20Group.groupA ∧
      0 < glm20Theorem3PopulationShare pi GLM20Group.groupB := by
  simpa [glm20Theorem3PopulationShare] using
    glm20Group_populationShare_pos_of_pi_mem_Ioo hpi

/--
Affine decreasing cost thresholds are continuous and strictly antitone on each
group's full-sub cost interval.
-/
theorem paper_theorem3_based_threshold_regularities_of_affine_decreasing
    {Group : Type*} {leftCost rightCost : Group → ℝ}
    (intercept slope : Group → ℝ) (hslope : ∀ g, 0 < slope g) :
    (∀ g,
      ContinuousOn (fun c => intercept g - slope g * c)
        (Set.Icc (leftCost g) (rightCost g))) ∧
      (∀ g,
        StrictAntiOn (fun c => intercept g - slope g * c)
          (Set.Icc (leftCost g) (rightCost g))) := by
  constructor
  · intro g
    exact (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  · intro g x _hx y _hy hxy
    have hmul : slope g * x < slope g * y :=
      mul_lt_mul_of_pos_left hxy (hslope g)
    nlinarith

/--
Bundled low/high version of
`paper_theorem3_based_threshold_regularities_of_affine_decreasing`, matching
the paired threshold-regularity premises in the fixed-law Theorem 3 route.
-/
theorem paper_theorem3_low_high_based_threshold_regularities_of_affine_decreasing
    {Group : Type*} {leftCost rightCost : Group → ℝ}
    (lowIntercept highIntercept lowSlope highSlope : Group → ℝ)
    (hlowSlope : ∀ g, 0 < lowSlope g)
    (hhighSlope : ∀ g, 0 < highSlope g) :
    (∀ g,
      ContinuousOn (fun c => lowIntercept g - lowSlope g * c)
        (Set.Icc (leftCost g) (rightCost g))) ∧
      (∀ g,
        StrictAntiOn (fun c => lowIntercept g - lowSlope g * c)
          (Set.Icc (leftCost g) (rightCost g))) ∧
        (∀ g,
          ContinuousOn (fun c => highIntercept g - highSlope g * c)
            (Set.Icc (leftCost g) (rightCost g))) ∧
          (∀ g,
            StrictAntiOn (fun c => highIntercept g - highSlope g * c)
              (Set.Icc (leftCost g) (rightCost g))) := by
  have hlow :=
    paper_theorem3_based_threshold_regularities_of_affine_decreasing
      (leftCost := leftCost) (rightCost := rightCost)
      lowIntercept lowSlope hlowSlope
  have hhigh :=
    paper_theorem3_based_threshold_regularities_of_affine_decreasing
      (leftCost := leftCost) (rightCost := rightCost)
      highIntercept highSlope hhighSlope
  exact ⟨hlow.1, hlow.2, hhigh.1, hhigh.2⟩

/--
Group-indexed source cost bounds for an interval that must lie below an
upper value, such as the equation-(50) sub/full inverse-CDF domain.
-/
def GLM20CostBoundsBelow {Group : Type*}
    (cost left right upper : Group → ℝ) : Prop :=
  ∀ g,
    0 < left g ∧ left g < right g ∧ right g < upper g ∧
      left g ≤ cost g ∧ cost g ≤ right g

/--
Group-indexed source cost bounds for an interval without a separate upper
inverse-CDF domain.
-/
def GLM20CostBounds {Group : Type*}
    (cost left right : Group → ℝ) : Prop :=
  ∀ g, 0 < left g ∧ left g < right g ∧ left g ≤ cost g ∧ cost g ≤ right g

/--
Sub/full source cost bounds unpack into the interval and inverse-CDF domain
premises used by the Theorem 3 equation-(50) route.
-/
theorem paper_theorem3_subFull_cost_premises_of_bounds
    {Group : Type*} {cost left right upper : Group → ℝ}
    (hbounds : GLM20CostBoundsBelow cost left right upper) :
    (∀ g, left g < right g) ∧
      (∀ g, 0 < left g) ∧
        (∀ g, right g < upper g) ∧
          (∀ g, cost g ∈ Set.Icc (left g) (right g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    exact (hbounds g).2.1
  · intro g
    exact (hbounds g).1
  · intro g
    exact (hbounds g).2.2.1
  · intro g
    exact ⟨(hbounds g).2.2.2.1, (hbounds g).2.2.2.2⟩

/--
Full/sub source cost bounds unpack into the interval premises used by the
Theorem 3 full-sub cost-row route.
-/
theorem paper_theorem3_fullSub_cost_premises_of_bounds
    {Group : Type*} {cost left right : Group → ℝ}
    (hbounds : GLM20CostBounds cost left right) :
    (∀ g, left g < right g) ∧
      (∀ g, 0 < left g) ∧
        (∀ g, cost g ∈ Set.Icc (left g) (right g)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g
    exact (hbounds g).2.1
  · intro g
    exact (hbounds g).1
  · intro g
    exact ⟨(hbounds g).2.2.1, (hbounds g).2.2.2⟩

/--
Theorem 3 source rows bundling the two full/full capacity equations and the
four cutoff-order comparisons that generate the full/full capacity-fill
premises.
-/
def GLM20Theorem3CapacityCutoffRows {Group : Type*}
    (api : StandardGaussianCDFAPI)
    (populationShare : Group → ℝ)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (groupA groupB : Group)
    (capacity1 capacity2 q1Sub q2Sub : ℝ)
    (fullFullCutoff : Group → ℝ) : Prop :=
  capacity1 =
      populationShare groupA *
          glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
            q1Sub +
        populationShare groupB *
          glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
            q1Sub ∧
    fullFullCutoff groupA ≤ q1Sub ∧
      fullFullCutoff groupB ≤ q1Sub ∧
        capacity2 =
            populationShare groupA *
                glm20StrategicSubEstimateMassAbove api
                  (subEstimateLaw groupA) q2Sub +
              populationShare groupB *
                glm20StrategicSubEstimateMassAbove api
                  (subEstimateLaw groupB) q2Sub ∧
          fullFullCutoff groupA ≤ q2Sub ∧
            fullFullCutoff groupB ≤ q2Sub

/--
Unpack the bundled Theorem 3 capacity/cutoff rows into the six scalar premises
used by lower-level wrappers.
-/
theorem paper_theorem3_capacity_cutoff_rows_components
    {Group : Type*} {api : StandardGaussianCDFAPI}
    {populationShare : Group → ℝ}
    {subEstimateLaw : Group → GaussianScaleLaw}
    {groupA groupB : Group}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff : Group → ℝ}
    (hrows :
      GLM20Theorem3CapacityCutoffRows api populationShare subEstimateLaw
        groupA groupB capacity1 capacity2 q1Sub q2Sub fullFullCutoff) :
    capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q1Sub ∧
      fullFullCutoff groupA ≤ q1Sub ∧
        fullFullCutoff groupB ≤ q1Sub ∧
          capacity2 =
              populationShare groupA *
                  glm20StrategicSubEstimateMassAbove api
                    (subEstimateLaw groupA) q2Sub +
                populationShare groupB *
                  glm20StrategicSubEstimateMassAbove api
                    (subEstimateLaw groupB) q2Sub ∧
            fullFullCutoff groupA ≤ q2Sub ∧
              fullFullCutoff groupB ≤ q2Sub :=
  hrows

/--
Theorem 3 source rows for school `J2`'s condition-(11)--(12) survivor side.

These are source assumptions, not consequences of the full/full
capacity/cutoff rows: for each possible expanding group, the other group's
sub/full mass fills school `J2` and its weighted `J2` admitted merit strictly
dominates the two-group `(P_sub,P_sub)` weighted merit.
-/
def GLM20Theorem3J2SurvivorRows {Group School : Type*}
    (populationShare : Group → ℝ)
    (subFullMass : Group → ℝ)
    (subSubMerit subFullMerit : School → Group → ℝ)
    (J2 : School) (groupA groupB : Group) (capacity2 : ℝ) : Prop :=
  subFullMass groupB ≥ capacity2 ∧
    populationShare groupB * subFullMerit J2 groupB >
      populationShare groupA * subSubMerit J2 groupA +
        populationShare groupB * subSubMerit J2 groupB ∧
      subFullMass groupA ≥ capacity2 ∧
        populationShare groupA * subFullMerit J2 groupA >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB

/--
Unpack the bundled condition-(11)--(12) survivor rows into the four scalar
source assumptions used by lower-level Theorem 3 wrappers.
-/
theorem paper_theorem3_j2_survivor_rows_components
    {Group School : Type*}
    {populationShare : Group → ℝ}
    {subFullMass : Group → ℝ}
    {subSubMerit subFullMerit : School → Group → ℝ}
    {J2 : School} {groupA groupB : Group} {capacity2 : ℝ}
    (hrows :
      GLM20Theorem3J2SurvivorRows populationShare subFullMass
        subSubMerit subFullMerit J2 groupA groupB capacity2) :
    subFullMass groupB ≥ capacity2 ∧
      populationShare groupB * subFullMerit J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB ∧
        subFullMass groupA ≥ capacity2 ∧
          populationShare groupA * subFullMerit J2 groupA >
            populationShare groupA * subSubMerit J2 groupA +
              populationShare groupB * subSubMerit J2 groupB :=
  hrows

/--
Theorem 3 source rows for the strict-merit half of school `J2`'s
condition-(11)--(12) survivor side.

On feasibility-aware surfaces the survivor capacity rows can be carried by the
feasibility predicate, so downstream wrappers should expose only these two
strict condition-(12) merit inequalities when possible.
-/
def GLM20Theorem3J2StrictSurvivorMeritRows {Group School : Type*}
    (populationShare : Group → ℝ)
    (subSubMerit subFullMerit : School → Group → ℝ)
    (J2 : School) (groupA groupB : Group) : Prop :=
  populationShare groupB * subFullMerit J2 groupB >
      populationShare groupA * subSubMerit J2 groupA +
        populationShare groupB * subSubMerit J2 groupB ∧
    populationShare groupA * subFullMerit J2 groupA >
      populationShare groupA * subSubMerit J2 groupA +
        populationShare groupB * subSubMerit J2 groupB

/--
Unpack the strict-merit-only school-`J2` survivor rows into the two scalar
condition-(12) inequalities used by feasibility-aware Theorem 3 routes.
-/
theorem paper_theorem3_j2_strict_survivor_merit_rows_components
    {Group School : Type*}
    {populationShare : Group → ℝ}
    {subSubMerit subFullMerit : School → Group → ℝ}
    {J2 : School} {groupA groupB : Group}
    (hrows :
      GLM20Theorem3J2StrictSurvivorMeritRows populationShare
        subSubMerit subFullMerit J2 groupA groupB) :
    populationShare groupB * subFullMerit J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB ∧
      populationShare groupA * subFullMerit J2 groupA >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB :=
  hrows

/--
The full condition-(11)--(12) school-`J2` survivor bundle implies the
strict-merit-only bundle used by feasibility-aware routes.
-/
theorem paper_theorem3_j2_strict_survivor_merit_rows_of_survivor_rows
    {Group School : Type*}
    {populationShare : Group → ℝ}
    {subFullMass : Group → ℝ}
    {subSubMerit subFullMerit : School → Group → ℝ}
    {J2 : School} {groupA groupB : Group} {capacity2 : ℝ}
    (hrows :
      GLM20Theorem3J2SurvivorRows populationShare subFullMass
        subSubMerit subFullMerit J2 groupA groupB capacity2) :
    GLM20Theorem3J2StrictSurvivorMeritRows populationShare
      subSubMerit subFullMerit J2 groupA groupB := by
  exact ⟨hrows.2.1, hrows.2.2.2⟩

/--
Feed a feasibility-aware endpoint that only needs the two strict school-`J2`
survivor-merit inequalities from the bundled strict-merit row predicate.
-/
theorem paper_theorem3_feasible_endpoint_of_j2_strict_survivor_merit_rows
    {Group School : Type*}
    {populationShare : Group → ℝ}
    {subSubMerit subFullMerit : School → Group → ℝ}
    {J2 : School} {groupA groupB : Group} {Conclusion : Prop}
    (endpoint :
      (populationShare groupB * subFullMerit J2 groupB >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB) →
        (populationShare groupA * subFullMerit J2 groupA >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB) →
          Conclusion)
    (hrows :
      GLM20Theorem3J2StrictSurvivorMeritRows populationShare
        subSubMerit subFullMerit J2 groupA groupB) :
    Conclusion :=
  endpoint hrows.1 hrows.2

/--
Theorem 3 source row for the sub/full affine Gaussian tail-mean route:
positive projected scale, positive affine slope, and the two endpoint
threshold crossings used to generate the sub/full admitted-merit comparison.
-/
def GLM20Theorem3SubFullAffineTailRows {Group : Type*}
    (Q : StandardGaussianQuantileAPI)
    (leftCost rightCost q2Full scale v2 intercept slope
      freeThreshold : Group → ℝ) : Prop :=
  (∀ g, 0 < scale g) ∧
    (∀ g, 0 < slope g) ∧
      (∀ g, freeThreshold g <
        intercept g -
          slope g *
            (q2Full g -
              scale g * Q.quantile (1 - leftCost g / v2 g))) ∧
        (∀ g,
          intercept g -
              slope g *
                (q2Full g -
                  scale g * Q.quantile (1 - rightCost g / v2 g)) <
            freeThreshold g)

/--
Unpack the bundled sub/full affine tail-mean row into the four scalar premises
used by lower-level wrappers.
-/
theorem paper_theorem3_subFull_affine_tail_rows_components
    {Group : Type*} {Q : StandardGaussianQuantileAPI}
    {leftCost rightCost q2Full scale v2 intercept slope
      freeThreshold : Group → ℝ}
    (hrows :
      GLM20Theorem3SubFullAffineTailRows Q leftCost rightCost q2Full
        scale v2 intercept slope freeThreshold) :
    (∀ g, 0 < scale g) ∧
      (∀ g, 0 < slope g) ∧
        (∀ g, freeThreshold g <
          intercept g -
            slope g *
              (q2Full g -
                scale g * Q.quantile (1 - leftCost g / v2 g))) ∧
          (∀ g,
            intercept g -
                slope g *
                  (q2Full g -
                    scale g * Q.quantile (1 - rightCost g / v2 g)) <
            freeThreshold g) :=
  hrows

/--
Theorem 3 source rows for the full/sub affine threshold route.

This bundles the four endpoint threshold crossings, the free-test threshold
order, the cost-indexed based-threshold prior-mean/order rows, and the two
positive affine slopes used to generate the low/high full-sub posterior
cost-row regularity.
-/
def GLM20Theorem3FullSubAffineThresholdRows {Group HighFreeFeature
    LowBasedFeature : Type*}
    [Fintype HighFreeFeature] [Fintype LowBasedFeature]
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowBasedFamily : Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (leftCost rightCost lowFreeThreshold highFreeThreshold lowIntercept
      highIntercept lowSlope highSlope : Group → ℝ) : Prop :=
  (∀ g, lowFreeThreshold g < lowIntercept g - lowSlope g * leftCost g) ∧
    (∀ g, lowIntercept g - lowSlope g * rightCost g <
      lowFreeThreshold g) ∧
      (∀ g, highFreeThreshold g <
        highIntercept g - highSlope g * leftCost g) ∧
        (∀ g, highIntercept g - highSlope g * rightCost g <
          highFreeThreshold g) ∧
          (∀ g, (highFreeFamily g).priorMean < highFreeThreshold g) ∧
            (∀ g, highFreeThreshold g ≤ lowFreeThreshold g) ∧
              (∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
                (lowBasedFamily g c).priorMean <
                  lowIntercept g - lowSlope g * c) ∧
                (∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
                  lowIntercept g - lowSlope g * c ≤
                    highIntercept g - highSlope g * c) ∧
                  (∀ g, 0 < lowSlope g) ∧
                    (∀ g, 0 < highSlope g)

/--
Unpack the bundled full/sub affine threshold row into the scalar premises used
by lower-level wrappers.
-/
theorem paper_theorem3_fullSub_affine_threshold_rows_components
    {Group HighFreeFeature LowBasedFeature : Type*}
    [Fintype HighFreeFeature] [Fintype LowBasedFeature]
    {highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature}
    {lowBasedFamily : Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature}
    {leftCost rightCost lowFreeThreshold highFreeThreshold lowIntercept
      highIntercept lowSlope highSlope : Group → ℝ}
    (hrows :
      GLM20Theorem3FullSubAffineThresholdRows highFreeFamily lowBasedFamily
        leftCost rightCost lowFreeThreshold highFreeThreshold lowIntercept
        highIntercept lowSlope highSlope) :
    (∀ g, lowFreeThreshold g < lowIntercept g - lowSlope g * leftCost g) ∧
      (∀ g, lowIntercept g - lowSlope g * rightCost g <
        lowFreeThreshold g) ∧
        (∀ g, highFreeThreshold g <
          highIntercept g - highSlope g * leftCost g) ∧
          (∀ g, highIntercept g - highSlope g * rightCost g <
            highFreeThreshold g) ∧
            (∀ g, (highFreeFamily g).priorMean < highFreeThreshold g) ∧
              (∀ g, highFreeThreshold g ≤ lowFreeThreshold g) ∧
                (∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
                  (lowBasedFamily g c).priorMean <
                    lowIntercept g - lowSlope g * c) ∧
                  (∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
                    lowIntercept g - lowSlope g * c ≤
                      highIntercept g - highSlope g * c) ∧
                    (∀ g, 0 < lowSlope g) ∧
                      (∀ g, 0 < highSlope g) :=
  hrows

/--
Theorem 3 source rows for the full/sub fixed posterior-law route.

The compact Theorem 3 wrapper needs two posterior-mean law equalities for the
low/high based full-sub rows.  This source predicate states the primitive
Gaussian rows that imply those law equalities: prior means, prior variances,
and total centered signal precisions agree with the relevant free-family or
extra-signal family.
-/
def GLM20Theorem3FullSubFixedLawRows {Group LowBasedFeature
    HighFreeFeature : Type*}
    [Fintype LowBasedFeature] [Fintype HighFreeFeature]
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (freeExtraNoiseMean freeExtraNoiseVar : Group → ℝ)
    (hfreeExtraNoiseVar : ∀ g, 0 < freeExtraNoiseVar g)
    (lowBasedFamily : Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (basedExtraNoiseMean basedExtraNoiseVar : Group → ℝ → ℝ)
    (hbasedExtraNoiseVar : ∀ g c, 0 < basedExtraNoiseVar g c) : Prop :=
  (∀ g c,
    (lowBasedFamily g c).priorMean =
      ((highFreeFamily g).withExtraSignal
        (freeExtraNoiseMean g) (freeExtraNoiseVar g)
        (hfreeExtraNoiseVar g)).priorMean) ∧
    (∀ g c,
      (lowBasedFamily g c).priorVar =
        ((highFreeFamily g).withExtraSignal
          (freeExtraNoiseMean g) (freeExtraNoiseVar g)
          (hfreeExtraNoiseVar g)).priorVar) ∧
      (∀ g c,
        (lowBasedFamily g c).centeredFamily.signalPrecisionSum =
          ((highFreeFamily g).withExtraSignal
            (freeExtraNoiseMean g) (freeExtraNoiseVar g)
            (hfreeExtraNoiseVar g)).centeredFamily.signalPrecisionSum) ∧
        (∀ g c,
          ((lowBasedFamily g c).withExtraSignal
            (basedExtraNoiseMean g c) (basedExtraNoiseVar g c)
            (hbasedExtraNoiseVar g c)).priorMean =
            (highFreeFamily g).priorMean) ∧
          (∀ g c,
            ((lowBasedFamily g c).withExtraSignal
              (basedExtraNoiseMean g c) (basedExtraNoiseVar g c)
              (hbasedExtraNoiseVar g c)).priorVar =
              (highFreeFamily g).priorVar) ∧
            (∀ g c,
              ((lowBasedFamily g c).withExtraSignal
                (basedExtraNoiseMean g c) (basedExtraNoiseVar g c)
                (hbasedExtraNoiseVar g c)).centeredFamily.signalPrecisionSum =
                (highFreeFamily g).centeredFamily.signalPrecisionSum)

/--
Unpack the primitive full/sub fixed-law source rows into the two posterior-law
equalities consumed by the compact Theorem 3 wrapper.
-/
theorem paper_theorem3_fullSub_fixed_law_rows_components
    {Group LowBasedFeature HighFreeFeature : Type*}
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    {highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature}
    {freeExtraNoiseMean freeExtraNoiseVar : Group → ℝ}
    {hfreeExtraNoiseVar : ∀ g, 0 < freeExtraNoiseVar g}
    {lowBasedFamily : Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature}
    {basedExtraNoiseMean basedExtraNoiseVar : Group → ℝ → ℝ}
    {hbasedExtraNoiseVar : ∀ g c, 0 < basedExtraNoiseVar g c}
    (hrows :
      GLM20Theorem3FullSubFixedLawRows highFreeFamily
        freeExtraNoiseMean freeExtraNoiseVar hfreeExtraNoiseVar
        lowBasedFamily basedExtraNoiseMean basedExtraNoiseVar
        hbasedExtraNoiseVar) :
    (∀ g c,
      (lowBasedFamily g c).posteriorMeanScaleLaw =
        ((highFreeFamily g).withExtraSignal
          (freeExtraNoiseMean g) (freeExtraNoiseVar g)
          (hfreeExtraNoiseVar g)).posteriorMeanScaleLaw) ∧
      (∀ g c,
        ((lowBasedFamily g c).withExtraSignal
          (basedExtraNoiseMean g c) (basedExtraNoiseVar g c)
          (hbasedExtraNoiseVar g c)).posteriorMeanScaleLaw =
          (highFreeFamily g).posteriorMeanScaleLaw) := by
  rcases hrows with
    ⟨hlowMean, hlowVar, hlowPrecision, hhighMean, hhighVar,
      hhighPrecision⟩
  constructor
  · intro g c
    exact
      GaussianOffsetSignalFamily.posteriorMeanScaleLaw_eq_of_priorMean_eq_priorVar_eq_signalPrecisionSum_eq
        (lowBasedFamily g c)
        ((highFreeFamily g).withExtraSignal
          (freeExtraNoiseMean g) (freeExtraNoiseVar g)
          (hfreeExtraNoiseVar g))
        (hlowMean g c) (hlowVar g c) (hlowPrecision g c)
  · intro g c
    exact
      GaussianOffsetSignalFamily.posteriorMeanScaleLaw_eq_of_priorMean_eq_priorVar_eq_signalPrecisionSum_eq
        ((lowBasedFamily g c).withExtraSignal
          (basedExtraNoiseMean g c) (basedExtraNoiseVar g c)
          (hbasedExtraNoiseVar g c))
        (highFreeFamily g)
        (hhighMean g c) (hhighVar g c) (hhighPrecision g c)

/--
Theorem 3 source-row bundle for the generated full/sub Gaussian route.

This packages the full/sub assumptions that usually travel together: the two
positive extra-noise rows needed to construct the generated low/high
families, the primitive fixed posterior-law rows, the affine threshold rows,
and the full/sub cost interval bounds.
-/
structure GLM20Theorem3FullSubGeneratedRows {Group LowBasedFeature
    HighFreeFeature : Type*}
    [Fintype LowBasedFeature] [Fintype HighFreeFeature]
    (testCost fullSubLeftCost fullSubRightCost : Group → ℝ)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (freeExtraNoiseMean freeExtraNoiseVar : Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : Group → ℝ)
    (lowBasedFamily : Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (basedExtraNoiseMean basedExtraNoiseVar : Group → ℝ → ℝ)
    (lowBasedThresholdIntercept highBasedThresholdIntercept
      lowBasedThresholdSlope highBasedThresholdSlope : Group → ℝ) : Prop where
  freeExtraNoiseVar_pos : ∀ g, 0 < freeExtraNoiseVar g
  basedExtraNoiseVar_pos : ∀ g c, 0 < basedExtraNoiseVar g c
  fixedLawRows :
    GLM20Theorem3FullSubFixedLawRows highFreeFamily
      freeExtraNoiseMean freeExtraNoiseVar freeExtraNoiseVar_pos
      lowBasedFamily basedExtraNoiseMean basedExtraNoiseVar
      basedExtraNoiseVar_pos
  affineThresholdRows :
    GLM20Theorem3FullSubAffineThresholdRows highFreeFamily lowBasedFamily
      fullSubLeftCost fullSubRightCost fullSubLowFreeThreshold
      fullSubHighFreeThreshold lowBasedThresholdIntercept
      highBasedThresholdIntercept lowBasedThresholdSlope
      highBasedThresholdSlope
  costBounds : GLM20CostBounds testCost fullSubLeftCost fullSubRightCost

/--
Build the generated full/sub row package directly from primitive Gaussian
source rows.

This is the raw-source entrypoint for the compact Theorem 3 route: the caller
supplies positive extra-noise rows, the six prior-mean/prior-variance/precision
equalities that generate the fixed posterior laws, the affine threshold rows,
and the full/sub cost bounds.
-/
theorem paper_theorem3_fullSub_generated_rows_of_prior_precision_rows
    {Group LowBasedFeature HighFreeFeature : Type*}
    [Fintype LowBasedFeature] [Fintype HighFreeFeature]
    {testCost fullSubLeftCost fullSubRightCost : Group → ℝ}
    {highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature}
    {freeExtraNoiseMean freeExtraNoiseVar : Group → ℝ}
    {fullSubLowFreeThreshold fullSubHighFreeThreshold : Group → ℝ}
    {lowBasedFamily : Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature}
    {basedExtraNoiseMean basedExtraNoiseVar : Group → ℝ → ℝ}
    {lowBasedThresholdIntercept highBasedThresholdIntercept
      lowBasedThresholdSlope highBasedThresholdSlope : Group → ℝ}
    (hfreeExtraNoiseVar : ∀ g, 0 < freeExtraNoiseVar g)
    (hbasedExtraNoiseVar : ∀ g c, 0 < basedExtraNoiseVar g c)
    (hlowPriorMean :
      ∀ g c,
        (lowBasedFamily g c).priorMean =
          ((highFreeFamily g).withExtraSignal
            (freeExtraNoiseMean g) (freeExtraNoiseVar g)
            (hfreeExtraNoiseVar g)).priorMean)
    (hlowPriorVar :
      ∀ g c,
        (lowBasedFamily g c).priorVar =
          ((highFreeFamily g).withExtraSignal
            (freeExtraNoiseMean g) (freeExtraNoiseVar g)
            (hfreeExtraNoiseVar g)).priorVar)
    (hlowPrecision :
      ∀ g c,
        (lowBasedFamily g c).centeredFamily.signalPrecisionSum =
          ((highFreeFamily g).withExtraSignal
            (freeExtraNoiseMean g) (freeExtraNoiseVar g)
            (hfreeExtraNoiseVar g)).centeredFamily.signalPrecisionSum)
    (hhighPriorMean :
      ∀ g c,
        ((lowBasedFamily g c).withExtraSignal
          (basedExtraNoiseMean g c) (basedExtraNoiseVar g c)
          (hbasedExtraNoiseVar g c)).priorMean =
          (highFreeFamily g).priorMean)
    (hhighPriorVar :
      ∀ g c,
        ((lowBasedFamily g c).withExtraSignal
          (basedExtraNoiseMean g c) (basedExtraNoiseVar g c)
          (hbasedExtraNoiseVar g c)).priorVar =
          (highFreeFamily g).priorVar)
    (hhighPrecision :
      ∀ g c,
        ((lowBasedFamily g c).withExtraSignal
          (basedExtraNoiseMean g c) (basedExtraNoiseVar g c)
          (hbasedExtraNoiseVar g c)).centeredFamily.signalPrecisionSum =
          (highFreeFamily g).centeredFamily.signalPrecisionSum)
    (haffineThresholdRows :
      GLM20Theorem3FullSubAffineThresholdRows highFreeFamily
        lowBasedFamily fullSubLeftCost fullSubRightCost
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        lowBasedThresholdIntercept highBasedThresholdIntercept
        lowBasedThresholdSlope highBasedThresholdSlope)
    (hcostBounds :
      GLM20CostBounds testCost fullSubLeftCost fullSubRightCost) :
    GLM20Theorem3FullSubGeneratedRows testCost fullSubLeftCost
      fullSubRightCost highFreeFamily freeExtraNoiseMean freeExtraNoiseVar
      fullSubLowFreeThreshold fullSubHighFreeThreshold lowBasedFamily
      basedExtraNoiseMean basedExtraNoiseVar lowBasedThresholdIntercept
      highBasedThresholdIntercept lowBasedThresholdSlope
      highBasedThresholdSlope where
  freeExtraNoiseVar_pos := hfreeExtraNoiseVar
  basedExtraNoiseVar_pos := hbasedExtraNoiseVar
  fixedLawRows :=
    ⟨hlowPriorMean, hlowPriorVar, hlowPrecision, hhighPriorMean,
      hhighPriorVar, hhighPrecision⟩
  affineThresholdRows := haffineThresholdRows
  costBounds := hcostBounds

/--
Theorem 3 source rows for the two generated keep-test signal families.

The compact source-family routes build each school's test-keeping family by
adding one positive-variance Gaussian signal to its test-dropping family.  The
school-specific threshold rows say the drop-family prior mean is below the
drop threshold and the drop threshold is weakly below the keep threshold.
-/
def GLM20Theorem3KeepSignalRows {Group FeatureDrop : Type*}
    [Fintype FeatureDrop]
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseVar J2ExtraNoiseVar : Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ) : Prop :=
  (∀ g, 0 < J1ExtraNoiseVar g) ∧
    (∀ g, 0 < J2ExtraNoiseVar g) ∧
      (∀ g, (J1DropFamily g).priorMean < J1DropThreshold g) ∧
        (∀ g, J1DropThreshold g ≤ J1KeepThreshold g) ∧
          (∀ g, (J2DropFamily g).priorMean < J2DropThreshold g) ∧
            (∀ g, J2DropThreshold g ≤ J2KeepThreshold g)

/--
Theorem 3 public source-row bundle for the current paper-groups/schools
academic-merit route.

This gathers the row packages that the compact public Theorem 3 wrapper
otherwise exposes separately: generated keep-signal rows, sub/full affine-tail
rows, generated full/sub rows, sub/full cost bounds, capacity/cutoff rows, and
school-`J2` survivor rows.
-/
structure GLM20Theorem3AcademicMeritPublicRows
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Fintype HighFreeFeature]
    [Fintype LowBasedFeature]
    (testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ)
    (capacity1 capacity2 q1Sub q2Sub pi : ℝ)
    (fullFullCutoff : GLM20Group → ℝ)
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase : GLM20School → GLM20Group → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope : GLM20Group → ℝ) : Prop where
  keepSignalRows :
    GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
      J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold
  subFullAffineTailRows :
    GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
      subFullLeftCost subFullRightCost subFullQ2Full subFullScale
      subFullV2 subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold
  fullSubGeneratedRows :
    GLM20Theorem3FullSubGeneratedRows testCost fullSubLeftCost
      fullSubRightCost fullSubHighFreeFamily fullSubFreeExtraNoiseMean
      fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
      fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
  subFullCostBounds :
    GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
      subFullV2
  capacityCutoffRows :
    GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
      (glm20Theorem3PopulationShare pi) subEstimateLaw
      GLM20Group.groupA GLM20Group.groupB capacity1 capacity2 q1Sub q2Sub
      fullFullCutoff
  j2SurvivorRows :
    GLM20Theorem3J2SurvivorRows (glm20Theorem3PopulationShare pi)
      subFullMass subSubMerit subFullMeritBase glm20SchoolJ2
      GLM20Group.groupA GLM20Group.groupB capacity2

/--
Theorem 3 public source-row bundle with the school-`J2` survivor side reduced
to the strict condition-(12) merit inequalities.

The survivor capacity-fill rows belong to the feasibility/capacity surface, so
this package keeps the human-facing source assumption at the narrower
strict-merit seam.
-/
structure GLM20Theorem3AcademicMeritStrictSurvivorPublicRows
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Fintype HighFreeFeature]
    [Fintype LowBasedFeature]
    (testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ)
    (capacity1 capacity2 q1Sub q2Sub pi : ℝ)
    (fullFullCutoff : GLM20Group → ℝ)
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMerit subFullMeritBase : GLM20School → GLM20Group → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope : GLM20Group → ℝ) : Prop where
  keepSignalRows :
    GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
      J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold
  subFullAffineTailRows :
    GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
      subFullLeftCost subFullRightCost subFullQ2Full subFullScale
      subFullV2 subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold
  fullSubGeneratedRows :
    GLM20Theorem3FullSubGeneratedRows testCost fullSubLeftCost
      fullSubRightCost fullSubHighFreeFamily fullSubFreeExtraNoiseMean
      fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
      fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
  subFullCostBounds :
    GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
      subFullV2
  capacityCutoffRows :
    GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
      (glm20Theorem3PopulationShare pi) subEstimateLaw
      GLM20Group.groupA GLM20Group.groupB capacity1 capacity2 q1Sub q2Sub
      fullFullCutoff
  j2StrictSurvivorMeritRows :
    GLM20Theorem3J2StrictSurvivorMeritRows
      (glm20Theorem3PopulationShare pi) subSubMerit subFullMeritBase
      glm20SchoolJ2 GLM20Group.groupA GLM20Group.groupB

/--
Theorem 3 public source-row bundle for the preferred feasibility-aware route,
with the paper population-share domain bundled into the same public premise.

This is the surface a reviewer should normally supply: all generated-row,
capacity/cutoff, cost-bound, strict survivor-merit, and `0 < pi < 1` facts live
in one package.
-/
structure GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Fintype HighFreeFeature]
    [Fintype LowBasedFeature]
    (testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ)
    (capacity1 capacity2 q1Sub q2Sub pi : ℝ)
    (fullFullCutoff : GLM20Group → ℝ)
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMerit subFullMeritBase : GLM20School → GLM20Group → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope : GLM20Group → ℝ) : Prop where
  rows :
    GLM20Theorem3AcademicMeritStrictSurvivorPublicRows testCost
      subFullLeftCost subFullRightCost fullSubLeftCost fullSubRightCost
      capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff subEstimateLaw
      subSubMerit subFullMeritBase J1DropFamily J2DropFamily
      J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale
      subFullV2 subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold fullSubHighFreeFamily fullSubFreeExtraNoiseMean
      fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
      fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
  populationShare_mem : pi ∈ Set.Ioo (0 : ℝ) 1

/--
Package strict-survivor public rows and the paper population-share domain into
the preferred single public-row bundle.
-/
theorem paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_rows
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Fintype HighFreeFeature]
    [Fintype LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff : GLM20Group → ℝ}
    {subEstimateLaw : GLM20Group → GaussianScaleLaw}
    {subSubMerit subFullMeritBase : GLM20School → GLM20Group → ℝ}
    {J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop}
    {J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ}
    {J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ}
    {fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature}
    {fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ}
    {fullSubLowFreeThreshold fullSubHighFreeThreshold : GLM20Group → ℝ}
    {fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature}
    {fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ}
    {fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope : GLM20Group → ℝ}
    (hrows :
      GLM20Theorem3AcademicMeritStrictSurvivorPublicRows testCost
        subFullLeftCost subFullRightCost fullSubLeftCost fullSubRightCost
        capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff subEstimateLaw
        subSubMerit subFullMeritBase J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
        J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold
        fullSubHighFreeFamily fullSubFreeExtraNoiseMean
        fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
        fullSubHighFreeThreshold fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1) :
    GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare
      testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff
      subEstimateLaw subSubMerit subFullMeritBase J1DropFamily J2DropFamily
      J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale subFullV2
      subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold fullSubHighFreeFamily fullSubFreeExtraNoiseMean
      fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
      fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope where
  rows := hrows
  populationShare_mem := hpi

/--
The older four-row public bundle implies the feasibility-aware strict-survivor
public bundle by dropping the two survivor capacity-fill rows.
-/
theorem paper_theorem3_academic_merit_strict_survivor_public_rows_of_public_rows
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Fintype HighFreeFeature]
    [Fintype LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff : GLM20Group → ℝ}
    {subEstimateLaw : GLM20Group → GaussianScaleLaw}
    {subFullMass : GLM20Group → ℝ}
    {subSubMerit subFullMeritBase : GLM20School → GLM20Group → ℝ}
    {J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop}
    {J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ}
    {J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ}
    {fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature}
    {fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ}
    {fullSubLowFreeThreshold fullSubHighFreeThreshold : GLM20Group → ℝ}
    {fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature}
    {fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ}
    {fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope : GLM20Group → ℝ}
    (hrows :
      GLM20Theorem3AcademicMeritPublicRows testCost subFullLeftCost
        subFullRightCost fullSubLeftCost fullSubRightCost capacity1
        capacity2 q1Sub q2Sub pi fullFullCutoff subEstimateLaw
        subFullMass subSubMerit subFullMeritBase J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
        J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold
        fullSubHighFreeFamily fullSubFreeExtraNoiseMean
        fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
        fullSubHighFreeThreshold fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope) :
    GLM20Theorem3AcademicMeritStrictSurvivorPublicRows testCost
      subFullLeftCost subFullRightCost fullSubLeftCost fullSubRightCost
      capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff subEstimateLaw
      subSubMerit subFullMeritBase J1DropFamily J2DropFamily
      J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale
      subFullV2 subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold fullSubHighFreeFamily fullSubFreeExtraNoiseMean
      fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
      fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope where
  keepSignalRows := hrows.keepSignalRows
  subFullAffineTailRows := hrows.subFullAffineTailRows
  fullSubGeneratedRows := hrows.fullSubGeneratedRows
  subFullCostBounds := hrows.subFullCostBounds
  capacityCutoffRows := hrows.capacityCutoffRows
  j2StrictSurvivorMeritRows :=
    paper_theorem3_j2_strict_survivor_merit_rows_of_survivor_rows
      hrows.j2SurvivorRows

/--
The older four-row public bundle plus the paper population-share domain implies
the preferred single public-row bundle.
-/
theorem paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_public_rows
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Fintype HighFreeFeature]
    [Fintype LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff : GLM20Group → ℝ}
    {subEstimateLaw : GLM20Group → GaussianScaleLaw}
    {subFullMass : GLM20Group → ℝ}
    {subSubMerit subFullMeritBase : GLM20School → GLM20Group → ℝ}
    {J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop}
    {J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ}
    {J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ}
    {fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature}
    {fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ}
    {fullSubLowFreeThreshold fullSubHighFreeThreshold : GLM20Group → ℝ}
    {fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature}
    {fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ}
    {fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope : GLM20Group → ℝ}
    (hrows :
      GLM20Theorem3AcademicMeritPublicRows testCost subFullLeftCost
        subFullRightCost fullSubLeftCost fullSubRightCost capacity1
        capacity2 q1Sub q2Sub pi fullFullCutoff subEstimateLaw
        subFullMass subSubMerit subFullMeritBase J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
        J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold
        fullSubHighFreeFamily fullSubFreeExtraNoiseMean
        fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
        fullSubHighFreeThreshold fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1) :
    GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare
      testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff
      subEstimateLaw subSubMerit subFullMeritBase J1DropFamily J2DropFamily
      J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale subFullV2
      subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold fullSubHighFreeFamily fullSubFreeExtraNoiseMean
      fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
      fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :=
  paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_rows
    (paper_theorem3_academic_merit_strict_survivor_public_rows_of_public_rows
      hrows)
    hpi

/--
Unpack the bundled generated keep-test signal rows into the scalar premises
used by the lower Theorem 3 wrappers.
-/
theorem paper_theorem3_keep_signal_rows_components
    {Group FeatureDrop : Type*}
    [Fintype FeatureDrop]
    {J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop}
    {J1ExtraNoiseVar J2ExtraNoiseVar : Group → ℝ}
    {J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ}
    (hrows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold) :
    (∀ g, 0 < J1ExtraNoiseVar g) ∧
      (∀ g, 0 < J2ExtraNoiseVar g) ∧
        (∀ g, (J1DropFamily g).priorMean < J1DropThreshold g) ∧
          (∀ g, J1DropThreshold g ≤ J1KeepThreshold g) ∧
            (∀ g, (J2DropFamily g).priorMean < J2DropThreshold g) ∧
              (∀ g, J2DropThreshold g ≤ J2KeepThreshold g) :=
  hrows

/--
The full/full capacity-fill premise used in Theorem 3 follows from the paper's
cutoff order: if each full/full group cutoff is weakly below the common source
cutoff `q`, then the sum of upper-tail masses at the full/full cutoffs is at
least the capacity filled at `q`.
-/
theorem paper_theorem3_fullFull_fill_capacity_of_cutoff_le
    {Group : Type*} (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    {groupA groupB : Group} {populationShare : Group → ℝ}
    {capacity q : ℝ} {fullFullCutoff : Group → ℝ}
    (hcapacity :
      capacity =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA) q +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB) q)
    (hshareA : 0 ≤ populationShare groupA)
    (hshareB : 0 ≤ populationShare groupB)
    (hcutA : fullFullCutoff groupA ≤ q)
    (hcutB : fullFullCutoff groupB ≤ q) :
    capacity ≤
      populationShare groupA *
          glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw groupA) (fullFullCutoff groupA) +
        populationShare groupB *
          glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw groupB) (fullFullCutoff groupB) := by
  rw [hcapacity]
  have hA :
      glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA) q ≤
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          (fullFullCutoff groupA) := by
    simpa [glm20StrategicSubEstimateMassAbove] using
      (api.thresholdPassProb_antitone_threshold (subEstimateLaw groupA) hcutA)
  have hB :
      glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB) q ≤
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          (fullFullCutoff groupB) := by
    simpa [glm20StrategicSubEstimateMassAbove] using
      (api.thresholdPassProb_antitone_threshold (subEstimateLaw groupB) hcutB)
  exact
    add_le_add
      (mul_le_mul_of_nonneg_left hA hshareA)
      (mul_le_mul_of_nonneg_left hB hshareB)

/--
The two full/full capacity-fill premises used by Theorem 3, bundled for the
two school cutoffs `q1Sub` and `q2Sub`.
-/
theorem paper_theorem3_fullFull_fill_capacities_of_cutoff_le
    {Group : Type*} (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    {groupA groupB : Group} {populationShare : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff : Group → ℝ}
    (hcapacity1 :
      capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q1Sub)
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q2Sub)
    (hshareA : 0 ≤ populationShare groupA)
    (hshareB : 0 ≤ populationShare groupB)
    (hcut1A : fullFullCutoff groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff groupB ≤ q1Sub)
    (hcut2A : fullFullCutoff groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff groupB ≤ q2Sub) :
    (capacity1 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw groupA) (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw groupB) (fullFullCutoff groupB)) ∧
      (capacity2 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw groupA) (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw groupB) (fullFullCutoff groupB)) := by
  constructor
  · exact
      paper_theorem3_fullFull_fill_capacity_of_cutoff_le
        api subEstimateLaw hcapacity1 hshareA hshareB hcut1A hcut1B
  · exact
      paper_theorem3_fullFull_fill_capacity_of_cutoff_le
        api subEstimateLaw hcapacity2 hshareA hshareB hcut2A hcut2B

/--
Apply any Theorem 3 endpoint whose only remaining full/full capacity-fill
requirements are the two fill inequalities, deriving those inequalities from
the paper's cutoff-order assumptions.
-/
theorem paper_theorem3_apply_fullFull_fill_of_cutoff_order
    {Group : Type*} (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    {groupA groupB : Group} {populationShare : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff : Group → ℝ} {Result : Prop}
    (hcapacity1 :
      capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q1Sub)
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q2Sub)
    (hshareA : 0 ≤ populationShare groupA)
    (hshareB : 0 ≤ populationShare groupB)
    (hcut1A : fullFullCutoff groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff groupB ≤ q1Sub)
    (hcut2A : fullFullCutoff groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff groupB ≤ q2Sub)
    (hendpoint :
      (capacity1 ≤
          populationShare groupA *
              glm20StrategicSubEstimateMassAbove api
                (subEstimateLaw groupA) (fullFullCutoff groupA) +
            populationShare groupB *
              glm20StrategicSubEstimateMassAbove api
                (subEstimateLaw groupB) (fullFullCutoff groupB)) →
        (capacity2 ≤
          populationShare groupA *
              glm20StrategicSubEstimateMassAbove api
                (subEstimateLaw groupA) (fullFullCutoff groupA) +
            populationShare groupB *
              glm20StrategicSubEstimateMassAbove api
                (subEstimateLaw groupB) (fullFullCutoff groupB)) →
        Result) :
    Result := by
  rcases
    paper_theorem3_fullFull_fill_capacities_of_cutoff_le
      api subEstimateLaw hcapacity1 hcapacity2 hshareA hshareB hcut1A
      hcut1B hcut2A hcut2B with
    ⟨hfill1, hfill2⟩
  exact hendpoint hfill1 hfill2

/--
Positive-share version of
`paper_theorem3_fullFull_fill_capacities_of_cutoff_le`, matching the
share hypotheses used by the main Theorem 3 routes.
-/
theorem paper_theorem3_fullFull_fill_capacities_of_cutoff_le_of_pos
    {Group : Type*} (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    {groupA groupB : Group} {populationShare : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff : Group → ℝ}
    (hcapacity1 :
      capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q1Sub)
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q2Sub)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hcut1A : fullFullCutoff groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff groupB ≤ q1Sub)
    (hcut2A : fullFullCutoff groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff groupB ≤ q2Sub) :
    (capacity1 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw groupA) (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw groupB) (fullFullCutoff groupB)) ∧
      (capacity2 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw groupA) (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw groupB) (fullFullCutoff groupB)) :=
  paper_theorem3_fullFull_fill_capacities_of_cutoff_le
    api subEstimateLaw hcapacity1 hcapacity2 (le_of_lt hshareA)
    (le_of_lt hshareB) hcut1A hcut1B hcut2A hcut2B

/--
Positive-share version of
`paper_theorem3_apply_fullFull_fill_of_cutoff_order`.
-/
theorem paper_theorem3_apply_fullFull_fill_of_cutoff_order_of_pos
    {Group : Type*} (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    {groupA groupB : Group} {populationShare : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff : Group → ℝ} {Result : Prop}
    (hcapacity1 :
      capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q1Sub)
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q2Sub)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hcut1A : fullFullCutoff groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff groupB ≤ q1Sub)
    (hcut2A : fullFullCutoff groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff groupB ≤ q2Sub)
    (hendpoint :
      (capacity1 ≤
          populationShare groupA *
              glm20StrategicSubEstimateMassAbove api
                (subEstimateLaw groupA) (fullFullCutoff groupA) +
            populationShare groupB *
              glm20StrategicSubEstimateMassAbove api
                (subEstimateLaw groupB) (fullFullCutoff groupB)) →
        (capacity2 ≤
          populationShare groupA *
              glm20StrategicSubEstimateMassAbove api
                (subEstimateLaw groupA) (fullFullCutoff groupA) +
            populationShare groupB *
              glm20StrategicSubEstimateMassAbove api
                (subEstimateLaw groupB) (fullFullCutoff groupB)) →
        Result) :
    Result :=
  paper_theorem3_apply_fullFull_fill_of_cutoff_order
    api subEstimateLaw hcapacity1 hcapacity2 (le_of_lt hshareA)
    (le_of_lt hshareB) hcut1A hcut1B hcut2A hcut2B hendpoint

end

end GLM20DroppingStandardizedTesting
