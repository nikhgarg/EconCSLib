import Monoculture.Theorem1
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open DecisionCore

namespace Monoculture

/-!
# Random-Utility Noise Inequalities

This file starts the random-utility-model side of the monoculture paper with the
finite real inequalities used by Appendix C.
-/

/--
Paper Definition 4, strict form.

For `a > b` and `c > d`, assigning the larger realized value to the larger true
value is strictly more likely than the crossed assignment.
-/
def StrictlyWellOrderedNoise (f : ℝ → ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
    f (a - c) * f (b - d) > f (a - d) * f (b - c)

/--
Weak version of Definition 4.  This is useful for Laplacian kernels, where the
strict paper inequality can be an equality when the two ordered intervals are
separated on the real line.
-/
def WeaklyWellOrderedNoise (f : ℝ → ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
    f (a - d) * f (b - c) ≤ f (a - c) * f (b - d)

/-- Gaussian density kernel, omitting the positive normalizing constant. -/
noncomputable def gaussianNoiseKernel (κ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-κ * x ^ 2)

/-- Laplacian density kernel, omitting the positive normalizing constant. -/
noncomputable def laplacianNoiseKernel (lam : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-lam * |x|)

theorem gaussianNoiseKernel_pos (κ x : ℝ) :
    0 < gaussianNoiseKernel κ x := by
  unfold gaussianNoiseKernel
  exact Real.exp_pos _

theorem gaussianNoiseKernel_nonneg (κ x : ℝ) :
    0 ≤ gaussianNoiseKernel κ x :=
  le_of_lt (gaussianNoiseKernel_pos κ x)

theorem laplacianNoiseKernel_pos (lam x : ℝ) :
    0 < laplacianNoiseKernel lam x := by
  unfold laplacianNoiseKernel
  exact Real.exp_pos _

theorem laplacianNoiseKernel_nonneg (lam x : ℝ) :
    0 ≤ laplacianNoiseKernel lam x :=
  le_of_lt (laplacianNoiseKernel_pos lam x)

/--
The algebraic core of the Gaussian well-ordering proof:
swapping the larger realized value to the larger true value improves the
negative squared-error exponent by `2κ(a-b)(c-d)`.
-/
theorem gaussian_exponent_cross_lt_ordered
    {κ a b c d : ℝ} (hκ : 0 < κ) (hab : b < a) (hcd : d < c) :
    -κ * (a - d) ^ 2 + -κ * (b - c) ^ 2 <
      -κ * (a - c) ^ 2 + -κ * (b - d) ^ 2 := by
  have hab_pos : 0 < a - b := sub_pos.mpr hab
  have hcd_pos : 0 < c - d := sub_pos.mpr hcd
  have hprod : 0 < 2 * κ * (a - b) * (c - d) := by
    have hκab : 0 < κ * (a - b) := mul_pos hκ hab_pos
    have h2κab : 0 < 2 * (κ * (a - b)) := mul_pos zero_lt_two hκab
    have hmain : 0 < (2 * (κ * (a - b))) * (c - d) := mul_pos h2κab hcd_pos
    simpa [mul_assoc] using hmain
  have hid :
      (-κ * (a - c) ^ 2 + -κ * (b - d) ^ 2) -
          (-κ * (a - d) ^ 2 + -κ * (b - c) ^ 2) =
        2 * κ * (a - b) * (c - d) := by
    ring
  have hdiff :
      0 <
        (-κ * (a - c) ^ 2 + -κ * (b - d) ^ 2) -
          (-κ * (a - d) ^ 2 + -κ * (b - c) ^ 2) := by
    rw [hid]
    exact hprod
  exact sub_pos.mp hdiff

/-- Gaussian kernels satisfy the paper's strict well-ordering condition. -/
theorem gaussianNoiseKernel_strictlyWellOrdered
    {κ : ℝ} (hκ : 0 < κ) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel κ) := by
  intro a b c d hab hcd
  unfold gaussianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_lt_exp.mpr
    (gaussian_exponent_cross_lt_ordered hκ hab hcd)

/-- Four-point rearrangement inequality for absolute distance on the line. -/
theorem abs_ordered_cross_le_ordered
    {a b c d : ℝ} (hab : b ≤ a) (hcd : d ≤ c) :
    |a - c| + |b - d| ≤ |a - d| + |b - c| := by
  cases abs_cases (a - c) <;>
    cases abs_cases (b - d) <;>
    cases abs_cases (a - d) <;>
    cases abs_cases (b - c) <;>
    linarith

/--
Strict four-point rearrangement for absolute distance when the two ordered
intervals overlap (`b < c` and `d < a`).
-/
theorem abs_ordered_cross_lt_ordered_of_overlap
    {a b c d : ℝ} (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    |a - c| + |b - d| < |a - d| + |b - c| := by
  cases abs_cases (a - c) <;>
    cases abs_cases (b - d) <;>
    cases abs_cases (a - d) <;>
    cases abs_cases (b - c) <;>
    linarith

/-- Laplacian kernels satisfy the weak well-ordering inequality. -/
theorem laplacianNoiseKernel_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) := by
  intro a b c d hab hcd
  have habs := abs_ordered_cross_le_ordered
    (a := a) (b := b) (c := c) (d := d) (le_of_lt hab) (le_of_lt hcd)
  unfold laplacianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul :
      (-lam) * (|a - d| + |b - c|) ≤
        (-lam) * (|a - c| + |b - d|) := by
    exact mul_le_mul_of_nonpos_left habs (neg_nonpos.mpr hlam)
  linarith

/--
The paper's strict Definition 4 is not satisfied by the Laplacian kernel as
stated: for separated ordered pairs, both assignments have the same total
absolute deviation.
-/
theorem laplacianNoiseKernel_not_strictlyWellOrdered (lam : ℝ) :
    ¬ StrictlyWellOrderedNoise (laplacianNoiseKernel lam) := by
  intro h
  have hbad := h (a := (10 : ℝ)) (b := 9) (c := 1) (d := 0)
    (by norm_num) (by norm_num)
  have heq :
      laplacianNoiseKernel lam ((10 : ℝ) - 1) *
          laplacianNoiseKernel lam (9 - 0) =
        laplacianNoiseKernel lam ((10 : ℝ) - 0) *
          laplacianNoiseKernel lam (9 - 1) := by
    unfold laplacianNoiseKernel
    norm_num
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hbad
  exact lt_irrefl _ hbad

/--
Laplacian kernels satisfy the strict paper inequality on the overlap region.
This is the pointwise strict case left after the separated-interval equality
case is removed.
-/
theorem laplacianNoiseKernel_strictlyWellOrdered_of_overlap
    {lam a b c d : ℝ} (hlam : 0 < lam)
    (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    laplacianNoiseKernel lam (a - c) * laplacianNoiseKernel lam (b - d) >
      laplacianNoiseKernel lam (a - d) * laplacianNoiseKernel lam (b - c) := by
  have habs := abs_ordered_cross_lt_ordered_of_overlap hab hcd hbc hda
  unfold laplacianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  have hmul :
      (-lam) * (|a - d| + |b - c|) <
      (-lam) * (|a - c| + |b - d|) := by
    exact mul_lt_mul_of_neg_left habs (by linarith)
  linarith

/-! ## Contraction geometry for RUM realizations -/

/--
The paper's contraction map on one coordinate:
`r' = x + t * (r - x)`, where `x` is the candidate's true value and
`0 ≤ t ≤ 1` corresponds to `θH / θA`.
-/
noncomputable def rumContractScore (t x r : ℝ) : ℝ :=
  x + t * (r - x)

theorem rumContractScore_eq_affine (t x r : ℝ) :
    rumContractScore t x r = (1 - t) * x + t * r := by
  unfold rumContractScore
  ring

theorem rumContractScore_sub
    (t xi xj ri rj : ℝ) :
    rumContractScore t xi ri - rumContractScore t xj rj =
      (1 - t) * (xi - xj) + t * (ri - rj) := by
  rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
  ring

/-- Candidate `x₁` is weakly first among three realized scores. -/
def rum3TopFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  s2 ≤ s1 ∧ s3 ≤ s1

/-- Candidate `x₂` strictly beats `x₁` and weakly beats `x₃`. -/
def rum3MiddleBeatsTopByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 < s2 ∧ s3 ≤ s2

/-- Candidate `x₃` is weakly first among three realized scores. -/
def rum3BottomFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 ≤ s3 ∧ s2 ≤ s3

/--
Contraction cannot reverse an already-correct weak order between two candidates.
-/
theorem rumContractScore_preserves_weak_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj ≤ xi) (hr : rj ≤ ri) :
    rumContractScore t xj rj ≤ rumContractScore t xi ri := by
  have hx_nonneg : 0 ≤ xi - xj := sub_nonneg.mpr hx
  have hr_nonneg : 0 ≤ ri - rj := sub_nonneg.mpr hr
  have h1t : 0 ≤ 1 - t := by linarith
  have hdiff :
      0 ≤ rumContractScore t xi ri - rumContractScore t xj rj := by
    rw [rumContractScore_sub]
    nlinarith [mul_nonneg h1t hx_nonneg, mul_nonneg ht0 hr_nonneg]
  linarith

/--
Strict version of the contraction order lemma.  If both true values and realized
scores put candidate `i` above candidate `j`, then contraction keeps `i` strictly
above `j`.
-/
theorem rumContractScore_preserves_strict_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj < xi) (hr : rj < ri) :
    rumContractScore t xj rj < rumContractScore t xi ri := by
  have hx_pos : 0 < xi - xj := sub_pos.mpr hx
  have hr_pos : 0 < ri - rj := sub_pos.mpr hr
  have h1t : 0 ≤ 1 - t := by linarith
  have hdiff_pos :
      0 < rumContractScore t xi ri - rumContractScore t xj rj := by
    rw [rumContractScore_sub]
    by_cases htpos : 0 < t
    · have hterm2 : 0 < t * (ri - rj) := mul_pos htpos hr_pos
      have hterm1 : 0 ≤ (1 - t) * (xi - xj) :=
        mul_nonneg h1t (le_of_lt hx_pos)
      nlinarith
    · have ht_eq : t = 0 := le_antisymm (le_of_not_gt htpos) ht0
      nlinarith
  linarith

/--
Three-candidate top-first preservation: if `x₁` is first before contraction,
it is still first after contraction.
-/
theorem rum3_contract_top_first_of_original_top_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 ≤ x1) (hx13 : x3 ≤ x1)
    (hr12 : r2 ≤ r1) (hr13 : r3 ≤ r1) :
    rumContractScore t x2 r2 ≤ rumContractScore t x1 r1 ∧
      rumContractScore t x3 r3 ≤ rumContractScore t x1 r1 :=
  ⟨rumContractScore_preserves_weak_order ht0 ht1 hx12 hr12,
    rumContractScore_preserves_weak_order ht0 ht1 hx13 hr13⟩

/--
Three-candidate bottom-first reflection: if the lowest-value candidate `x₃` is
first after contraction, then it was already first before contraction.
-/
theorem rum3_contract_bottom_first_imp_original_bottom_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx31 : x3 < x1) (hx32 : x3 < x2)
    (hc31 : rumContractScore t x1 r1 ≤ rumContractScore t x3 r3)
    (hc32 : rumContractScore t x2 r2 ≤ rumContractScore t x3 r3) :
    r1 ≤ r3 ∧ r2 ≤ r3 := by
  constructor
  · by_contra h
    have hr : r3 < r1 := lt_of_not_ge h
    have hc_lt :
        rumContractScore t x3 r3 < rumContractScore t x1 r1 :=
      rumContractScore_preserves_strict_order ht0 ht1 hx31 hr
    linarith
  · by_contra h
    have hr : r3 < r2 := lt_of_not_ge h
    have hc_lt :
        rumContractScore t x3 r3 < rumContractScore t x2 r2 :=
      rumContractScore_preserves_strict_order ht0 ht1 hx32 hr
    linarith

/--
The deterministic `swapi` geometry used in Appendix C / Lemma 3 for `i = 2`.

If the original realization is bottom-first (`r₁,r₂ ≤ r₃`) and contraction
makes the middle candidate strictly beat the top candidate while weakly beating
the bottom candidate, then after swapping the top and middle realization
coordinates, the original realization is still bottom-first and the contracted
realization is top-first.
-/
theorem rum3_swap_middle_transition_geometry
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hr13 : r1 ≤ r3) (hr23 : r2 ≤ r3)
    (hc12 : rumContractScore t x1 r1 < rumContractScore t x2 r2)
    (hc32 : rumContractScore t x3 r3 ≤ rumContractScore t x2 r2) :
    r2 ≤ r3 ∧ r1 ≤ r3 ∧
      rumContractScore t x2 r1 ≤ rumContractScore t x1 r2 ∧
      rumContractScore t x3 r3 ≤ rumContractScore t x1 r2 := by
  have hr12 : r1 < r2 := by
    by_contra hnot
    have hr21 : r2 ≤ r1 := le_of_not_gt hnot
    have hcontract :
        rumContractScore t x2 r2 ≤ rumContractScore t x1 r1 :=
      rumContractScore_preserves_weak_order ht0 ht1 (le_of_lt hx12) hr21
    linarith
  have hswap12 :
      rumContractScore t x2 r1 ≤ rumContractScore t x1 r2 :=
    le_of_lt (rumContractScore_preserves_strict_order ht0 ht1 hx12 hr12)
  have hsameRealization :
      rumContractScore t x2 r2 ≤ rumContractScore t x1 r2 :=
    rumContractScore_preserves_weak_order ht0 ht1 (le_of_lt hx12) le_rfl
  exact ⟨hr23, hr13, hswap12, le_trans hc32 hsameRealization⟩

theorem weaklyWellOrderedNoise_swap_middle_density_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) ≤ f (r2 - x1) * f (r1 - x2) := by
  have h := hf (a := r2) (b := r1) (c := x1) (d := x2) hr12 hx12
  calc
    f (r1 - x1) * f (r2 - x2) =
        f (r2 - x2) * f (r1 - x1) := by ring
    _ ≤ f (r2 - x1) * f (r1 - x2) := h

theorem strictlyWellOrderedNoise_swap_middle_density_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) < f (r2 - x1) * f (r1 - x2) := by
  have h := hf (a := r2) (b := r1) (c := x1) (d := x2) hr12 hx12
  calc
    f (r1 - x1) * f (r2 - x2) =
        f (r2 - x2) * f (r1 - x1) := by ring
    _ < f (r2 - x1) * f (r1 - x2) := h

/--
Pointwise three-coordinate density comparison for swapping the top and middle
coordinates in a wrong `x₁`/`x₂` pairwise realization.
-/
theorem weaklyWellOrderedNoise_swap12_density3_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) := by
  have hpair := weaklyWellOrderedNoise_swap_middle_density_le
    (f := f) hf hx12 hr12
  exact mul_le_mul_of_nonneg_right hpair hctx

/--
Strict three-coordinate density comparison for swapping the top and middle
coordinates in a wrong `x₁`/`x₂` pairwise realization.
-/
theorem strictlyWellOrderedNoise_swap12_density3_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) := by
  have hpair := strictlyWellOrderedNoise_swap_middle_density_lt
    (f := f) hf hx12 hr12
  exact mul_lt_mul_of_pos_right hpair hctx

/--
Pointwise three-coordinate density comparison for swapping the middle and
bottom coordinates in a wrong `x₂`/`x₃` pairwise realization.
-/
theorem weaklyWellOrderedNoise_swap23_density3_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by
  have hpair := weaklyWellOrderedNoise_swap_middle_density_le
    (f := f) hf hx23 hr23
  calc
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) =
        f (r1 - x1) * (f (r2 - x2) * f (r3 - x3)) := by ring
    _ ≤ f (r1 - x1) * (f (r3 - x2) * f (r2 - x3)) := by
        exact mul_le_mul_of_nonneg_left hpair hctx
    _ = f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by ring

/--
Strict three-coordinate density comparison for swapping the middle and bottom
coordinates in a wrong `x₂`/`x₃` pairwise realization.
-/
theorem strictlyWellOrderedNoise_swap23_density3_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by
  have hpair := strictlyWellOrderedNoise_swap_middle_density_lt
    (f := f) hf hx23 hr23
  calc
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) =
        f (r1 - x1) * (f (r2 - x2) * f (r3 - x3)) := by ring
    _ < f (r1 - x1) * (f (r3 - x2) * f (r2 - x3)) := by
        exact mul_lt_mul_of_pos_left hpair hctx
    _ = f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by ring

/--
Mass comparison for a finite sample law whose atoms are represented by the
three-coordinate density product, under a top/middle coordinate swap.
-/
theorem rum3_swap12_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  intro ω hp
  rw [hdens ω, hdens (swap ω), hswap1 ω, hswap2 ω, hswap3 ω]
  exact weaklyWellOrderedNoise_swap12_density3_le
    hf (hctx ω hp) hx12 (hscore ω hp)

/--
Strict mass comparison for a finite sample law represented by the
three-coordinate density product, under a top/middle coordinate swap.
-/
theorem rum3_swap12_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 < f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal := by
  intro ω hp
  rw [hdens ω, hdens (swap ω), hswap1 ω, hswap2 ω, hswap3 ω]
  exact strictlyWellOrderedNoise_swap12_density3_lt
    hf (hctx ω hp) hx12 (hscore ω hp)

/--
Mass comparison for a finite sample law whose atoms are represented by the
three-coordinate density product, under a middle/bottom coordinate swap.
-/
theorem rum3_swap23_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  intro ω hp
  rw [hdens ω, hdens (swap ω), hswap1 ω, hswap2 ω, hswap3 ω]
  exact weaklyWellOrderedNoise_swap23_density3_le
    hf (hctx ω hp) hx23 (hscore ω hp)

/--
Strict mass comparison for a finite sample law represented by the
three-coordinate density product, under a middle/bottom coordinate swap.
-/
theorem rum3_swap23_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 < f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal := by
  intro ω hp
  rw [hdens ω, hdens (swap ω), hswap1 ω, hswap2 ω, hswap3 ω]
  exact strictlyWellOrderedNoise_swap23_density3_lt
    hf (hctx ω hp) hx23 (hscore ω hp)

/-! ## Three-candidate RUM payoff algebra -/

/-- In the three-candidate RUM proof, utility after candidate `x₁` is unavailable. -/
noncomputable def rum3_uMinus1 (ell1 x2 x3 : ℝ) : ℝ :=
  ell1 * x2 + (1 - ell1) * x3

/-- In the three-candidate RUM proof, utility after candidate `x₂` is unavailable. -/
noncomputable def rum3_uMinus2 (ell2 x1 x3 : ℝ) : ℝ :=
  ell2 * x1 + (1 - ell2) * x3

/-- In the three-candidate RUM proof, utility after candidate `x₃` is unavailable. -/
noncomputable def rum3_uMinus3 (ell3 x1 x2 : ℝ) : ℝ :=
  ell3 * x1 + (1 - ell3) * x2

/-- Paper Theorem 6's `λ₁`: after `x₁` is unavailable, human chooses `x₂`. -/
noncomputable def rum3Lambda1 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))

/-- Paper Theorem 6's `λ₂`: after `x₂` is unavailable, human chooses `x₁`. -/
noncomputable def rum3Lambda2 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))

/-- Paper Theorem 6's `λ₃`: after `x₃` is unavailable, human chooses `x₁`. -/
noncomputable def rum3Lambda3 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

theorem rum3Lambda1_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
      1 - rum3Lambda1 μ := by
  classical
  unfold rum3Lambda1
  rw [← pmfProb_compl μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))]
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro π
  by_cases h1 : bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1)
  · simp [h1]
  · have hne0 :
        bestRemainingAfter π (0 : Candidate 1) ≠ (0 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (0 : Candidate 1)
    have h2 : bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (0 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact hne0 (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact h1 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (0 : Candidate 1)).isLt
      omega
    simp [h2]

theorem rum3Lambda3_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
      1 - rum3Lambda3 μ := by
  classical
  unfold rum3Lambda3
  rw [← pmfProb_compl μ
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))]
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro π
  by_cases h0 : bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1)
  · simp [h0]
  · have hne2 :
        bestRemainingAfter π (2 : Candidate 1) ≠ (2 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (2 : Candidate 1)
    have h1 : bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (2 : Candidate 1)).val = 1
      have hval0 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h0 (Fin.ext hv)
      have hval2 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 2 := by
        intro hv
        exact hne2 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (2 : Candidate 1)).isLt
      omega
    simp [h1]

theorem rum3Lambda1_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μ) :
    (1 : ℝ) / 2 < rum3Lambda1 μ := by
  rw [rum3Lambda1_wrong_eq_one_sub μ] at hwrong
  linarith

theorem rum3Lambda3_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μ) :
    (1 : ℝ) / 2 < rum3Lambda3 μ := by
  rw [rum3Lambda3_wrong_eq_one_sub μ] at hwrong
  linarith

/--
Named finite certificate for Appendix C / Theorem 6.

The fields are the exact non-analytic facts used after the paper invokes
monotonicity, Lemma 2, Lemma 3, and the pairwise human-ranking probabilities.
-/
structure RUM3Theorem6Certificate
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    (x1 x2 x3 : ℝ) : Prop where
  value_first : value (0 : Candidate 1) = x1
  value_second : value (1 : Candidate 1) = x2
  value_third : value (2 : Candidate 1) = x3
  value12 : x2 < x1
  value23 : x3 < x2
  /-- Paper: `1/2 < λ₁`. -/
  lambda1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse
  /-- Paper: `λ₁ < 1`. -/
  lambda1_lt_one : rum3Lambda1 μWorse < 1
  /-- Paper: `λ₂ > λ₁`. -/
  lambda12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse
  /-- Paper: `1/2 < λ₃`. -/
  lambda3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse
  /-- Paper monotonicity: `Δp₁ > 0`. -/
  delta_top_pos :
    0 <
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  /-- Paper Lemma 3 for `i = 2`: `Δp₂ ≤ Δp₁`. -/
  delta_middle_le_top :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  /-- Paper Lemma 2: `Δp₃ ≤ 0`. -/
  delta_bottom_nonpos :
    firstChoiceProb μBetter (2 : Candidate 1) -
        firstChoiceProb μWorse (2 : Candidate 1) ≤ 0

/-- The lambda side of the paper's Theorem 6 proof. -/
structure RUM3LambdaCertificate (μWorse : PMF (Ranking 1)) : Prop where
  lambda1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse
  lambda1_lt_one : rum3Lambda1 μWorse < 1
  lambda12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse
  lambda3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse

/-- The first-choice-delta side of the paper's Theorem 6 proof. -/
structure RUM3DeltaCertificate
    (μBetter μWorse : PMF (Ranking 1)) : Prop where
  delta_top_pos :
    0 <
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  delta_middle_le_top :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  delta_bottom_nonpos :
    firstChoiceProb μBetter (2 : Candidate 1) -
        firstChoiceProb μWorse (2 : Candidate 1) ≤ 0

theorem rum3Theorem6Certificate_of_lambda_delta
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda : RUM3LambdaCertificate μWorse)
    (delta : RUM3DeltaCertificate μBetter μWorse) :
    RUM3Theorem6Certificate μBetter μWorse value x1 x2 x3 where
  value_first := hvalue1
  value_second := hvalue2
  value_third := hvalue3
  value12 := hx12
  value23 := hx23
  lambda1_half := lambda.lambda1_half
  lambda1_lt_one := lambda.lambda1_lt_one
  lambda12 := lambda.lambda12
  lambda3_half := lambda.lambda3_half
  delta_top_pos := delta.delta_top_pos
  delta_middle_le_top := delta.delta_middle_le_top
  delta_bottom_nonpos := delta.delta_bottom_nonpos

theorem rum3DeltaCertificate_of_paper_lemmas
    {μBetter μWorse : PMF (Ranking 1)}
    (monotonicity_top :
      firstChoiceProb μWorse (0 : Candidate 1) <
        firstChoiceProb μBetter (0 : Candidate 1))
    (lemma3_middle :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (lemma2_bottom :
      firstChoiceProb μBetter (2 : Candidate 1) ≤
        firstChoiceProb μWorse (2 : Candidate 1)) :
    RUM3DeltaCertificate μBetter μWorse where
  delta_top_pos := by linarith
  delta_middle_le_top := lemma3_middle
  delta_bottom_nonpos := by linarith

/--
Abstract finite-coupling form of Appendix C / Lemma 2 for the bottom candidate.

The continuous paper proof constructs such a coupling by contraction.  This
lemma isolates the order-theoretic probability step: if every coupled realization
where the better/more accurate ranking puts `x₃` first also has the worse/human
ranking put `x₃` first, then the better bottom-first probability is no larger.
-/
theorem rum3_lemma2_bottom_of_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter :
      firstChoiceProb μBetter (2 : Candidate 1) =
        pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (better ω)))
    (hworse :
      firstChoiceProb μWorse (2 : Candidate 1) =
        pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (worse ω)))
    (himp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    firstChoiceProb μBetter (2 : Candidate 1) ≤
      firstChoiceProb μWorse (2 : Candidate 1) := by
  rw [hbetter, hworse]
  exact pmfProb_le_of_imp ν
    (fun ω => (2 : Candidate 1) = firstChoice (better ω))
    (fun ω => (2 : Candidate 1) = firstChoice (worse ω))
    himp

theorem rum3_middle_delta_indicator_le_bottom_middle
    (b w : Candidate 1)
    (hnoTopOut : (0 : Candidate 1) = w → (0 : Candidate 1) = b) :
    (if (1 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if (1 : Candidate 1) = w then (1 : ℝ) else 0) ≤
      (if (2 : Candidate 1) = w ∧ (1 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if False then (1 : ℝ) else 0) := by
  fin_cases b <;> fin_cases w <;> simp at *

theorem rum3_bottom_top_indicator_le_top_delta
    (b w : Candidate 1)
    (hnoTopOut : (0 : Candidate 1) = w → (0 : Candidate 1) = b) :
    (if (2 : Candidate 1) = w ∧ (0 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if False then (1 : ℝ) else 0) ≤
      (if (0 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if (0 : Candidate 1) = w then (1 : ℝ) else 0) := by
  fin_cases b <;> fin_cases w <;> simp at *

/--
Abstract finite transition-mass form of Appendix C / Lemma 3 for the middle
candidate in the three-candidate case.

The continuous paper proof shows that the human-realization mass moving from
`x₃` to `x₂` under contraction is at most the mass moving from `x₃` to `x₁`,
using the `swapi` bijection and well-ordered noise.  This lemma isolates the
finite probability algebra around that step: if top-first realizations cannot
leave the top under contraction, and `x₃ → x₂` mass is no larger than
`x₃ → x₁` mass, then the paper's Lemma 3 delta inequality for `i = 2` follows.
-/
theorem rum3_lemma3_middle_of_transition_mass
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hbottomMiddle_le_bottomTop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1) := by
  rw [hbetter (1 : Candidate 1), hworse (1 : Candidate 1),
    hbetter (0 : Candidate 1), hworse (0 : Candidate 1)]
  have hmid :
      pmfProb ν (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun _ => False) := by
    refine pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le ν
      (fun ω => (1 : Candidate 1) = firstChoice (better ω))
      (fun ω => (1 : Candidate 1) = firstChoice (worse ω))
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω))
      (fun _ => False) ?_
    intro ω
    exact rum3_middle_delta_indicator_le_bottom_middle
      (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)
  have htop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun _ => False) ≤
        pmfProb ν (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) := by
    refine pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le ν
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω))
      (fun _ => False)
      (fun ω => (0 : Candidate 1) = firstChoice (better ω))
      (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) ?_
    intro ω
    exact rum3_bottom_top_indicator_le_top_delta
      (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)
  simp only [pmfProb_false, sub_zero] at hmid htop
  linarith

/--
Finite `swapi` change-of-variables skeleton for Appendix C / Lemma 3.

An equivalence `swap` sends each `x₃ → x₂` transition realization into an
`x₃ → x₁` transition realization, and the target atom has at least as much
mass.  Therefore the `x₃ → x₂` transition probability is no larger.
-/
theorem rum3_bottomMiddle_transition_le_bottomTop_of_swap_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ν : PMF Ω) (swap : Ω ≃ Ω)
    (better worse : Ω → Ranking 1)
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω)) ≤
      pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω)) :=
  pmfProb_le_of_equiv_event_mass_le ν swap
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω))
    hmap hmass

/--
Finite coupling form of the top-candidate monotonicity step used in Appendix C /
Theorem 6.

If every coupled realization that is top-first for the worse/human ranking is
also top-first for the better/algorithmic ranking, and some positive-mass
realization is corrected into top-first, then the top-first probability is
strictly larger for the better ranking.
-/
theorem rum3_monotonicity_top_of_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal) :
    firstChoiceProb μWorse (0 : Candidate 1) <
      firstChoiceProb μBetter (0 : Candidate 1) := by
  rw [hworse (0 : Candidate 1), hbetter (0 : Candidate 1)]
  exact pmfProb_lt_of_imp_of_mass ν
    (fun ω => (0 : Candidate 1) = firstChoice (worse ω))
    (fun ω => (0 : Candidate 1) = firstChoice (better ω))
    hnoTopOut ω₀ hbetterTop hworseNotTop hmass

/--
Finite contraction/coupling certificate for the delta side of Appendix C /
Theorem 6.

This packages the finite monotonicity step, Lemma 2 bottom inequality, and
Lemma 3 middle-vs-top inequality into the `RUM3DeltaCertificate` consumed by
the final payoff algebra.  The continuous RUM proof still needs to construct the
coupling and prove the listed event/transition facts from contraction and
well-ordered noise.
-/
theorem rum3DeltaCertificate_of_finite_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbottomMiddle_le_bottomTop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_paper_lemmas
    (rum3_monotonicity_top_of_coupling
      μBetter μWorse ν better worse hbetter hworse hnoTopOut
      hbetterTop hworseNotTop hmass)
    (rum3_lemma3_middle_of_transition_mass
      μBetter μWorse ν better worse hbetter hworse hnoTopOut
      hbottomMiddle_le_bottomTop)
    (rum3_lemma2_bottom_of_coupling
      μBetter μWorse ν better worse
      (hbetter (2 : Candidate 1)) (hworse (2 : Candidate 1)) hbottomImp)

/--
Delta certificate where the Lemma 3 transition-mass inequality is supplied by a
finite `swapi` equivalence with pointwise mass dominance.
-/
theorem rum3DeltaCertificate_of_finite_contraction_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_finite_contraction_facts
    μBetter μWorse ν better worse hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmassTop hbottomImp
    (rum3_bottomMiddle_transition_le_bottomTop_of_swap_equiv
      ν swap better worse hmap hmassSwap)

/--
Delta certificate from finite score-level contraction and `swapi` facts.

This bridge derives the ranking-level event implications used by Lemmas 2 and 3
from deterministic score geometry.  The remaining measure-theoretic work is only
the marginal identification and the mass comparison for the finite/discretized
`swapi` map.
-/
theorem rum3DeltaCertificate_of_finite_score_contraction_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (t x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ Ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    RUM3DeltaCertificate μBetter μWorse := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω) := by
    intro ω hwTop
    rcases hworseTop_scores_of_first ω hwTop with ⟨hr21, hr31⟩
    exact hbetterTop_of_scores ω
      (rum3_contract_top_first_of_original_top_first
        ht0 ht1 (le_of_lt hx12) (le_of_lt hx13) hr21 hr31)
  have hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω) := by
    intro ω hbBetter
    rcases hbetterBottom_scores_of_first ω hbBetter with ⟨hc13, hc23⟩
    exact hworseBottom_of_scores ω
      (rum3_contract_bottom_first_imp_original_bottom_first
        ht0 ht1 hx13 hx23 hc13 hc23)
  have hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)) := by
    intro ω htransition
    rcases hworseBottom_scores_of_first ω htransition.1 with ⟨hr13, hr23⟩
    rcases hbetterMiddle_scores_of_first ω htransition.2 with ⟨hc12, hc32⟩
    rcases rum3_swap_middle_transition_geometry
        ht0 ht1 hx12 hr13 hr23 hc12 hc32 with
      ⟨hr23_swap, hr13_swap, hc21_swap, hc31_swap⟩
    constructor
    · apply hworseBottom_of_scores
      unfold rum3BottomFirstByScores
      constructor
      · rw [hswap1, hswap3]
        exact hr23_swap
      · rw [hswap2, hswap3]
        exact hr13_swap
    · apply hbetterTop_of_scores
      unfold rum3TopFirstByScores
      constructor
      · rw [hswap2, hswap1]
        exact hc21_swap
      · rw [hswap3, hswap1]
        exact hc31_swap
  exact rum3DeltaCertificate_of_finite_contraction_swap_facts
    μBetter μWorse ν better worse swap hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmassTop hbottomImp hmap hmassSwap

theorem rum3LambdaCertificate_of_pairwise_facts
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_correct : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (h23_not_sure : rum3Lambda1 μWorse < 1)
    (h12_correct : (1 : ℝ) / 2 < rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse where
  lambda1_half := h23_correct
  lambda1_lt_one := h23_not_sure
  lambda12 := h13_gt_23
  lambda3_half := h12_correct

theorem rum3Lambda1_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda1 μ ≤ 1 := by
  exact pmfProb_le_one μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))

theorem rum3Lambda2_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda2 μ ≤ 1 := by
  exact pmfProb_le_one μ
    (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))

theorem rum3Lambda3_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda3 μ ≤ 1 := by
  exact pmfProb_le_one μ
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

theorem rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
    (μ : PMF (Ranking 1)) (π₀ : Ranking 1)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μ π₀).toReal) :
    rum3Lambda1 μ < 1 := by
  unfold rum3Lambda1
  refine pmfProb_lt_one_of_mass_not μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    π₀ ?hnot hmass
  intro h
  have : (2 : Candidate 1) = (1 : Candidate 1) := by
    rw [← hchoose, h]
  have hval : (2 : ℕ) = 1 := by
    simpa using congrArg Fin.val this
  norm_num at hval

theorem rum3_bestRemainingAfter_swap02_remove0 :
    bestRemainingAfter
        (Equiv.swap (0 : Candidate 1) (2 : Candidate 1))
        (0 : Candidate 1) = (2 : Candidate 1) := by
  simp [bestRemainingAfter, firstChoice]

theorem rum3Lambda1_lt_one_of_full_support
    (μ : PMF (Ranking 1))
    (hfull : ∀ π : Ranking 1, 0 < (μ π).toReal) :
    rum3Lambda1 μ < 1 :=
  rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
    μ (Equiv.swap (0 : Candidate 1) (2 : Candidate 1))
    rum3_bestRemainingAfter_swap02_remove0
    (hfull (Equiv.swap (0 : Candidate 1) (2 : Candidate 1)))

theorem rum3LambdaCertificate_of_pairwise_facts_and_support
    {μWorse : PMF (Ranking 1)} {π₀ : Ranking 1}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_correct : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_correct : (1 : ℝ) / 2 < rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts
    h13_gt_23 h23_correct
    (rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
      μWorse π₀ hchoose hmass)
    h12_correct

theorem rum3LambdaCertificate_of_pairwise_wrong_facts_and_support
    {μWorse : PMF (Ranking 1)} {π₀ : Ranking 1}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts_and_support
    h13_gt_23
    (rum3Lambda1_half_of_wrong_lt_correct h23_wrong_lt_correct)
    hchoose hmass
    (rum3Lambda3_half_of_wrong_lt_correct h12_wrong_lt_correct)

theorem rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (h12_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts
    h13_gt_23
    (rum3Lambda1_half_of_wrong_lt_correct h23_wrong_lt_correct)
    (rum3Lambda1_lt_one_of_full_support μWorse hfull)
    (rum3Lambda3_half_of_wrong_lt_correct h12_wrong_lt_correct)

/--
Finite paired-density skeleton for the `x₂` versus `x₃` lambda comparison.

If a finite equivalence sends each realization choosing `x₃` after `x₁` is
removed to one choosing `x₂`, never decreases mass on that wrong-choice event,
and strictly increases mass for one such realization, then the wrong-choice
probability is strictly smaller than `λ₁`.
-/
theorem rum3Lambda1_wrong_lt_correct_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hwrong : bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 μ := by
  unfold rum3Lambda1
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1))
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Finite paired-density skeleton for the `x₁` versus `x₂` lambda comparison.

If a finite equivalence sends each realization choosing `x₂` after `x₃` is
removed to one choosing `x₁`, never decreases mass on that wrong-choice event,
and strictly increases mass for one such realization, then the wrong-choice
probability is strictly smaller than `λ₃`.
-/
theorem rum3Lambda3_wrong_lt_correct_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hwrong : bestRemainingAfter π₀ (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 μ := by
  unfold rum3Lambda3
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1))
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Finite paired-density skeleton for the `λ₁ < λ₂` gap in Theorem 6.

If a finite equivalence sends each realization where `x₂` beats `x₃` after
`x₁` is removed to one where `x₁` beats `x₃` after `x₂` is removed, never
decreases mass on the source event, and strictly increases mass for one such
realization, then `λ₁ < λ₂`.
-/
theorem rum3Lambda1_lt_lambda2_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hsource : bestRemainingAfter π₀ (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ := by
  unfold rum3Lambda1 rum3Lambda2
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hsource hstrict

/--
Sample-space version of the `x₂` versus `x₃` lambda comparison.

The strict change-of-variables argument runs on a finite realization space `Ω`;
the two marginal-identification equalities connect it back to the ranking law.
-/
theorem rum3Lambda1_wrong_lt_correct_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hwrongμ :
      pmfProb μ
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hcorrectμ :
      rum3Lambda1 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hwrong : bestRemainingAfter (rank ω₀) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 μ := by
  rw [hwrongμ, hcorrectμ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Sample-space version of the `x₁` versus `x₂` lambda comparison.
-/
theorem rum3Lambda3_wrong_lt_correct_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hwrongμ :
      pmfProb μ
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (hcorrectμ :
      rum3Lambda3 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hwrong : bestRemainingAfter (rank ω₀) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 μ := by
  rw [hwrongμ, hcorrectμ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Sample-space version of the `λ₁ < λ₂` gap comparison.
-/
theorem rum3Lambda1_lt_lambda2_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hlambda1μ :
      rum3Lambda1 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hsource : bestRemainingAfter (rank ω₀) (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ := by
  rw [hlambda1μ, hlambda2μ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hsource hstrict

/--
Score-level event map for the `x₂` versus `x₃` lambda swap.

If choosing `x₃` after removing `x₁` implies the `x₃` score strictly beats the
`x₂` score, and a weak `x₂` score lead implies choosing `x₂`, then swapping the
two scores maps the wrong event into the correct event.
-/
theorem rum3Lambda1_wrong_to_correct_map_of_score_swap23
    {Ω : Type*} (rank : Ω → Ranking 1) (s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        s2 ω < s3 ω)
    (hcorrect_of_scores : ∀ ω,
      s3 ω ≤ s2 ω →
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap2 : ∀ ω, s2 (swap ω) = s3 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s2 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
          (1 : Candidate 1) := by
  intro ω hwrong
  apply hcorrect_of_scores
  rw [hswap2, hswap3]
  exact le_of_lt (hwrong_scores ω hwrong)

/--
Score-level event map for the `x₁` versus `x₂` lambda swap.
-/
theorem rum3Lambda3_wrong_to_correct_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1) (s1 s2 : Ω → ℝ) (swap : Ω → Ω)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        s1 ω < s2 ω)
    (hcorrect_of_scores : ∀ ω,
      s2 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap2 : ∀ ω, s2 (swap ω) = s1 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (2 : Candidate 1) =
          (0 : Candidate 1) := by
  intro ω hwrong
  apply hcorrect_of_scores
  rw [hswap1, hswap2]
  exact le_of_lt (hwrong_scores ω hwrong)

/--
Lambda certificate from finite paired-density swap facts.

This packages the two strict pairwise comparisons in the form produced by a
finite change-of-variables argument, while keeping the separate support witness
needed for `λ₁ < 1`.
-/
theorem rum3LambdaCertificate_of_pairwise_swap_facts_and_support
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassSupport : 0 < (μWorse πsupport).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_support
    h13_gt_23
    (rum3Lambda1_wrong_lt_correct_of_equiv
      μWorse swap23 hmap23 hmass23 hwrong23 hstrict23)
    hchooseSupport hmassSupport
    (rum3Lambda3_wrong_lt_correct_of_equiv
      μWorse swap12 hmap12 hmass12 hwrong12 hstrict12)

/--
Lambda certificate from finite paired-density swap facts, including the
`λ₁ < λ₂` comparison as a swap certificate rather than a raw scalar premise.
-/
theorem rum3LambdaCertificate_of_all_pairwise_swap_facts_and_support
    {μWorse : PMF (Ranking 1)}
    (swap13gap : Ranking 1 ≃ Ranking 1)
    (hmap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap13gap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hsource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (μWorse π13gap).toReal < (μWorse (swap13gap π13gap)).toReal)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassSupport : 0 < (μWorse πsupport).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_swap_facts_and_support
    (rum3Lambda1_lt_lambda2_of_equiv
      μWorse swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap)
    swap23 hmap23 hmass23 hwrong23 hstrict23
    hchooseSupport hmassSupport swap12 hmap12 hmass12 hwrong12 hstrict12

/--
Lambda certificate from finite paired-density swap facts plus full support of
the finite human ranking law.
-/
theorem rum3LambdaCertificate_of_all_pairwise_swap_facts_and_full_support
    {μWorse : PMF (Ranking 1)}
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (swap13gap : Ranking 1 ≃ Ranking 1)
    (hmap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap13gap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hsource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (μWorse π13gap).toReal < (μWorse (swap13gap π13gap)).toReal)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_equiv
      μWorse swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap)
    (rum3Lambda1_wrong_lt_correct_of_equiv
      μWorse swap23 hmap23 hmass23 hwrong23 hstrict23)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_equiv
      μWorse swap12 hmap12 hmass12 hwrong12 hstrict12)

/--
Lambda certificate from finite sample-space swap facts plus full support of the
human ranking law.

This is the finite/discrete analogue closest to the continuous RUM density
argument: the swaps act on realizations, and marginal equalities identify the
realization events with the ranking-law lambda events.
-/
theorem rum3LambdaCertificate_of_sample_swap_facts_and_full_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μWorse : PMF (Ranking 1)}
    (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (hlambda1μ :
      rum3Lambda1 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (swap13gap : Ω ≃ Ω)
    (hmap13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap13gap ω)) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hmass13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap13gap ω)).toReal)
    {ω13gap : Ω}
    (hsource13gap :
      bestRemainingAfter (rank ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (ν ω13gap).toReal < (ν (swap13gap ω13gap)).toReal)
    (swap23 : Ω ≃ Ω)
    (hmap23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hmass23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap23 ω)).toReal)
    {ω23 : Ω}
    (hwrong23 :
      bestRemainingAfter (rank ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (ν ω23).toReal < (ν (swap23 ω23)).toReal)
    (swap12 : Ω ≃ Ω)
    (hmap12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hmass12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap12 ω)).toReal)
    {ω12 : Ω}
    (hwrong12 :
      bestRemainingAfter (rank ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (ν ω12).toReal < (ν (swap12 ω12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_sample_equiv
      μWorse ν rank swap13gap hlambda1μ hlambda2μ
      hmap13gap hmass13gap hsource13gap hstrict13gap)
    (rum3Lambda1_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap23 hwrong23μ hlambda1μ
      hmap23 hmass23 hwrong23 hstrict23)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap12 hwrong12μ hlambda3μ
      hmap12 hmass12 hwrong12 hstrict12)

theorem expectedBestAfterRemoval_rum3_remove0
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (0 : Candidate 1) =
      rum3Lambda1 μ * value (1 : Candidate 1) +
        (1 - rum3Lambda1 μ) * value (2 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda1
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    (fun π => value (bestRemainingAfter π (0 : Candidate 1)))
    (value (1 : Candidate 1)) (value (2 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1)
  · simp [h]
  · have hne0 : bestRemainingAfter π (0 : Candidate 1) ≠ (0 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (0 : Candidate 1)
    have h2 : bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (0 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact hne0 (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact h (Fin.ext hv)
      have hlt := (bestRemainingAfter π (0 : Candidate 1)).isLt
      omega
    simp [h2]

theorem expectedBestAfterRemoval_rum3_remove1
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (1 : Candidate 1) =
      rum3Lambda2 μ * value (0 : Candidate 1) +
        (1 - rum3Lambda2 μ) * value (2 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda2
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
    (fun π => value (bestRemainingAfter π (1 : Candidate 1)))
    (value (0 : Candidate 1)) (value (2 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1)
  · simp [h]
  · have hne1 : bestRemainingAfter π (1 : Candidate 1) ≠ (1 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (1 : Candidate 1)
    have h2 : bestRemainingAfter π (1 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (1 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (1 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (1 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact hne1 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (1 : Candidate 1)).isLt
      omega
    simp [h2]

theorem expectedBestAfterRemoval_rum3_remove2
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (2 : Candidate 1) =
      rum3Lambda3 μ * value (0 : Candidate 1) +
        (1 - rum3Lambda3 μ) * value (1 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda3
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
    (fun π => value (bestRemainingAfter π (2 : Candidate 1)))
    (value (0 : Candidate 1)) (value (1 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1)
  · simp [h]
  · have hne2 : bestRemainingAfter π (2 : Candidate 1) ≠ (2 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (2 : Candidate 1)
    have h1 : bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (2 : Candidate 1)).val = 1
      have hval0 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h (Fin.ext hv)
      have hval2 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 2 := by
        intro hv
        exact hne2 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (2 : Candidate 1)).isLt
      omega
    simp [h1]

theorem rum3_uMinus1_lt_uMinus2
    {x1 x2 x3 ell1 ell2 : ℝ}
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_pos : 0 < ell1) (hell12 : ell1 < ell2) :
    rum3_uMinus1 ell1 x2 x3 < rum3_uMinus2 ell2 x1 x3 := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hx23_pos : 0 < x2 - x3 := sub_pos.mpr hx23
  have hx13_pos : 0 < x1 - x3 := sub_pos.mpr hx13
  have hx_gap : x2 - x3 < x1 - x3 := by linarith
  have hleft : ell1 * (x2 - x3) < ell1 * (x1 - x3) :=
    mul_lt_mul_of_pos_left hx_gap hell1_pos
  have hright : ell1 * (x1 - x3) < ell2 * (x1 - x3) :=
    mul_lt_mul_of_pos_right hell12 hx13_pos
  have hmain : ell1 * (x2 - x3) < ell2 * (x1 - x3) :=
    lt_trans hleft hright
  unfold rum3_uMinus1 rum3_uMinus2
  nlinarith

theorem rum3_uMinus1_lt_x2
    {x2 x3 ell1 : ℝ} (hx23 : x3 < x2) (hell1_lt_one : ell1 < 1) :
    rum3_uMinus1 ell1 x2 x3 < x2 := by
  have hcoef : 0 < 1 - ell1 := by linarith
  have hgap : x3 - x2 < 0 := by linarith
  have hprod : (1 - ell1) * (x3 - x2) < 0 :=
    mul_neg_of_pos_of_neg hcoef hgap
  unfold rum3_uMinus1
  nlinarith

theorem rum3_x2_lt_uMinus3
    {x1 x2 ell3 : ℝ} (hx12 : x2 < x1) (hell3_pos : 0 < ell3) :
    x2 < rum3_uMinus3 ell3 x1 x2 := by
  have hgap : 0 < x1 - x2 := sub_pos.mpr hx12
  have hprod : 0 < ell3 * (x1 - x2) := mul_pos hell3_pos hgap
  unfold rum3_uMinus3
  nlinarith

theorem rum3_uMinus2_le_x1
    {x1 x3 ell2 : ℝ} (hx31 : x3 ≤ x1) (hell2_le_one : ell2 ≤ 1) :
    rum3_uMinus2 ell2 x1 x3 ≤ x1 := by
  have hcoef : 0 ≤ 1 - ell2 := by linarith
  have hgap : x3 - x1 ≤ 0 := by linarith
  have hprod : (1 - ell2) * (x3 - x1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef hgap
  unfold rum3_uMinus2
  nlinarith

theorem x1_add_x2_lt_two_mul_rum3_uMinus3
    {x1 x2 ell3 : ℝ} (hx12 : x2 < x1) (hell3_half : (1 : ℝ) / 2 < ell3) :
    x1 + x2 < 2 * rum3_uMinus3 ell3 x1 x2 := by
  have hcoef : 0 < 2 * ell3 - 1 := by linarith
  have hgap : 0 < x1 - x2 := sub_pos.mpr hx12
  have hprod : 0 < (2 * ell3 - 1) * (x1 - x2) := mul_pos hcoef hgap
  unfold rum3_uMinus3
  nlinarith

/--
The scalar algebra at the end of paper Theorem 6.

Here `dᵢ = Pr[τ₁ = xᵢ] - Pr[π₁ = xᵢ]`, and `uᵢ` is the human expected utility
when candidate `xᵢ` is unavailable.  The hypotheses are the paper's
`Δp₁ > 0`, `Δp₁ ≥ Δp₂`, `Δp₃ ≤ 0`, total-mass identity, and the three utility
comparisons derived in the proof.
-/
theorem rum3_delta_weighted_sum_neg
    {u1 u2 u3 d1 d2 d3 : ℝ}
    (hu12 : u1 < u2) (hu13 : u1 < u3) (hu_sum : u1 + u2 < 2 * u3)
    (hd1_pos : 0 < d1) (hd12 : d2 ≤ d1) (hd3_nonpos : d3 ≤ 0)
    (hd_sum : d1 + d2 + d3 = 0) :
    d1 * u1 + d2 * u2 + d3 * u3 < 0 := by
  by_cases hd2_nonpos : d2 ≤ 0
  · have hsome_neg : d2 < 0 ∨ d3 < 0 := by
      by_contra hnot
      have hd2_nonneg : 0 ≤ d2 := le_of_not_gt (fun h => hnot (Or.inl h))
      have hd3_nonneg : 0 ≤ d3 := le_of_not_gt (fun h => hnot (Or.inr h))
      nlinarith
    cases hsome_neg with
    | inl hd2_neg =>
        have h2 : d2 * u2 < d2 * u1 :=
          mul_lt_mul_of_neg_left hu12 hd2_neg
        have h3 : d3 * u3 ≤ d3 * u1 :=
          mul_le_mul_of_nonpos_left (le_of_lt hu13) hd3_nonpos
        calc
          d1 * u1 + d2 * u2 + d3 * u3
              < d1 * u1 + d2 * u1 + d3 * u1 := by linarith
          _ = (d1 + d2 + d3) * u1 := by ring
          _ = 0 := by rw [hd_sum]; ring
    | inr hd3_neg =>
        have h2 : d2 * u2 ≤ d2 * u1 :=
          mul_le_mul_of_nonpos_left (le_of_lt hu12) hd2_nonpos
        have h3 : d3 * u3 < d3 * u1 :=
          mul_lt_mul_of_neg_left hu13 hd3_neg
        calc
          d1 * u1 + d2 * u2 + d3 * u3
              < d1 * u1 + d2 * u1 + d3 * u1 := by linarith
          _ = (d1 + d2 + d3) * u1 := by ring
          _ = 0 := by rw [hd_sum]; ring
  · have hd2_pos : 0 < d2 := lt_of_not_ge hd2_nonpos
    have hdiff_nonpos : u1 - u3 ≤ 0 := by linarith
    have hfirst :
        d1 * (u1 - u3) ≤ d2 * (u1 - u3) :=
      mul_le_mul_of_nonpos_right hd12 hdiff_nonpos
    have htail : d2 * (u1 + u2 - 2 * u3) < 0 := by
      have hsum_neg : u1 + u2 - 2 * u3 < 0 := by linarith
      exact mul_neg_of_pos_of_neg hd2_pos hsum_neg
    have hbound :
        d1 * u1 + d2 * u2 + d3 * u3 ≤
          d2 * (u1 + u2 - 2 * u3) := by
      have hd3_eq : d3 = -d1 - d2 := by linarith
      calc
        d1 * u1 + d2 * u2 + d3 * u3
            = d1 * (u1 - u3) + d2 * (u2 - u3) := by
                rw [hd3_eq]
                ring
        _ ≤ d2 * (u1 - u3) + d2 * (u2 - u3) := by linarith
        _ = d2 * (u1 + u2 - 2 * u3) := by ring
    exact lt_of_le_of_lt hbound htail

/--
Paper Theorem 6 payoff algebra after substituting the three `u_-i` formulas.

The remaining RUM-specific tasks are to derive the lambda and delta hypotheses
from the continuous random-utility model.  This theorem closes the final
finite-dimensional inequality once those hypotheses are available.
-/
theorem rum3_theorem6_payoff_algebra
    {x1 x2 x3 ell1 ell2 ell3 d1 d2 d3 : ℝ}
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_half : (1 : ℝ) / 2 < ell1) (hell1_lt_one : ell1 < 1)
    (hell12 : ell1 < ell2) (hell2_le_one : ell2 ≤ 1)
    (hell3_half : (1 : ℝ) / 2 < ell3)
    (hd1_pos : 0 < d1) (hd12 : d2 ≤ d1) (hd3_nonpos : d3 ≤ 0)
    (hd_sum : d1 + d2 + d3 = 0) :
    d1 * rum3_uMinus1 ell1 x2 x3 +
        d2 * rum3_uMinus2 ell2 x1 x3 +
        d3 * rum3_uMinus3 ell3 x1 x2 < 0 := by
  have hell1_pos : 0 < ell1 := by nlinarith
  have hell3_pos : 0 < ell3 := by nlinarith
  have hx13_le : x3 ≤ x1 := le_of_lt (lt_trans hx23 hx12)
  have hu12 :
      rum3_uMinus1 ell1 x2 x3 < rum3_uMinus2 ell2 x1 x3 :=
    rum3_uMinus1_lt_uMinus2 hx12 hx23 hell1_pos hell12
  have hu1_x2 : rum3_uMinus1 ell1 x2 x3 < x2 :=
    rum3_uMinus1_lt_x2 hx23 hell1_lt_one
  have hx2_u3 : x2 < rum3_uMinus3 ell3 x1 x2 :=
    rum3_x2_lt_uMinus3 hx12 hell3_pos
  have hu13 :
      rum3_uMinus1 ell1 x2 x3 < rum3_uMinus3 ell3 x1 x2 :=
    lt_trans hu1_x2 hx2_u3
  have hu2_x1 : rum3_uMinus2 ell2 x1 x3 ≤ x1 :=
    rum3_uMinus2_le_x1 hx13_le hell2_le_one
  have hxsum_u3 : x1 + x2 < 2 * rum3_uMinus3 ell3 x1 x2 :=
    x1_add_x2_lt_two_mul_rum3_uMinus3 hx12 hell3_half
  have hu_sum :
      rum3_uMinus1 ell1 x2 x3 + rum3_uMinus2 ell2 x1 x3 <
        2 * rum3_uMinus3 ell3 x1 x2 := by
    nlinarith
  exact rum3_delta_weighted_sum_neg
    hu12 hu13 hu_sum hd1_pos hd12 hd3_nonpos hd_sum

/--
Three-candidate RUM weaker-competition bridge in model notation.

This turns the scalar Theorem 6 algebra into the utility predicate from
Definition 3.  The first-choice delta hypotheses are stated directly in terms of
the better and worse first-mover ranking laws; their total-mass identity is
derived from `sum_firstChoiceProb_eq_one`.
-/
theorem rum3_prefersWeakerCompetition_of_payoff_algebra
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 ell1 ell2 ell3 : ℝ}
    (hbest1 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (0 : Candidate 1) =
        rum3_uMinus1 ell1 x2 x3)
    (hbest2 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (1 : Candidate 1) =
        rum3_uMinus2 ell2 x1 x3)
    (hbest3 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (2 : Candidate 1) =
        rum3_uMinus3 ell3 x1 x2)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_half : (1 : ℝ) / 2 < ell1) (hell1_lt_one : ell1 < 1)
    (hell12 : ell1 < ell2) (hell2_le_one : ell2 ≤ 1)
    (hell3_half : (1 : ℝ) / 2 < ell3)
    (hd1_pos :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd12 :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd3_nonpos :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    Model.PrefersWeakerCompetition μBetter μWorse value := by
  classical
  let d1 : ℝ :=
    firstChoiceProb μBetter (0 : Candidate 1) -
      firstChoiceProb μWorse (0 : Candidate 1)
  let d2 : ℝ :=
    firstChoiceProb μBetter (1 : Candidate 1) -
      firstChoiceProb μWorse (1 : Candidate 1)
  let d3 : ℝ :=
    firstChoiceProb μBetter (2 : Candidate 1) -
      firstChoiceProb μWorse (2 : Candidate 1)
  have hbetter_sum :
      firstChoiceProb μBetter (0 : Candidate 1) +
          firstChoiceProb μBetter (1 : Candidate 1) +
          firstChoiceProb μBetter (2 : Candidate 1) = 1 := by
    simpa [Candidate, Fin.sum_univ_three] using
      (sum_firstChoiceProb_eq_one (μ := μBetter) (n := 1))
  have hworse_sum :
      firstChoiceProb μWorse (0 : Candidate 1) +
          firstChoiceProb μWorse (1 : Candidate 1) +
          firstChoiceProb μWorse (2 : Candidate 1) = 1 := by
    simpa [Candidate, Fin.sum_univ_three] using
      (sum_firstChoiceProb_eq_one (μ := μWorse) (n := 1))
  have hd_sum : d1 + d2 + d3 = 0 := by
    dsimp [d1, d2, d3]
    nlinarith
  have hneg :
      d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2 < 0 := by
    exact rum3_theorem6_payoff_algebra
      hx12 hx23 hell1_half hell1_lt_one hell12 hell2_le_one hell3_half
      (by simpa [d1] using hd1_pos)
      (by simpa [d1, d2] using hd12)
      (by simpa [d3] using hd3_nonpos)
      hd_sum
  have hdiff :
      expectedSecondMoverIndependent μWorse μBetter value -
          expectedSecondMoverIndependent μWorse μWorse value =
        d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2 := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_sub_eq_sum_firstChoiceProb_sub_mul_bestAfterRemoval]
    change
      (∑ c : Fin 3,
        (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
          AccuracyFamily.expectedBestAfterRemoval μWorse value c) =
        d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2
    rw [Fin.sum_univ_three]
    simp [d1, d2, d3, hbest1, hbest2, hbest3]
  unfold Model.PrefersWeakerCompetition
  have hsub : expectedSecondMoverIndependent μWorse μBetter value -
      expectedSecondMoverIndependent μWorse μWorse value < 0 := by
    rw [hdiff]
    exact hneg
  linarith

/--
Three-candidate RUM weaker-competition bridge with the `u_-i` formulas derived
from the human ranking law itself.

The remaining assumptions are exactly the upstream RUM probability facts from
the paper: value ordering, `λ₁ > 1/2`, `λ₁ < 1`, `λ₂ > λ₁`, `λ₃ > 1/2`, and
the first-choice delta inequalities.
-/
theorem rum3_prefersWeakerCompetition
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hlam1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (hlam1_lt_one : rum3Lambda1 μWorse < 1)
    (hlam12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (hlam3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse)
    (hd1_pos :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd12 :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd3_nonpos :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    Model.PrefersWeakerCompetition μBetter μWorse value := by
  have hbest1 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (0 : Candidate 1) =
        rum3_uMinus1 (rum3Lambda1 μWorse) x2 x3 := by
    rw [expectedBestAfterRemoval_rum3_remove0]
    simp [rum3_uMinus1, hvalue2, hvalue3]
  have hbest2 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (1 : Candidate 1) =
        rum3_uMinus2 (rum3Lambda2 μWorse) x1 x3 := by
    rw [expectedBestAfterRemoval_rum3_remove1]
    simp [rum3_uMinus2, hvalue1, hvalue3]
  have hbest3 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (2 : Candidate 1) =
        rum3_uMinus3 (rum3Lambda3 μWorse) x1 x2 := by
    rw [expectedBestAfterRemoval_rum3_remove2]
    simp [rum3_uMinus3, hvalue1, hvalue2]
  exact rum3_prefersWeakerCompetition_of_payoff_algebra
    μBetter μWorse value
    hbest1 hbest2 hbest3
    hx12 hx23 hlam1_half hlam1_lt_one hlam12
    (pmfProb_le_one μWorse
      (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1)))
    hlam3_half hd1_pos hd12 hd3_nonpos

/-- Appendix C / Theorem 6 from its named finite certificate. -/
theorem rum3_prefersWeakerCompetition_of_certificate
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (cert : RUM3Theorem6Certificate μBetter μWorse value x1 x2 x3) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  rum3_prefersWeakerCompetition
    μBetter μWorse value
    cert.value_first cert.value_second cert.value_third
    cert.value12 cert.value23
    cert.lambda1_half cert.lambda1_lt_one cert.lambda12 cert.lambda3_half
    cert.delta_top_pos cert.delta_middle_le_top cert.delta_bottom_nonpos

end Monoculture
