import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import EconCSLib.Foundations.Econometrics.RatingModels.BinaryRating
import EconCSLib.Foundations.Probability.FinsetVariance
import EconCSLib.Foundations.Probability.FiniteExpectation

namespace MBJG25ProducerFairness
namespace Responsive

/--
Selection Rate (SR) for a product $v$.
Defined in the responsive market section as the expected number of times selected
divided by its lifespan. We parameterize this directly.
-/
noncomputable def selectionRate (selections : ℝ) (lifespan : ℝ) : ℝ :=
  selections / lifespan

/--
Individual Producer Unfairness.
Defined as the standard deviation in Selection Rate (SR) among producers with
the same true quality `q`. We formalize the variance here for algebraic stability.
-/
noncomputable def producerUnfairnessVariance
    {V : Type*} [Fintype V] [DecidableEq V]
    (selections : V → ℝ)
    (lifespan : V → ℝ)
    (q_v : V → ℝ)
    (q : ℝ) : ℝ :=
  let S := Finset.univ.filter (fun v => q_v v = q)
  EconCSLib.Statistics.finsetVariance S (fun v => selectionRate (selections v) (lifespan v))

/--
Individual Producer Unfairness.
The standard deviation counterpart.
-/
noncomputable def producerUnfairness
    {V : Type*} [Fintype V] [DecidableEq V]
    (selections : V → ℝ)
    (lifespan : V → ℝ)
    (q_v : V → ℝ)
    (q : ℝ) : ℝ :=
  Real.sqrt (producerUnfairnessVariance selections lifespan q_v q)

/--
Mean Squared Error (MSE) decomposition in the responsive setting.
As shown in Appendix C, when the number of reviews $N$ is a random variable,
the expected MSE conditional on true quality $q_v$ decomposes into the expected
squared bias and the expected variance over the random variable $N$.
-/
theorem paper_responsive_mse_decomposition
    {α : Type*} [Fintype α] [DecidableEq α]
    {alpha beta eta q_v : ℝ}
    (state_dist : PMF α)
    (N : α → ℝ)
    (posterior_rating : α → ℝ)
    (h_cond_mean : ∀ s,
      posterior_rating s - q_v =
      EconCSLib.Statistics.priorWeightedBias alpha beta eta (N s) q_v)
    (h_cond_var : ∀ s,
      (posterior_rating s - q_v) ^ 2 -
      (EconCSLib.Statistics.priorWeightedBias alpha beta eta (N s) q_v) ^ 2 =
      EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) :
    EconCSLib.pmfExp state_dist (fun s => (posterior_rating s - q_v) ^ 2) =
      EconCSLib.pmfExp state_dist (fun s =>
        EconCSLib.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v) +
      EconCSLib.pmfExp state_dist (fun s =>
        EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) := by
  have h_eq : ∀ s, (posterior_rating s - q_v) ^ 2 =
      EconCSLib.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v +
      EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v := by
    intro s
    have h1 := h_cond_var s
    unfold EconCSLib.Statistics.priorWeightedSquaredBias
    linarith
  simp only [h_eq]
  exact EconCSLib.pmfExp_add state_dist _ _

end Responsive
end MBJG25ProducerFairness
