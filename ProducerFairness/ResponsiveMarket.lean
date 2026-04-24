import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import EconCSLean.Statistics.BinaryRating
import EconCSLean.Statistics.FinsetVariance
import DecisionCore.FiniteExpectation

namespace ProducerFairness
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
  EconCSLean.Statistics.finsetVariance S (fun v => selectionRate (selections v) (lifespan v))

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
      EconCSLean.Statistics.priorWeightedBias alpha beta eta (N s) q_v)
    (h_cond_var : ∀ s,
      (posterior_rating s - q_v) ^ 2 -
      (EconCSLean.Statistics.priorWeightedBias alpha beta eta (N s) q_v) ^ 2 =
      EconCSLean.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) :
    DecisionCore.pmfExp state_dist (fun s => (posterior_rating s - q_v) ^ 2) =
      DecisionCore.pmfExp state_dist (fun s =>
        EconCSLean.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v) +
      DecisionCore.pmfExp state_dist (fun s =>
        EconCSLean.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) := by
  have h_eq : ∀ s, (posterior_rating s - q_v) ^ 2 =
      EconCSLean.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v +
      EconCSLean.Statistics.priorWeightedVariance alpha beta eta (N s) q_v := by
    intro s
    have h1 := h_cond_var s
    unfold EconCSLean.Statistics.priorWeightedSquaredBias
    linarith
  simp only [h_eq]
  exact DecisionCore.pmfExp_add state_dist _ _

end Responsive
end ProducerFairness
