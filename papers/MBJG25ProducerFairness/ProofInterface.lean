import MBJG25ProducerFairness.PaperInterface

/-!
# Proof Interface: Bayesian Rating Fairness

This file keeps proof-facing aliases and library-link checks out of the
human-review `PaperInterface.lean` surface.
-/

namespace MBJG25ProducerFairness

theorem paper_posterior_mean_eq (alpha beta eta t q_v : ℝ) :
    paper_posterior_mean alpha beta eta t q_v =
      EconCSLib.Statistics.priorWeightedPosteriorMean alpha beta eta t q_v := by
  rfl

theorem paper_bias_eq (alpha beta eta t q_v : ℝ) :
    paper_bias alpha beta eta t q_v =
      EconCSLib.Statistics.priorWeightedBias alpha beta eta t q_v := by
  rfl

theorem paper_variance_eq (alpha beta eta t q_v : ℝ) :
    paper_variance alpha beta eta t q_v =
      EconCSLib.Statistics.priorWeightedVariance alpha beta eta t q_v := by
  rfl

theorem paper_squared_bias_eq (alpha beta eta t q_v : ℝ) :
    paper_squared_bias alpha beta eta t q_v =
      EconCSLib.Statistics.priorWeightedSquaredBias alpha beta eta t q_v := by
  rfl

abbrev JensenConvex := EconCSLib.Statistics.JensenConvex
abbrev JensenConcave := EconCSLib.Statistics.JensenConcave
abbrev GlobalMinAt := EconCSLib.Statistics.GlobalMinAt
abbrev GlobalMaxAt := EconCSLib.Statistics.GlobalMaxAt

end MBJG25ProducerFairness
