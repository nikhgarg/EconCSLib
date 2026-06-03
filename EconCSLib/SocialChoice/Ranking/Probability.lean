import EconCSLib.Foundations.Probability.MeasureInequalities
import EconCSLib.SocialChoice.Ranking.Basic

/-!
# Probability Laws on Rankings

Reusable bridges between measure-theoretic random rankings and finite PMF laws
on ranking spaces.

## Main declarations

- `rankingPMFOfMeasure`
- `rankingPMFOfMeasure_eventProb`
- `bestRemainingAfterProb_rankingPMFOfMeasure`
- `firstChoiceProb`
- `firstChoiceProb_rankingPMFOfMeasure`
-/

namespace EconCSLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- Rankings carry the discrete measurable structure by default. -/
instance instMeasurableSpaceRanking (n : ℕ) : MeasurableSpace (Ranking n) := ⊤

/-- Probability that a ranking law places candidate `c` first. -/
def firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  EconCSLib.pmfProb μ (fun π => c = firstChoice π)

/--
The ranking PMF induced by pushing a probability measure through a ranking map.
-/
def rankingPMFOfMeasure
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank) : PMF (Ranking n) :=
  @MeasureTheory.Measure.toPMF (Ranking n) _ _ _ (μ.map rank)
    (MeasureTheory.Measure.isProbabilityMeasure_map hrank.aemeasurable)

/--
Event probabilities for an induced ranking PMF are source-measure preimage
masses.
-/
theorem rankingPMFOfMeasure_eventProb
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (p : Ranking n → Prop) [DecidablePred p] :
    EconCSLib.pmfProb (rankingPMFOfMeasure μ rank hrank) p =
      EconCSLib.measureProb μ (fun ω => p (rank ω)) := by
  unfold rankingPMFOfMeasure
  exact EconCSLib.pmfProb_toPMF_map_eq_measureProb
    μ rank hrank p MeasurableSet.of_discrete

/--
Continuous-measure form of the probability that, after removing one candidate,
the best remaining candidate is another fixed candidate.
-/
theorem bestRemainingAfterProb_rankingPMFOfMeasure
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (removed chosen : Candidate n) :
    EconCSLib.pmfProb (rankingPMFOfMeasure μ rank hrank)
        (fun π => bestRemainingAfter π removed = chosen) =
      EconCSLib.measureProb μ
        (fun ω => bestRemainingAfter (rank ω) removed = chosen) := by
  exact rankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => bestRemainingAfter π removed = chosen)

/-- Continuous-measure form of first-choice probability. -/
theorem firstChoiceProb_rankingPMFOfMeasure
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (c : Candidate n) :
    firstChoiceProb (rankingPMFOfMeasure μ rank hrank) c =
      EconCSLib.measureProb μ (fun ω => c = firstChoice (rank ω)) := by
  unfold firstChoiceProb
  exact rankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => c = firstChoice π)

end

end Ranking
end SocialChoice
end EconCSLib
