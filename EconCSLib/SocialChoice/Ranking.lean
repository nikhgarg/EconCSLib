import EconCSLib.SocialChoice.Ranking.Basic
import EconCSLib.SocialChoice.Ranking.Kendall
import EconCSLib.SocialChoice.Ranking.Probability
import EconCSLib.SocialChoice.Ranking.Mallows
import EconCSLib.SocialChoice.Ranking.Payoff
import EconCSLib.SocialChoice.Ranking.RankPower
import EconCSLib.SocialChoice.Ranking.MallowsRankFactorization
import EconCSLib.SocialChoice.Ranking.Score
import EconCSLib.SocialChoice.Ranking.Sequential
import EconCSLib.SocialChoice.Ranking.SequentialPayoff
import EconCSLib.SocialChoice.Ranking.MallowsSequential

/-!
# Ranking

Aggregate import for finite ranking primitives.

Includes base ranking operations, Kendall distance, probability-law bridges,
Mallows laws and rank-factorization algebra, Mallows best-in-set payoff
decompositions, first-choice payoff decompositions, pure score-induced
three-candidate ranking maps, probability-free sequential choice helpers, and
expected best-feasible-candidate payoffs.
-/
