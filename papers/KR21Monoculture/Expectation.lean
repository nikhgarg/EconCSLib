import KR21Monoculture.Basic
import EconCSLib.Foundations.Probability.FiniteExpectation
import EconCSLib.SocialChoice.Ranking.Payoff

open EconCSLib

namespace KR21Monoculture

export EconCSLib.SocialChoice.Ranking
  (expectedFirstMoverUtility
    expectedSecondMoverShared
    secondChoiceProb
    expectedSecondMoverShared_eq_sum_secondChoiceProb
    secondMoverUtility
    expectedSecondMoverIndependent
    secondMoverUtility_self
    secondMoverUtility_eq_if
    welfareOrdered
    expectedWelfareOrdered
    welfareOrdered_eq
    welfareOrdered_self)

end KR21Monoculture
