import EconCSLib
import EconCSLib.Basic
import EconCSLib.Foundations.Graph
import EconCSLib.Foundations.Probability.MDP
import EconCSLib.MechanismDesign.Auctions
import EconCSLib.MechanismDesign.Auctions.MainTheorems
import EconCSLib.Applications.RecommenderSystems.PolicyAveraging
import EconCSLib.Markets.Matching
import EconCSLib.Algorithms.Online
import EconCSLib.SocialChoice.FairDivision
import EconCSLib.Learning.Bandits.ThompsonSampling

open scoped BigOperators

section
  variable {Agent : Type*} [Fintype Agent]
  variable (price : Agent → ℝ)
  variable (values : Agent → ℝ)
  variable [DecidableEq Agent]

  -- Front-facing smoke check: key reusable theorem names are in scope.
  #guard_msgs(drop info) in
  #check EconCSLib.Auction.paper_posted_price_revenue_eq_single_price
  #guard_msgs(drop info) in
  #check EconCSLib.Auction.paper_posted_price_truthful
  #guard_msgs(drop info) in
  #check EconCSLib.measureProb_mono
  #guard_msgs(drop info) in
  #check EconCSLib.measureProb_lt_of_imp_of_residual_ne_zero
  #guard_msgs(drop info) in
  #check EconCSLib.Math.TendsToZero_of_eventually_abs_le_inv
  #guard_msgs(drop info) in
  #check EconCSLib.Math.TendsToZero_of_eventually_abs_le_inv_sqrt

  example : price = price := by
    rfl

  example : values = values := by
    rfl
end

example : True := by
  trivial
