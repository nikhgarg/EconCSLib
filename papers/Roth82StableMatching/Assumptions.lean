import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

/-!
# Paper Assumptions: Roth 1982 Stable Matching

This file records source/model assumptions used by the paper-facing Roth82
interface. These assumptions are explicit domain conventions or named lemma
conditions from the source paper, not proof certificates.
-/

namespace Roth82StableMatching

/--
The source marriage-problem representation uses balanced one-to-one markets.
This is the equal-size condition needed for complete strict-marriage endpoints.
-/
-- audit-premise: hcard : Fintype.card M = Fintype.card W
abbrev assumption_equal_cardinality {M W : Type*}
    [Fintype M] [Fintype W] : Prop :=
  Fintype.card M = Fintype.card W

/--
Roth's Lemma 1 simple-misrepresentation route assumes the simplified report
strictly ranks the obtained partner first.
-/
-- audit-premise: hfirst : ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar
abbrev assumption_simple_report_ranks_partner_first {W : Type*}
    (simple_report_m : W → ℝ) (wstar : W) : Prop :=
  ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar

end Roth82StableMatching
