import EconCSLib.SocialChoice.Voting

/-!
# Paper-Facing Theorems: Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the United States

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

## Main declarations

- `partyPAVScore`: source-facing PAV/Thiele score wrapper.
- `pavSeatScore`: source-facing two-party PAV seat-count score.
- `pavSeatMinArgmax`: source-facing leftmost maximizing PAV seat count.
- `stvTwoPartyLowerBounds`: source-facing lower-bound/conservation boundary to
  be discharged from the solid-coalition STV theorem.
- `stvSeatShareBounds`: source-facing STV floor/ceiling consequence.
- `pavSeatInterval`: Lemma C.1 interval characterization for the PAV seat count.
- `pavSeatMarginalConditions`: adjacent PAV marginal optimality conditions from
  the proof of Lemma C.1.
- `pavSeatInterval_seatShareRounded`: reusable arithmetic consequence used by
  Proposition 1.
-/

namespace GGRS26CombattingGerrymanderingRCV

open EconCSLib.SocialChoice.Voting

/-- Source-facing alias for approval ballots used by the Thiele/PAV comparison. -/
abbrev PartyApprovalBallot (Candidate : Type*) := ApprovalBallot Candidate

/-- Source-facing wrapper for natural-valued Thiele committee scores. -/
def partyThieleScore {Candidate Score : Type*} [DecidableEq Candidate] [AddMonoid Score]
    (weight : ℕ → Score) (committee : Finset Candidate)
    (profile : List (PartyApprovalBallot Candidate)) : Score :=
  thieleScore weight committee profile

/-- Source-facing wrapper for proportional approval voting scores. -/
noncomputable def partyPAVScore {Candidate : Type*} [DecidableEq Candidate]
    (committee : Finset Candidate) (profile : List (PartyApprovalBallot Candidate)) : ℝ :=
  pavScore committee profile

@[simp] theorem partyPAVScore_nil {Candidate : Type*} [DecidableEq Candidate]
    (committee : Finset Candidate) :
    partyPAVScore committee ([] : List (PartyApprovalBallot Candidate)) = 0 := rfl

/--
Seat-share rounding target from Proposition 1: a party's seat count is one of
the floor or ceiling of its vote share times the number of seats.
-/
def seatShareRounded (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  roundedSeatShare seatCount partyShare seats

/--
Lemma C.1 interval characterization for the PAV party seat count:
`y_R (M + 1) - 1 <= n_R < y_R (M + 1)`.
-/
def pavSeatInterval (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  EconCSLib.SocialChoice.Voting.pavSeatInterval seatCount partyShare seats

/--
Adjacent PAV marginal optimality conditions used in the proof of Lemma C.1.

These are the source proof's two neighboring-seat inequalities after clearing
positive denominators.
-/
def pavSeatMarginalConditions (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  EconCSLib.SocialChoice.Voting.pavSeatMarginalConditions seatCount partyShare seats

/--
The source proof's adjacent PAV marginal conditions imply the Lemma C.1
interval characterization.
-/
theorem pavSeatInterval_of_marginalConditions {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1) (hseat : seatCount ≤ seats)
    (hmarg : pavSeatMarginalConditions seatCount partyShare seats) :
    pavSeatInterval seatCount partyShare seats := by
  simpa [pavSeatMarginalConditions, pavSeatInterval] using
    (EconCSLib.SocialChoice.Voting.pavSeatInterval_of_marginalConditions
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hseat hmarg)

/--
The Lemma C.1 interval implies the coarser floor/ceiling seat-share target used
in Proposition 1.
-/
theorem pavSeatInterval_seatShareRounded {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hinterval : pavSeatInterval seatCount partyShare seats) :
    seatShareRounded seatCount partyShare seats := by
  simpa [pavSeatInterval, seatShareRounded] using
    (EconCSLib.SocialChoice.Voting.pavSeatInterval_roundedSeatShare
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hinterval)

/--
The source proof's adjacent PAV marginal conditions imply the Proposition 1
floor/ceiling seat-share target for the PAV component.
-/
theorem pavSeatMarginalConditions_seatShareRounded {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1) (hseat : seatCount ≤ seats)
    (hmarg : pavSeatMarginalConditions seatCount partyShare seats) :
    seatShareRounded seatCount partyShare seats :=
  pavSeatInterval_seatShareRounded hpos hle <|
    pavSeatInterval_of_marginalConditions hpos hle hseat hmarg

/--
Source-facing two-party PAV seat-count score from Lemma C.1: the selected party
receives `seatCount` seats and the other party receives `seats - seatCount`.
-/
noncomputable def pavSeatScore (partyShare : ℝ) (seats seatCount : ℕ) : ℝ :=
  partyShare * pavHarmonicSum seatCount +
    (1 - partyShare) * pavHarmonicSum (seats - seatCount)

/--
Source-facing interpretation of the paper's `min arg max` PAV seat-count
selection.
-/
def pavSeatMinArgmax (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  IsMinArgmaxOn (pavSeatScore partyShare seats) seatCount seats

/--
The paper's leftmost PAV maximizing seat count satisfies the Lemma C.1 interval.
-/
theorem pavSeatMinArgmax_seatInterval {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hmin : pavSeatMinArgmax seatCount partyShare seats) :
    pavSeatInterval seatCount partyShare seats := by
  simpa [pavSeatMinArgmax, pavSeatScore, pavSeatInterval] using
    (EconCSLib.SocialChoice.Voting.pavSeatInterval_of_isMinArgmaxOn
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hmin)

/--
The paper's leftmost PAV maximizing seat count has the floor/ceiling
seat-share property used in Proposition 1.
-/
theorem pavSeatMinArgmax_seatShareRounded {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hmin : pavSeatMinArgmax seatCount partyShare seats) :
    seatShareRounded seatCount partyShare seats := by
  simpa [pavSeatMinArgmax, pavSeatScore, seatShareRounded] using
    (roundedSeatShare_of_isMinArgmaxOn
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hmin)

/--
Source-facing STV bridge target from Proposition 1: the STV party seat count
lies between floor and ceiling of vote share times seats.
-/
def stvSeatShareBounds (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  ⌊partyShare * (seats : ℝ)⌋₊ ≤ seatCount ∧
    seatCount ≤ ⌈partyShare * (seats : ℝ)⌉₊

/--
Source-facing two-party STV lower-bound/conservation boundary from the proof of
Proposition 1.

The focal party and the other party together fill all seats, and each has at
least the floor of its proportional seat share.
-/
def stvTwoPartyLowerBounds (partySeats otherPartySeats : ℕ) (partyShare : ℝ)
    (seats : ℕ) : Prop :=
  partySeats + otherPartySeats = seats ∧
    ⌊partyShare * (seats : ℝ)⌋₊ ≤ partySeats ∧
    ⌊(1 - partyShare) * (seats : ℝ)⌋₊ ≤ otherPartySeats

/--
Existential packaging of the two-party STV lower-bound boundary when the paper
only names the focal party's STV seat count.
-/
def stvSolidCoalitionLowerBounds (seatCount : ℕ) (partyShare : ℝ)
    (seats : ℕ) : Prop :=
  ∃ otherPartySeats, stvTwoPartyLowerBounds seatCount otherPartySeats partyShare seats

/--
Source-facing quota lower-bound boundary from the STV proof.

Each party has at least the floor of its vote count divided by the Droop quota,
the two parties fill all seats, and the voter-count/domain hypotheses needed for
the Droop quota arithmetic are visible.
-/
def stvTwoPartyQuotaLowerBounds (partySeats otherPartySeats seats voters : ℕ)
    (partyShare : ℝ) : Prop :=
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤ partySeats ∧
    ⌊(1 - partyShare) * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤
      otherPartySeats

/--
Existential packaging of the quota lower-bound boundary when the paper only
names the focal party's STV seat count.
-/
def stvSolidCoalitionQuotaLowerBounds (seatCount : ℕ) (partyShare : ℝ)
    (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartyQuotaLowerBounds seatCount otherPartySeats seats voters partyShare

/--
The source proof's quota-capacity step: the two parties' full Droop-quota
counts fit within the district's `seats` available winners.
-/
theorem stvTwoPartyQuotaFloors_sum_le_seats {seats voters : ℕ} {partyShare : ℝ}
    (hshare_nonneg : 0 ≤ partyShare) (hshare_le : partyShare ≤ 1) :
    ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ +
        ⌊(1 - partyShare) *
          ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤ seats :=
  twoParty_floor_votes_div_STVQuota_sum_le_seats hshare_nonneg hshare_le

/--
There is a filled two-party seat allocation extending both parties' canonical
Droop-quota floors. This is the abstract seat-fill step after the appendix's
separate solid-coalition quota processes terminate.
-/
theorem exists_stvTwoPartyQuotaLowerBounds {seats voters : ℕ} {partyShare : ℝ}
    (hshare_nonneg : 0 ≤ partyShare) (hshare_le : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters) :
    ∃ partySeats otherPartySeats,
      stvTwoPartyQuotaLowerBounds partySeats otherPartySeats seats voters
        partyShare := by
  let partySeats : ℕ :=
    ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊
  let otherQuotaFloor : ℕ :=
    ⌊(1 - partyShare) * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊
  have hsum : partySeats + otherQuotaFloor ≤ seats := by
    simpa [partySeats, otherQuotaFloor] using
      (stvTwoPartyQuotaFloors_sum_le_seats
        (seats := seats) (voters := voters) (partyShare := partyShare)
        hshare_nonneg hshare_le)
  have hparty_le_seats : partySeats ≤ seats :=
    le_trans (Nat.le_add_right partySeats otherQuotaFloor) hsum
  have hsum_comm : otherQuotaFloor + partySeats ≤ seats := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
  have hother_lower : otherQuotaFloor ≤ seats - partySeats := by
    exact (Nat.le_sub_iff_add_le hparty_le_seats).2 hsum_comm
  refine ⟨partySeats, seats - partySeats, ?_, hshare_nonneg, hshare_le,
    hvoters, ?_, ?_⟩
  · exact Nat.add_sub_cancel' hparty_le_seats
  · rfl
  · exact hother_lower

/--
Existential packaging of the filled two-party quota extension for the paper
form that names only the focal party's STV seat count.
-/
theorem exists_stvSolidCoalitionQuotaLowerBounds {seats voters : ℕ}
    {partyShare : ℝ}
    (hshare_nonneg : 0 ≤ partyShare) (hshare_le : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters) :
    ∃ seatCount,
      stvSolidCoalitionQuotaLowerBounds seatCount partyShare seats voters := by
  rcases exists_stvTwoPartyQuotaLowerBounds
      (seats := seats) (voters := voters) (partyShare := partyShare)
      hshare_nonneg hshare_le hvoters with
    ⟨partySeats, otherPartySeats, hbounds⟩
  exact ⟨partySeats, otherPartySeats, hbounds⟩

/--
Source-facing residual boundary from the separate solid-coalition STV processes:
after quota elections for each party, the residual vote mass for each party is
below one Droop quota.
-/
def stvTwoPartyQuotaResidualBounds (partySeats otherPartySeats seats voters : ℕ)
    (partyShare : ℝ) : Prop :=
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    QuotaResidualBound partySeats
      (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ) ∧
    QuotaResidualBound otherPartySeats
      ((1 - partyShare) * (voters : ℝ)) (STVQuota seats voters : ℝ)

/--
Existential packaging of the residual boundary when the paper only names the
focal party's STV seat count.
-/
def stvSolidCoalitionQuotaResidualBounds (seatCount : ℕ) (partyShare : ℝ)
    (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartyQuotaResidualBounds seatCount otherPartySeats seats voters partyShare

/--
Source-facing quota-witness boundary from the appendix STV proof.

For each party, there is a number of same-party quota winners no larger than
the party's final STV seat count, and those quota winners leave less than one
quota of same-party residual vote mass. This is weaker and more source-faithful
than requiring the final party seat count itself to be the quota-process count.
-/
def stvTwoPartyQuotaWitnessBounds (partySeats otherPartySeats seats voters : ℕ)
    (partyShare : ℝ) : Prop :=
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    QuotaLowerBoundWitness partySeats
      (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ) ∧
    QuotaLowerBoundWitness otherPartySeats
      ((1 - partyShare) * (voters : ℝ)) (STVQuota seats voters : ℝ)

/--
Existential packaging of the quota-witness boundary when the paper only names
the focal party's STV seat count.
-/
def stvSolidCoalitionQuotaWitnessBounds (seatCount : ℕ) (partyShare : ℝ)
    (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartyQuotaWitnessBounds seatCount otherPartySeats seats voters partyShare

/--
Appendix-style solid-coalition process boundary: for each party, a terminal
same-party quota process has produced quota winners no larger than the final
party seat count.
-/
def stvTwoPartySolidCoalitionProcessBounds
    (partySeats otherPartySeats seats voters : ℕ) (partyShare : ℝ) : Prop :=
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    ∃ partyProcess :
        PartyQuotaProcess
          (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ),
      ∃ otherPartyProcess :
        PartyQuotaProcess
          ((1 - partyShare) * (voters : ℝ)) (STVQuota seats voters : ℝ),
        partyProcess.terminalState.quotaWinners ≤ partySeats ∧
        otherPartyProcess.terminalState.quotaWinners ≤ otherPartySeats

/--
Existential packaging of the appendix-style process boundary when the paper
only names the focal party's STV seat count.
-/
def stvSolidCoalitionProcessBounds (seatCount : ℕ) (partyShare : ℝ)
    (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartySolidCoalitionProcessBounds seatCount otherPartySeats seats voters
      partyShare

/--
Appendix-style terminal process states imply the quota-witness boundary.
-/
theorem stvTwoPartyQuotaWitnessBounds_of_processBounds
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartySolidCoalitionProcessBounds
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters,
      partyProcess, otherPartyProcess, hpartySeats, hotherSeats⟩
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  refine ⟨htotal, hshare_nonneg, hshare_le, hvoters, ?_, ?_⟩
  · exact quotaLowerBoundWitness_of_partyQuotaProcessCertificate partyProcess
      hquota_pos hpartySeats
  · exact quotaLowerBoundWitness_of_partyQuotaProcessCertificate otherPartyProcess
      hquota_pos hotherSeats

/--
The appendix-style process boundary implies the quota-witness boundary.
-/
theorem stvSolidCoalitionQuotaWitnessBounds_of_processBounds
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds : stvSolidCoalitionProcessBounds seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats, stvTwoPartyQuotaWitnessBounds_of_processBounds htwoParty⟩

/--
Direct quota lower bounds also provide the quota-witness boundary; the witness
uses the canonical floor residual from `Voting.STV.Quota`.
-/
theorem stvTwoPartyQuotaWitnessBounds_of_quotaLowerBounds
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyQuotaLowerBounds partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyLower, hotherLower⟩
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  have hvoters_nonneg : 0 ≤ (voters : ℝ) := by positivity
  have hparty_votes_nonneg : 0 ≤ partyShare * (voters : ℝ) := by
    exact mul_nonneg hshare_nonneg hvoters_nonneg
  have hother_votes_nonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) := by
    exact mul_nonneg (sub_nonneg.mpr hshare_le) hvoters_nonneg
  have hpartyLower' :
      ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ ≤
        partySeats := by
    simpa [mul_div_assoc] using hpartyLower
  have hotherLower' :
      ⌊((1 - partyShare) * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ ≤
        otherPartySeats := by
    simpa [mul_div_assoc] using hotherLower
  refine ⟨htotal, hshare_nonneg, hshare_le, hvoters, ?_, ?_⟩
  · exact quotaLowerBoundWitness_of_floor_votes_div_quota_le_finalSeats
      hquota_pos hparty_votes_nonneg hpartyLower'
  · exact quotaLowerBoundWitness_of_floor_votes_div_quota_le_finalSeats
      hquota_pos hother_votes_nonneg hotherLower'

/--
The named quota lower-bound boundary provides the quota-witness boundary.
-/
theorem stvSolidCoalitionQuotaWitnessBounds_of_quotaLowerBounds
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds : stvSolidCoalitionQuotaLowerBounds seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats, stvTwoPartyQuotaWitnessBounds_of_quotaLowerBounds htwoParty⟩

/--
Direct quota lower bounds construct the appendix-style terminal same-party
process certificates.
-/
theorem stvTwoPartySolidCoalitionProcessBounds_of_quotaLowerBounds
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyQuotaLowerBounds partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartySolidCoalitionProcessBounds
      partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyLower, hotherLower⟩
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  have hvoters_nonneg : 0 ≤ (voters : ℝ) := by positivity
  have hparty_votes_nonneg : 0 ≤ partyShare * (voters : ℝ) :=
    mul_nonneg hshare_nonneg hvoters_nonneg
  have hother_votes_nonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hshare_le) hvoters_nonneg
  have hpartyLower' :
      ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ ≤
        partySeats := by
    simpa [mul_div_assoc] using hpartyLower
  have hotherLower' :
      ⌊((1 - partyShare) * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ ≤
        otherPartySeats := by
    simpa [mul_div_assoc] using hotherLower
  rcases exists_partyQuotaProcess_floor
      (initialVotes := partyShare * (voters : ℝ))
      (quota := (STVQuota seats voters : ℝ))
      (remainingCandidates :=
        ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊)
      hquota_pos hparty_votes_nonneg le_rfl with
    ⟨partyProcess, hpartyQuotaWinners, _hpartyMass⟩
  rcases exists_partyQuotaProcess_floor
      (initialVotes := (1 - partyShare) * (voters : ℝ))
      (quota := (STVQuota seats voters : ℝ))
      (remainingCandidates :=
        ⌊((1 - partyShare) * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊)
      hquota_pos hother_votes_nonneg le_rfl with
    ⟨otherPartyProcess, hotherQuotaWinners, _hotherMass⟩
  refine ⟨htotal, hshare_nonneg, hshare_le, hvoters,
    partyProcess, otherPartyProcess, ?_, ?_⟩
  · rw [hpartyQuotaWinners]
    exact hpartyLower'
  · rw [hotherQuotaWinners]
    exact hotherLower'

/--
The named quota lower-bound boundary constructs the appendix-style terminal
process boundary.
-/
theorem stvSolidCoalitionProcessBounds_of_quotaLowerBounds
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds : stvSolidCoalitionQuotaLowerBounds seatCount partyShare seats voters) :
    stvSolidCoalitionProcessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartySolidCoalitionProcessBounds_of_quotaLowerBounds htwoParty⟩

/--
Residual bounds imply the quota lower bounds used by the remaining arithmetic
bridge.
-/
theorem stvTwoPartyQuotaLowerBounds_of_residualBounds
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyQuotaResidualBounds partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartyQuotaLowerBounds partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyResidual, hotherResidual⟩
  refine ⟨htotal, hshare_nonneg, hshare_le, hvoters, ?_, ?_⟩
  · simpa [mul_div_assoc] using
      (floor_votes_div_quota_le_seatsElected_of_residualBound hpartyResidual)
  · simpa [mul_div_assoc] using
      (floor_votes_div_quota_le_seatsElected_of_residualBound hotherResidual)

/--
The residual boundary implies the quota lower-bound boundary.
-/
theorem stvSolidCoalitionQuotaLowerBounds_of_residualBounds
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds : stvSolidCoalitionQuotaResidualBounds seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaLowerBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats, stvTwoPartyQuotaLowerBounds_of_residualBounds htwoParty⟩

/--
Quota witnesses imply the quota lower bounds used by the remaining arithmetic
bridge.
-/
theorem stvTwoPartyQuotaLowerBounds_of_quotaWitnessBounds
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartyQuotaLowerBounds partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyWitness, hotherWitness⟩
  refine ⟨htotal, hshare_nonneg, hshare_le, hvoters, ?_, ?_⟩
  · simpa [mul_div_assoc] using
      (floor_votes_div_quota_le_finalSeats_of_quotaLowerBoundWitness hpartyWitness)
  · simpa [mul_div_assoc] using
      (floor_votes_div_quota_le_finalSeats_of_quotaLowerBoundWitness hotherWitness)

/--
The quota-witness boundary implies the quota lower-bound boundary.
-/
theorem stvSolidCoalitionQuotaLowerBounds_of_quotaWitnessBounds
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds : stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaLowerBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats, stvTwoPartyQuotaLowerBounds_of_quotaWitnessBounds htwoParty⟩

/--
The appendix terminal-process boundary is equivalent to the direct quota
lower-bound boundary once reusable process/residual arithmetic is available.
-/
theorem stvTwoPartySolidCoalitionProcessBounds_iff_quotaLowerBounds
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ} :
    stvTwoPartySolidCoalitionProcessBounds
        partySeats otherPartySeats seats voters partyShare ↔
      stvTwoPartyQuotaLowerBounds
        partySeats otherPartySeats seats voters partyShare := by
  constructor
  · intro hprocess
    exact stvTwoPartyQuotaLowerBounds_of_quotaWitnessBounds
      (stvTwoPartyQuotaWitnessBounds_of_processBounds hprocess)
  · intro hlower
    exact stvTwoPartySolidCoalitionProcessBounds_of_quotaLowerBounds hlower

/--
Named version of the equivalence between the appendix terminal-process boundary
and direct quota lower bounds.
-/
theorem stvSolidCoalitionProcessBounds_iff_quotaLowerBounds
    {seatCount seats voters : ℕ} {partyShare : ℝ} :
    stvSolidCoalitionProcessBounds seatCount partyShare seats voters ↔
      stvSolidCoalitionQuotaLowerBounds seatCount partyShare seats voters := by
  constructor
  · intro hprocess
    exact stvSolidCoalitionQuotaLowerBounds_of_quotaWitnessBounds
      (stvSolidCoalitionQuotaWitnessBounds_of_processBounds hprocess)
  · intro hlower
    exact stvSolidCoalitionProcessBounds_of_quotaLowerBounds hlower

/--
Quota lower bounds imply the proportional lower bounds used in the final
two-party rounding step.
-/
theorem stvTwoPartyLowerBounds_of_quotaLowerBounds
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyQuotaLowerBounds partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartyLowerBounds partySeats otherPartySeats partyShare seats := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyQuota, hotherQuota⟩
  refine ⟨htotal, ?_, ?_⟩
  · exact le_trans
      (floor_partyShare_mul_seats_le_floor_partyShare_mul_voters_div_quota
        (seats := seats) (voters := voters) (partyShare := partyShare)
        hshare_nonneg hvoters)
      hpartyQuota
  · exact le_trans
      (floor_partyShare_mul_seats_le_floor_partyShare_mul_voters_div_quota
        (seats := seats) (voters := voters) (partyShare := 1 - partyShare)
        (sub_nonneg.mpr hshare_le) hvoters)
      hotherQuota

/--
The quota lower-bound boundary implies the lower-bound/conservation boundary.
-/
theorem stvSolidCoalitionLowerBounds_of_quotaLowerBounds {seatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hbounds : stvSolidCoalitionQuotaLowerBounds seatCount partyShare seats voters) :
    stvSolidCoalitionLowerBounds seatCount partyShare seats := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats, stvTwoPartyLowerBounds_of_quotaLowerBounds htwoParty⟩

/--
The source proof's two-party lower-bound/conservation boundary implies the
STV floor/ceiling seat-share consequence.
-/
theorem stvSeatShareBounds_of_twoPartyLowerBounds {partySeats otherPartySeats seats : ℕ}
    {partyShare : ℝ}
    (hbounds : stvTwoPartyLowerBounds partySeats otherPartySeats partyShare seats) :
    stvSeatShareBounds partySeats partyShare seats := by
  rcases hbounds with ⟨htotal, hlower, hotherLower⟩
  constructor
  · exact hlower
  · have hround :
        roundedSeatShare partySeats partyShare seats :=
      roundedSeatShare_of_twoParty_lowerBounds htotal hlower hotherLower
    rcases hround with hfloor | hceil
    · rw [hfloor]
      exact Nat.floor_le_ceil (partyShare * (seats : ℝ))
    · rw [hceil]

/--
The named solid-coalition lower-bound boundary implies the STV floor/ceiling
seat-share consequence.
-/
theorem stvSeatShareBounds_of_solidCoalitionLowerBounds {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hbounds : stvSolidCoalitionLowerBounds seatCount partyShare seats) :
    stvSeatShareBounds seatCount partyShare seats := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact stvSeatShareBounds_of_twoPartyLowerBounds htwoParty

/--
The STV floor/ceiling bounds imply the rounded seat-share conclusion.
-/
theorem stvSeatShareBounds_seatShareRounded {seatCount seats : ℕ} {partyShare : ℝ}
    (hbounds : stvSeatShareBounds seatCount partyShare seats) :
    seatShareRounded seatCount partyShare seats := by
  exact roundedSeatShare_of_floor_le_of_le_ceil hbounds.1 hbounds.2

/--
Proposition 1 reduced to its two mathematical inputs: the cited STV
solid-coalition bounds and the PAV min-argmax characterization.
-/
theorem proposition1_seatSharesRounded_of_stvBounds_and_pavMinArgmax
    {stvSeatCount pavSeatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv : stvSeatShareBounds stvSeatCount partyShare seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  exact ⟨stvSeatShareBounds_seatShareRounded hstv,
    pavSeatMinArgmax_seatShareRounded hpos hle hpav⟩

/--
Proposition 1 reduced to the source proof's STV lower-bound/conservation
boundary and the PAV min-argmax characterization.
-/
theorem proposition1_seatSharesRounded_of_stvLowerBounds_and_pavMinArgmax
    {stvSeatCount pavSeatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv : stvSolidCoalitionLowerBounds stvSeatCount partyShare seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvBounds_and_pavMinArgmax hpos hle
    (stvSeatShareBounds_of_solidCoalitionLowerBounds hstv) hpav

/--
Proposition 1 reduced to the source proof's STV quota lower-bound boundary and
the PAV min-argmax characterization.
-/
theorem proposition1_seatSharesRounded_of_stvQuotaLowerBounds_and_pavMinArgmax
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv : stvSolidCoalitionQuotaLowerBounds stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvLowerBounds_and_pavMinArgmax hpos hle
    (stvSolidCoalitionLowerBounds_of_quotaLowerBounds hstv) hpav

/--
Proposition 1 reduced to the appendix STV quota-witness boundary and the PAV
min-argmax characterization.
-/
theorem proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv : stvSolidCoalitionQuotaWitnessBounds stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvQuotaLowerBounds_and_pavMinArgmax hpos hle
    (stvSolidCoalitionQuotaLowerBounds_of_quotaWitnessBounds hstv) hpav

/--
Proposition 1 reduced to the source proof's STV residual boundary and the PAV
min-argmax characterization.
-/
theorem proposition1_seatSharesRounded_of_stvQuotaResidualBounds_and_pavMinArgmax
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv : stvSolidCoalitionQuotaResidualBounds stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvQuotaLowerBounds_and_pavMinArgmax hpos hle
    (stvSolidCoalitionQuotaLowerBounds_of_residualBounds hstv) hpav

end GGRS26CombattingGerrymanderingRCV
