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
- `stvSolidCoalitionBallots_partyTraceIsolation`: STV-dynamics bridge showing
  solid coalitions have no cross-party active support before party exhaustion.
- `stvSolidCoalitionProcessBounds_of_fractionalReplayBounds`: shared
  fractional trace replay bridge into the appendix terminal process predicate.
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
Fractional STV replay boundary over the shared trace dynamics.

For each party, a concrete fractional replay of the shared `STVTrace` reaches a
below-quota terminal state, and the number of quota winners in that replay is no
larger than the party's final STV seat count.
-/
def stvTwoPartyFractionalReplayBounds {Candidate : Type*}
    [DecidableEq Candidate]
    (partySeats otherPartySeats seats voters : ℕ) (partyShare : ℝ) : Prop :=
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    ∃ partyReplay :
        FractionalPartySTVTraceReplay
          (Candidate := Candidate)
          (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ),
      ∃ otherPartyReplay :
        FractionalPartySTVTraceReplay
          (Candidate := Candidate)
          ((1 - partyShare) * (voters : ℝ)) (STVQuota seats voters : ℝ),
        partyReplay.trace = otherPartyReplay.trace ∧
        partyReplay.terminalState.quotaWinners ≤ partySeats ∧
        otherPartyReplay.terminalState.quotaWinners ≤ otherPartySeats

/--
Transfer-rule-parametric fractional STV preservation boundary.

This is the rule-explicit form of the GGRS “any transfer rule” claim: for an
arbitrary transfer rule, if the analyzed shared candidate-level STV steps
satisfy the source preservation laws for both parties and both party projections
terminate below quota, then the subsequent GGRS quota and rounding conclusions
apply. The preservation laws are the paper's transfer condition: same-party
quota elections retain exactly one quota and transfer the full surplus inside
the party, while same-party eliminations preserve party vote mass.
-/
def stvTwoPartyTransferRuleReplayBounds {Candidate : Type*}
    [DecidableEq Candidate]
    (rule : FractionalSTVTransferRule Candidate)
    (partySeats otherPartySeats seats voters : ℕ) (partyShare : ℝ) : Prop :=
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    ∃ partyReplay :
        FractionalPartySTVTransferRulePreservationReplay
          (Candidate := Candidate) rule
          (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ),
      ∃ otherPartyReplay :
        FractionalPartySTVTransferRulePreservationReplay
          (Candidate := Candidate) rule
          ((1 - partyShare) * (voters : ℝ)) (STVQuota seats voters : ℝ),
        partyReplay.steps = otherPartyReplay.steps ∧
        partyReplay.terminalState.quotaWinners ≤ partySeats ∧
        otherPartyReplay.terminalState.quotaWinners ≤ otherPartySeats

/--
Existential packaging of the fractional replay boundary when the paper only
names the focal party's STV seat count.
-/
def stvSolidCoalitionFractionalReplayBounds {Candidate : Type*}
    [DecidableEq Candidate] (seatCount : ℕ) (partyShare : ℝ)
    (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartyFractionalReplayBounds
      (Candidate := Candidate)
      seatCount otherPartySeats seats voters partyShare

/--
Existential packaging of the rule-parametric preservation boundary when the
paper only names the focal party's STV seat count.
-/
def stvSolidCoalitionTransferRuleReplayBounds {Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (seatCount : ℕ) (partyShare : ℝ) (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartyTransferRuleReplayBounds
      (Candidate := Candidate) rule
      seatCount otherPartySeats seats voters partyShare

/--
Source-primitive candidate-trace STV boundary for the Appendix Proposition 1
argument.

This exposes the paper's primitive route directly: both parties have at least
`seats` candidates, both projections of the same candidate-level STV trace
satisfy the transfer-preservation laws for the chosen rule, and the resulting
quota winners are included in the final party seat counts.
-/
def stvTwoPartySourcePrimitiveTransferTraceBounds {Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyCandidates otherPartyCandidates :
      Finset Candidate)
    (partySeats otherPartySeats seats voters : ℕ) (partyShare : ℝ) : Prop :=
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    seats ≤ partyCandidates.card ∧
    seats ≤ otherPartyCandidates.card ∧
    PartyTransferPreservationTraceOutcome rule trace partyCandidates
      (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ) partySeats ∧
    PartyTransferPreservationTraceOutcome rule trace otherPartyCandidates
      ((1 - partyShare) * (voters : ℝ)) (STVQuota seats voters : ℝ)
      otherPartySeats

/--
Existential packaging of the source-primitive candidate-trace STV boundary
when the paper only names the focal party's STV seat count.
-/
def stvSolidCoalitionSourcePrimitiveTransferTraceBounds {Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyCandidates otherPartyCandidates :
      Finset Candidate)
    (seatCount : ℕ) (partyShare : ℝ) (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartySourcePrimitiveTransferTraceBounds
      (Candidate := Candidate) rule trace partyCandidates otherPartyCandidates
      seatCount otherPartySeats seats voters partyShare

/--
Source-primitive solid-coalition trace bounds.

This is the fully expanded STV input for the theoretical GGRS proof: raw
solid-coalition ballot assumptions justify party isolation, while primitive
per-step transfer laws for the concrete rule and trace construct the
candidate-level party preservation paths internally.
-/
def stvTwoPartySolidCoalitionPrimitiveTraceBounds {Voter Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyVoters otherPartyVoters : Finset Voter)
    (ballots : Voter → Ballot Candidate)
    (partyCandidates otherPartyCandidates : Finset Candidate)
    (partySeats otherPartySeats seats voters : ℕ) (partyShare : ℝ) : Prop :=
  let quota : ℝ := STVQuota seats voters
  let partyStart :=
    PartyQuotaStartState partyCandidates.card (partyShare * (voters : ℝ))
  let partyTerminal :=
    partyTransferPreservationTerminalState partyCandidates quota
      rule.fractionalTally trace.steps partyStart
  let otherStart :=
    PartyQuotaStartState otherPartyCandidates.card
      ((1 - partyShare) * (voters : ℝ))
  let otherTerminal :=
    partyTransferPreservationTerminalState otherPartyCandidates quota
      rule.fractionalTally trace.steps otherStart
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    seats ≤ partyCandidates.card ∧
    seats ≤ otherPartyCandidates.card ∧
    SolidCoalitionBallots partyVoters ballots partyCandidates ∧
    SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates ∧
    FractionalPartySTVPrimitiveTransferTraceLaw partyCandidates quota
      rule.fractionalTally trace.steps partyStart ∧
    PartyQuotaTerminalBelowQuota quota partyTerminal ∧
    partyTerminal.quotaWinners ≤ partySeats ∧
    FractionalPartySTVPrimitiveTransferTraceLaw otherPartyCandidates quota
      rule.fractionalTally trace.steps otherStart ∧
    PartyQuotaTerminalBelowQuota quota otherTerminal ∧
    otherTerminal.quotaWinners ≤ otherPartySeats

/--
Existential packaging of the fully expanded solid-coalition primitive trace
bounds when the paper names only the focal party's STV seat count.
-/
def stvSolidCoalitionPrimitiveTraceBounds {Voter Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyVoters otherPartyVoters : Finset Voter)
    (ballots : Voter → Ballot Candidate)
    (partyCandidates otherPartyCandidates : Finset Candidate)
    (seatCount : ℕ) (partyShare : ℝ) (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartySolidCoalitionPrimitiveTraceBounds
      (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
      otherPartyVoters ballots partyCandidates otherPartyCandidates seatCount
      otherPartySeats seats voters partyShare

/--
Indexed source-primitive solid-coalition trace bounds.

This is the per-concrete-step form expected from an executable STV run: each
`trace.steps.get i` satisfies the primitive transfer law at the deterministic
party projection state obtained by folding the preceding concrete steps.
-/
def stvTwoPartySolidCoalitionIndexedPrimitiveTraceBounds
    {Voter Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyVoters otherPartyVoters : Finset Voter)
    (ballots : Voter → Ballot Candidate)
    (partyCandidates otherPartyCandidates : Finset Candidate)
    (partySeats otherPartySeats seats voters : ℕ) (partyShare : ℝ) : Prop :=
  let quota : ℝ := STVQuota seats voters
  let partyStart :=
    PartyQuotaStartState partyCandidates.card (partyShare * (voters : ℝ))
  let partyTerminal :=
    partyTransferPreservationTerminalState partyCandidates quota
      rule.fractionalTally trace.steps partyStart
  let otherStart :=
    PartyQuotaStartState otherPartyCandidates.card
      ((1 - partyShare) * (voters : ℝ))
  let otherTerminal :=
    partyTransferPreservationTerminalState otherPartyCandidates quota
      rule.fractionalTally trace.steps otherStart
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    seats ≤ partyCandidates.card ∧
    seats ≤ otherPartyCandidates.card ∧
    SolidCoalitionBallots partyVoters ballots partyCandidates ∧
    SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates ∧
    (∀ i : Fin trace.steps.length,
      FractionalPartySTVPrimitiveTransferStepLaw partyCandidates
        (rule.fractionalTally (trace.steps.get i)) quota
        (trace.steps.get i)
        (partyTransferPreservationTerminalState partyCandidates quota
          rule.fractionalTally (trace.steps.take i.1) partyStart)) ∧
    PartyQuotaTerminalBelowQuota quota partyTerminal ∧
    partyTerminal.quotaWinners ≤ partySeats ∧
    (∀ i : Fin trace.steps.length,
      FractionalPartySTVPrimitiveTransferStepLaw otherPartyCandidates
        (rule.fractionalTally (trace.steps.get i)) quota
        (trace.steps.get i)
        (partyTransferPreservationTerminalState otherPartyCandidates quota
          rule.fractionalTally (trace.steps.take i.1) otherStart)) ∧
    PartyQuotaTerminalBelowQuota quota otherTerminal ∧
    otherTerminal.quotaWinners ≤ otherPartySeats

/--
Existential packaging of the indexed source-primitive solid-coalition trace
bounds when the paper names only the focal party's STV seat count.
-/
def stvSolidCoalitionIndexedPrimitiveTraceBounds {Voter Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyVoters otherPartyVoters : Finset Voter)
    (ballots : Voter → Ballot Candidate)
    (partyCandidates otherPartyCandidates : Finset Candidate)
    (seatCount : ℕ) (partyShare : ℝ) (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartySolidCoalitionIndexedPrimitiveTraceBounds
      (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
      otherPartyVoters ballots partyCandidates otherPartyCandidates seatCount
      otherPartySeats seats voters partyShare

/--
Source-step solid-coalition trace bounds.

Compared with the primitive trace boundary, this consumes the reusable
source-step dynamics law: focused candidate active, active tallies nonnegative,
party state equal to the active same-party tally mass, and same-party quota
elections meeting quota. The primitive transfer trace is derived internally.
-/
def stvTwoPartySolidCoalitionSourceStepTraceBounds
    {Voter Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyVoters otherPartyVoters : Finset Voter)
    (ballots : Voter → Ballot Candidate)
    (partyCandidates otherPartyCandidates : Finset Candidate)
    (partySeats otherPartySeats seats voters : ℕ) (partyShare : ℝ) : Prop :=
  let quota : ℝ := STVQuota seats voters
  partySeats + otherPartySeats = seats ∧
    0 ≤ partyShare ∧
    partyShare ≤ 1 ∧
    seats * (seats + 1) ≤ voters ∧
    seats ≤ partyCandidates.card ∧
    seats ≤ otherPartyCandidates.card ∧
    SolidCoalitionBallots partyVoters ballots partyCandidates ∧
    SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates ∧
    PartyTransferSourceTraceOutcome rule trace partyCandidates
      (partyShare * (voters : ℝ)) quota partySeats ∧
    PartyTransferSourceTraceOutcome rule trace otherPartyCandidates
      ((1 - partyShare) * (voters : ℝ)) quota otherPartySeats

/--
Existential packaging of the source-step solid-coalition trace bounds when the
paper names only the focal party's STV seat count.
-/
def stvSolidCoalitionSourceStepTraceBounds {Voter Candidate : Type*}
    [DecidableEq Candidate] (rule : FractionalSTVTransferRule Candidate)
    (trace : STVTrace Candidate) (partyVoters otherPartyVoters : Finset Voter)
    (ballots : Voter → Ballot Candidate)
    (partyCandidates otherPartyCandidates : Finset Candidate)
    (seatCount : ℕ) (partyShare : ℝ) (seats voters : ℕ) : Prop :=
  ∃ otherPartySeats,
    stvTwoPartySolidCoalitionSourceStepTraceBounds
      (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
      otherPartyVoters ballots partyCandidates otherPartyCandidates seatCount
      otherPartySeats seats voters partyShare

/--
STV-dynamics bridge for the source proof's party-level analysis step.

If a party's voters rank all same-party candidates above all other-party
candidates, then at every STV trace step before that party is exhausted, no
outside-party candidate has active support from that party's voters.
-/
theorem stvSolidCoalitionBallots_partyTraceIsolation
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {trace : STVTrace Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates) :
    NoCrossPartyTransferBeforeExhaustion
      voters ballots partyCandidates trace :=
  noCrossPartyTransferBeforeExhaustion_of_solidCoalitionBallots hsolid

/--
A concrete shared-trace fractional replay provides the appendix terminal
process boundary.
-/
theorem stvTwoPartySolidCoalitionProcessBounds_of_fractionalReplayBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyFractionalReplayBounds
        (Candidate := Candidate)
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartySolidCoalitionProcessBounds
      partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters,
      partyReplay, otherPartyReplay, _hsameTrace, hpartySeats, hotherSeats⟩
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters,
    partyQuotaProcess_of_fractionalPartySTVTraceReplay partyReplay,
    partyQuotaProcess_of_fractionalPartySTVTraceReplay otherPartyReplay,
    hpartySeats, hotherSeats⟩

/--
Any transfer rule whose analyzed candidate-level steps satisfy the source
transfer-preservation laws for both parties provides the appendix terminal
process boundary.
-/
theorem stvTwoPartySolidCoalitionProcessBounds_of_transferRuleReplayBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyTransferRuleReplayBounds
        (Candidate := Candidate) rule
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartySolidCoalitionProcessBounds
      partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters,
      partyReplay, otherPartyReplay, _hsameTrace, hpartySeats, hotherSeats⟩
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters,
    partyQuotaProcess_of_transferRulePreservationReplay partyReplay,
    partyQuotaProcess_of_transferRulePreservationReplay otherPartyReplay,
    hpartySeats, hotherSeats⟩

/--
The named fractional replay boundary provides the appendix terminal process
boundary.
-/
theorem stvSolidCoalitionProcessBounds_of_fractionalReplayBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionFractionalReplayBounds
        (Candidate := Candidate) seatCount partyShare seats voters) :
    stvSolidCoalitionProcessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartySolidCoalitionProcessBounds_of_fractionalReplayBounds htwoParty⟩

/--
The named transfer-rule-parametric preservation boundary provides the appendix
terminal process boundary.
-/
theorem stvSolidCoalitionProcessBounds_of_transferRuleReplayBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionTransferRuleReplayBounds
        (Candidate := Candidate) rule seatCount partyShare seats voters) :
    stvSolidCoalitionProcessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartySolidCoalitionProcessBounds_of_transferRuleReplayBounds
      htwoParty⟩

/--
A concrete shared-trace fractional replay provides the appendix quota-witness
boundary directly, without using the terminal party-process predicate as an
intermediate theorem boundary.
-/
theorem stvTwoPartyQuotaWitnessBounds_of_fractionalReplayBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyFractionalReplayBounds
        (Candidate := Candidate)
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters
      partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters,
      partyReplay, otherPartyReplay, _hsameTrace, hpartySeats, hotherSeats⟩
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters,
    quotaLowerBoundWitness_of_fractionalPartySTVTraceReplay
      partyReplay hquota_pos hpartySeats,
    quotaLowerBoundWitness_of_fractionalPartySTVTraceReplay
      otherPartyReplay hquota_pos hotherSeats⟩

/--
Any transfer rule whose analyzed candidate-level steps satisfy the source
transfer-preservation laws for both parties provides the appendix quota-witness
boundary directly.
-/
theorem stvTwoPartyQuotaWitnessBounds_of_transferRuleReplayBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartyTransferRuleReplayBounds
        (Candidate := Candidate) rule
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters
      partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters,
      partyReplay, otherPartyReplay, _hsameTrace, hpartySeats, hotherSeats⟩
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  let partyProcess :=
    partyQuotaProcess_of_transferRulePreservationReplay partyReplay
  let otherPartyProcess :=
    partyQuotaProcess_of_transferRulePreservationReplay otherPartyReplay
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters,
    quotaLowerBoundWitness_of_partyQuotaProcessCertificate
      partyProcess hquota_pos hpartySeats,
    quotaLowerBoundWitness_of_partyQuotaProcessCertificate
      otherPartyProcess hquota_pos hotherSeats⟩

/--
The source-primitive candidate-trace transfer boundary provides the appendix
quota-witness boundary directly.
-/
theorem stvTwoPartyQuotaWitnessBounds_of_sourcePrimitiveTransferTraceBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartySourcePrimitiveTransferTraceBounds
        (Candidate := Candidate) rule trace partyCandidates
        otherPartyCandidates partySeats otherPartySeats seats voters
        partyShare) :
    stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters
      partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, _hpartyCandidates,
      _hotherPartyCandidates, hpartyTrace, hotherTrace⟩
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  have hvoters_nonneg : 0 ≤ (voters : ℝ) := by positivity
  have hparty_votes_nonneg : 0 ≤ partyShare * (voters : ℝ) :=
    mul_nonneg hshare_nonneg hvoters_nonneg
  have hother_votes_nonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hshare_le) hvoters_nonneg
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters,
    quotaLowerBoundWitness_of_partyTransferPreservationTraceOutcome
      hquota_pos hparty_votes_nonneg hpartyTrace,
    quotaLowerBoundWitness_of_partyTransferPreservationTraceOutcome
      hquota_pos hother_votes_nonneg hotherTrace⟩

/--
Two source-primitive party trace outcomes, possibly obtained from different
prefixes of the same executable STV run, provide the quota-witness boundary.

This is the prefix-friendly form needed for source STV algorithms: once a
party's residual falls below quota, later rounds need not preserve that party's
active-coalition hypotheses for the lower-bound witness.
-/
theorem stvTwoPartyQuotaWitnessBounds_of_partyTransferTraceOutcomes
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {partyTrace otherPartyTrace : STVTrace Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (htotal : partySeats + otherPartySeats = seats)
    (hshare_nonneg : 0 ≤ partyShare) (hshare_le : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyTrace :
      PartyTransferPreservationTraceOutcome rule partyTrace partyCandidates
        (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ) partySeats)
    (hotherTrace :
      PartyTransferPreservationTraceOutcome rule otherPartyTrace
        otherPartyCandidates ((1 - partyShare) * (voters : ℝ))
        (STVQuota seats voters : ℝ) otherPartySeats) :
    stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters
      partyShare := by
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  have hvoters_nonneg : 0 ≤ (voters : ℝ) := by positivity
  have hparty_votes_nonneg : 0 ≤ partyShare * (voters : ℝ) :=
    mul_nonneg hshare_nonneg hvoters_nonneg
  have hother_votes_nonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hshare_le) hvoters_nonneg
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters,
    quotaLowerBoundWitness_of_partyTransferPreservationTraceOutcome
      hquota_pos hparty_votes_nonneg hpartyTrace,
    quotaLowerBoundWitness_of_partyTransferPreservationTraceOutcome
      hquota_pos hother_votes_nonneg hotherTrace⟩

/--
Variant of `stvTwoPartyQuotaWitnessBounds_of_partyTransferTraceOutcomes` where
the two party prefixes may use different generated transfer-rule
interpretations. The final quota-witness arithmetic only consumes the two
party-local outcomes.
-/
theorem stvTwoPartyQuotaWitnessBounds_of_partyTransferTraceOutcomes_twoRules
    {Candidate : Type*} [DecidableEq Candidate]
    {partyRule otherPartyRule : FractionalSTVTransferRule Candidate}
    {partyTrace otherPartyTrace : STVTrace Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (htotal : partySeats + otherPartySeats = seats)
    (hshare_nonneg : 0 ≤ partyShare) (hshare_le : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyTrace :
      PartyTransferPreservationTraceOutcome partyRule partyTrace
        partyCandidates (partyShare * (voters : ℝ))
        (STVQuota seats voters : ℝ) partySeats)
    (hotherTrace :
      PartyTransferPreservationTraceOutcome otherPartyRule otherPartyTrace
        otherPartyCandidates ((1 - partyShare) * (voters : ℝ))
        (STVQuota seats voters : ℝ) otherPartySeats) :
    stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters
      partyShare := by
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  have hvoters_nonneg : 0 ≤ (voters : ℝ) := by positivity
  have hparty_votes_nonneg : 0 ≤ partyShare * (voters : ℝ) :=
    mul_nonneg hshare_nonneg hvoters_nonneg
  have hother_votes_nonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hshare_le) hvoters_nonneg
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters,
    quotaLowerBoundWitness_of_partyTransferPreservationTraceOutcome
      hquota_pos hparty_votes_nonneg hpartyTrace,
    quotaLowerBoundWitness_of_partyTransferPreservationTraceOutcome
      hquota_pos hother_votes_nonneg hotherTrace⟩

/--
The named fractional replay boundary provides the appendix quota-witness
boundary directly.
-/
theorem stvSolidCoalitionQuotaWitnessBounds_of_fractionalReplayBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionFractionalReplayBounds
        (Candidate := Candidate) seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartyQuotaWitnessBounds_of_fractionalReplayBounds htwoParty⟩

/--
The named transfer-rule-parametric preservation boundary provides the appendix
quota-witness boundary directly.
-/
theorem stvSolidCoalitionQuotaWitnessBounds_of_transferRuleReplayBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionTransferRuleReplayBounds
        (Candidate := Candidate) rule seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartyQuotaWitnessBounds_of_transferRuleReplayBounds htwoParty⟩

/--
The named source-primitive candidate-trace transfer boundary provides the
appendix quota-witness boundary directly.
-/
theorem stvSolidCoalitionQuotaWitnessBounds_of_sourcePrimitiveTransferTraceBounds
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionSourcePrimitiveTransferTraceBounds
        (Candidate := Candidate) rule trace partyCandidates
        otherPartyCandidates seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartyQuotaWitnessBounds_of_sourcePrimitiveTransferTraceBounds
      htwoParty⟩

/--
Fully expanded source-primitive solid-coalition trace bounds construct the
candidate-level transfer-preservation trace boundary.
-/
theorem stvTwoPartySourcePrimitiveTransferTraceBounds_of_solidCoalitionPrimitiveTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartySolidCoalitionPrimitiveTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartySourcePrimitiveTransferTraceBounds
      (Candidate := Candidate) rule trace partyCandidates otherPartyCandidates
      partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyCandidates,
      hotherPartyCandidates, _hpartySolid, _hotherSolid, hpartyLaw,
      hpartyTerminal, hpartyFinal, hotherLaw, hotherTerminal, hotherFinal⟩
  have hpartyTrace :
      PartyTransferPrimitiveTraceOutcome rule trace partyCandidates
        (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ)
        partySeats := by
    dsimp [PartyTransferPrimitiveTraceOutcome]
    exact ⟨hpartyLaw, hpartyTerminal, hpartyFinal⟩
  have hotherTrace :
      PartyTransferPrimitiveTraceOutcome rule trace otherPartyCandidates
        ((1 - partyShare) * (voters : ℝ)) (STVQuota seats voters : ℝ)
        otherPartySeats := by
    dsimp [PartyTransferPrimitiveTraceOutcome]
    exact ⟨hotherLaw, hotherTerminal, hotherFinal⟩
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyCandidates,
    hotherPartyCandidates,
    partyTransferPreservationTraceOutcome_of_primitiveTraceOutcome
      hpartyTrace,
    partyTransferPreservationTraceOutcome_of_primitiveTraceOutcome
      hotherTrace⟩

/--
Indexed source-primitive solid-coalition trace facts construct the recursive
primitive trace boundary used by the existing quota-witness theorem.
-/
theorem stvTwoPartySolidCoalitionPrimitiveTraceBounds_of_indexedPrimitiveTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartySolidCoalitionIndexedPrimitiveTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartySolidCoalitionPrimitiveTraceBounds
      (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
      otherPartyVoters ballots partyCandidates otherPartyCandidates
      partySeats otherPartySeats seats voters partyShare := by
  dsimp [stvTwoPartySolidCoalitionIndexedPrimitiveTraceBounds,
    stvTwoPartySolidCoalitionPrimitiveTraceBounds] at hbounds ⊢
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyCandidates,
      hotherPartyCandidates, hpartySolid, hotherSolid, hpartySteps,
      hpartyTerminal, hpartyFinal, hotherSteps, hotherTerminal, hotherFinal⟩
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyCandidates,
    hotherPartyCandidates, hpartySolid, hotherSolid,
    fractionalPartySTVPrimitiveTransferTraceLaw_of_getElem hpartySteps,
    hpartyTerminal, hpartyFinal,
    fractionalPartySTVPrimitiveTransferTraceLaw_of_getElem hotherSteps,
    hotherTerminal, hotherFinal⟩

/--
Source-step solid-coalition trace facts construct the candidate-level
transfer-preservation trace boundary.
-/
theorem stvTwoPartySourcePrimitiveTransferTraceBounds_of_sourceStepTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartySolidCoalitionSourceStepTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartySourcePrimitiveTransferTraceBounds
      (Candidate := Candidate) rule trace partyCandidates otherPartyCandidates
      partySeats otherPartySeats seats voters partyShare := by
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyCandidates,
      hotherPartyCandidates, _hpartySolid, _hotherSolid, hpartyTrace,
      hotherTrace⟩
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyCandidates,
    hotherPartyCandidates,
    partyTransferPreservationTraceOutcome_of_sourceTraceOutcome
      hpartyTrace,
    partyTransferPreservationTraceOutcome_of_sourceTraceOutcome
      hotherTrace⟩

/--
Source-step solid-coalition trace facts construct the recursive primitive trace
boundary.
-/
theorem stvTwoPartySolidCoalitionPrimitiveTraceBounds_of_sourceStepTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartySolidCoalitionSourceStepTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartySolidCoalitionPrimitiveTraceBounds
      (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
      otherPartyVoters ballots partyCandidates otherPartyCandidates
      partySeats otherPartySeats seats voters partyShare := by
  dsimp [stvTwoPartySolidCoalitionSourceStepTraceBounds,
    stvTwoPartySolidCoalitionPrimitiveTraceBounds] at hbounds ⊢
  rcases hbounds with
    ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyCandidates,
      hotherPartyCandidates, hpartySolid, hotherSolid, hpartyTrace,
      hotherTrace⟩
  rcases hpartyTrace with ⟨hpartyLaw, hpartyTerminal, hpartyFinal⟩
  rcases hotherTrace with ⟨hotherLaw, hotherTerminal, hotherFinal⟩
  exact ⟨htotal, hshare_nonneg, hshare_le, hvoters, hpartyCandidates,
    hotherPartyCandidates, hpartySolid, hotherSolid,
    fractionalPartySTVPrimitiveTransferTraceLaw_of_sourceTraceLaw hpartyLaw,
    hpartyTerminal, hpartyFinal,
    fractionalPartySTVPrimitiveTransferTraceLaw_of_sourceTraceLaw hotherLaw,
    hotherTerminal, hotherFinal⟩

/--
The named source-step solid-coalition trace boundary constructs the recursive
primitive trace boundary.
-/
theorem stvSolidCoalitionPrimitiveTraceBounds_of_sourceStepTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionSourceStepTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        seatCount partyShare seats voters) :
    stvSolidCoalitionPrimitiveTraceBounds
      (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
      otherPartyVoters ballots partyCandidates otherPartyCandidates
      seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartySolidCoalitionPrimitiveTraceBounds_of_sourceStepTraceBounds
      htwoParty⟩

/--
The named indexed source-primitive solid-coalition trace boundary constructs
the recursive primitive trace boundary.
-/
theorem stvSolidCoalitionPrimitiveTraceBounds_of_indexedPrimitiveTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionIndexedPrimitiveTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        seatCount partyShare seats voters) :
    stvSolidCoalitionPrimitiveTraceBounds
      (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
      otherPartyVoters ballots partyCandidates otherPartyCandidates
      seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartySolidCoalitionPrimitiveTraceBounds_of_indexedPrimitiveTraceBounds
      htwoParty⟩

/--
Fully expanded source-primitive solid-coalition trace bounds provide the
appendix quota-witness boundary directly.
-/
theorem stvTwoPartyQuotaWitnessBounds_of_solidCoalitionPrimitiveTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partySeats otherPartySeats seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvTwoPartySolidCoalitionPrimitiveTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        partySeats otherPartySeats seats voters partyShare) :
    stvTwoPartyQuotaWitnessBounds partySeats otherPartySeats seats voters
      partyShare :=
  stvTwoPartyQuotaWitnessBounds_of_sourcePrimitiveTransferTraceBounds
    (stvTwoPartySourcePrimitiveTransferTraceBounds_of_solidCoalitionPrimitiveTraceBounds
      hbounds)

/--
The named fully expanded source-primitive solid-coalition trace bounds provide
the appendix quota-witness boundary directly.
-/
theorem stvSolidCoalitionQuotaWitnessBounds_of_solidCoalitionPrimitiveTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionPrimitiveTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters := by
  rcases hbounds with ⟨otherPartySeats, htwoParty⟩
  exact ⟨otherPartySeats,
    stvTwoPartyQuotaWitnessBounds_of_solidCoalitionPrimitiveTraceBounds
      htwoParty⟩

/--
Indexed source-primitive solid-coalition trace bounds provide the appendix
quota-witness boundary directly.
-/
theorem stvSolidCoalitionQuotaWitnessBounds_of_indexedPrimitiveTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionIndexedPrimitiveTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters :=
  stvSolidCoalitionQuotaWitnessBounds_of_solidCoalitionPrimitiveTraceBounds
    (stvSolidCoalitionPrimitiveTraceBounds_of_indexedPrimitiveTraceBounds hbounds)

/--
Source-step solid-coalition trace bounds provide the appendix quota-witness
boundary directly.
-/
theorem stvSolidCoalitionQuotaWitnessBounds_of_sourceStepTraceBounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hbounds :
      stvSolidCoalitionSourceStepTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        seatCount partyShare seats voters) :
    stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters :=
  stvSolidCoalitionQuotaWitnessBounds_of_solidCoalitionPrimitiveTraceBounds
    (stvSolidCoalitionPrimitiveTraceBounds_of_sourceStepTraceBounds hbounds)

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
Two-party lower bounds plus a trace-derived upper bound on the two visible
party seat counts imply the STV floor/ceiling consequence.
-/
theorem stvSeatShareBounds_of_twoPartyLowerBounds_le_total
    {partySeats otherPartySeats seats : ℕ} {partyShare : ℝ}
    (htotal_le : partySeats + otherPartySeats ≤ seats)
    (hlower : ⌊partyShare * (seats : ℝ)⌋₊ ≤ partySeats)
    (hotherLower : ⌊(1 - partyShare) * (seats : ℝ)⌋₊ ≤ otherPartySeats) :
    stvSeatShareBounds partySeats partyShare seats := by
  constructor
  · exact hlower
  · have hround :
        roundedSeatShare partySeats partyShare seats :=
      roundedSeatShare_of_twoParty_lowerBounds_le_total
        htotal_le hlower hotherLower
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
Proposition 1 from party-specific source trace outcomes. The two party
outcomes may come from different prefixes of the same executable STV run; once
a party's residual is below quota, its lower-bound witness is complete.
-/
theorem proposition1_seatSharesRounded_of_partyTransferTraceOutcomes_and_pavMinArgmax
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {partyTrace otherPartyTrace : STVTrace Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyTrace :
      PartyTransferPreservationTraceOutcome rule partyTrace partyCandidates
        (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ)
        stvSeatCount)
    (hotherTrace :
      PartyTransferPreservationTraceOutcome rule otherPartyTrace
        otherPartyCandidates ((1 - partyShare) * (voters : ℝ))
        (STVQuota seats voters : ℝ) otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hstv :
      stvSolidCoalitionQuotaWitnessBounds stvSeatCount partyShare seats voters :=
    ⟨otherPartySeatCount,
      stvTwoPartyQuotaWitnessBounds_of_partyTransferTraceOutcomes
        (rule := rule) (partyTrace := partyTrace)
        (otherPartyTrace := otherPartyTrace)
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        htotal hpos.le hle hvoters hpartyTrace hotherTrace⟩
  exact
    proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
      hpos hle hstv hpav

/--
Proposition 1 from party-specific source trace outcomes whose generated
transfer-rule interpretations may differ across the two party prefixes.
-/
theorem proposition1_seatSharesRounded_of_partyTransferTraceOutcomes_twoRules_and_pavMinArgmax
    {Candidate : Type*} [DecidableEq Candidate]
    {partyRule otherPartyRule : FractionalSTVTransferRule Candidate}
    {partyTrace otherPartyTrace : STVTrace Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyTrace :
      PartyTransferPreservationTraceOutcome partyRule partyTrace
        partyCandidates (partyShare * (voters : ℝ))
        (STVQuota seats voters : ℝ) stvSeatCount)
    (hotherTrace :
      PartyTransferPreservationTraceOutcome otherPartyRule otherPartyTrace
        otherPartyCandidates ((1 - partyShare) * (voters : ℝ))
        (STVQuota seats voters : ℝ) otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hstv :
      stvSolidCoalitionQuotaWitnessBounds stvSeatCount partyShare seats voters :=
    ⟨otherPartySeatCount,
      stvTwoPartyQuotaWitnessBounds_of_partyTransferTraceOutcomes_twoRules
        (partyRule := partyRule) (otherPartyRule := otherPartyRule)
        (partyTrace := partyTrace) (otherPartyTrace := otherPartyTrace)
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        htotal hpos.le hle hvoters hpartyTrace hotherTrace⟩
  exact
    proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
      hpos hle hstv hpav

/--
Proposition 1 from party-specific source-trace prefixes whose capacity
invariant reaches no active same-party candidates. This is the source-prefix
form targeted by the executable STV simulator: each party can close its quota
witness at the prefix where its residual falls below quota.
-/
theorem proposition1_seatSharesRounded_of_sourceTraceLaw_capacityTerminals_and_pavMinArgmax
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {partyTrace otherPartyTrace : STVTrace Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {partyStartActive partyTerminalActive
      otherStartActive otherTerminalActive : Finset Candidate}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyLaw :
      FractionalPartySTVSourceTraceLaw partyCandidates
        (STVQuota seats voters : ℝ) rule.fractionalTally
        partyTrace.steps
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))))
    (hpartyStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))))
    (hpartyNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (partyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ))
    (hpartyReplay :
      partyTrace.replaysFrom partyStartActive partyTerminalActive)
    (hpartyStartRemaining :
      (PartyQuotaStartState partyCandidates.card
        (partyShare * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates partyStartActive partyCandidates).card)
    (hpartySteps :
      ∀ step, step ∈ partyTrace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate))
    (hpartyTerminalNoParty :
      activePartyCandidates partyTerminalActive partyCandidates = ∅)
    (hpartyFinal :
      partyElectStepCount partyCandidates partyTrace.steps ≤ stvSeatCount)
    (hotherLaw :
      FractionalPartySTVSourceTraceLaw otherPartyCandidates
        (STVQuota seats voters : ℝ) rule.fractionalTally
        otherPartyTrace.steps
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))))
    (hotherStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))))
    (hotherNoquotaOnEliminate :
      ∀ i : Fin otherPartyTrace.steps.length,
        (otherPartyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  (otherPartyTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally (otherPartyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ))
    (hotherReplay :
      otherPartyTrace.replaysFrom otherStartActive otherTerminalActive)
    (hotherStartRemaining :
      (PartyQuotaStartState otherPartyCandidates.card
        ((1 - partyShare) * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates otherStartActive otherPartyCandidates).card)
    (hotherSteps :
      ∀ step, step ∈ otherPartyTrace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate))
    (hotherTerminalNoParty :
      activePartyCandidates otherTerminalActive otherPartyCandidates = ∅)
    (hotherFinal :
      partyElectStepCount otherPartyCandidates otherPartyTrace.steps ≤
        otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hpartyOutcome :
      PartyTransferPreservationTraceOutcome rule partyTrace partyCandidates
        (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ)
        stvSeatCount :=
    partyTransferPreservationTraceOutcome_of_sourceTraceLaw_capacityTerminal
      (rule := rule) (trace := partyTrace)
      (partyCandidates := partyCandidates)
      (initialVotes := partyShare * (voters : ℝ))
      (quota := (STVQuota seats voters : ℝ))
      (finalSeats := stvSeatCount)
      (startActive := partyStartActive)
      (terminalActive := partyTerminalActive)
      hpartyLaw hpartyStartCapacity hpartyNoquotaOnEliminate hpartyReplay
      hpartyStartRemaining hpartySteps hpartyTerminalNoParty hpartyFinal
  have hotherOutcome :
      PartyTransferPreservationTraceOutcome rule otherPartyTrace
        otherPartyCandidates ((1 - partyShare) * (voters : ℝ))
        (STVQuota seats voters : ℝ) otherPartySeatCount :=
    partyTransferPreservationTraceOutcome_of_sourceTraceLaw_capacityTerminal
      (rule := rule) (trace := otherPartyTrace)
      (partyCandidates := otherPartyCandidates)
      (initialVotes := (1 - partyShare) * (voters : ℝ))
      (quota := (STVQuota seats voters : ℝ))
      (finalSeats := otherPartySeatCount)
      (startActive := otherStartActive)
      (terminalActive := otherTerminalActive)
      hotherLaw hotherStartCapacity hotherNoquotaOnEliminate hotherReplay
      hotherStartRemaining hotherSteps hotherTerminalNoParty hotherFinal
  exact
    proposition1_seatSharesRounded_of_partyTransferTraceOutcomes_and_pavMinArgmax
      (rule := rule) (partyTrace := partyTrace)
      (otherPartyTrace := otherPartyTrace)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      hpos hle htotal hvoters hpartyOutcome hotherOutcome hpav

/--
Proposition 1 from executable fractional STV prefix traces.

This is the strict source-closure route for the transfer dynamics: the party
source-trace laws, active-set replays, and ordinary step facts are derived from
the executable trace certificate and solid-coalition ballot semantics.
-/
theorem proposition1_seatSharesRounded_of_executableTrace_capacityTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {partyTrace otherPartyTrace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive partyTerminalActive otherTerminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyRun :
      FractionalSTVExecutableTrace rule partyTrace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive partyTerminalActive
        initialWeight)
    (hotherRun :
      FractionalSTVExecutableTrace rule otherPartyTrace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive otherTerminalActive
        initialWeight)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyTracePartyActive :
      ∀ i : Fin partyTrace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (partyTrace.steps.get i).beforeActive)
    (hpartyTraceOtherActive :
      ∀ i : Fin partyTrace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (partyTrace.steps.get i).beforeActive)
    (hotherTracePartyActive :
      ∀ i : Fin otherPartyTrace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (otherPartyTrace.steps.get i).beforeActive)
    (hotherTraceOtherActive :
      ∀ i : Fin otherPartyTrace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (otherPartyTrace.steps.get i).beforeActive)
    (hpartyStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))))
    (hotherStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))))
    (hpartyNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (partyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ))
    (hotherNoquotaOnEliminate :
      ∀ i : Fin otherPartyTrace.steps.length,
        (otherPartyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  (otherPartyTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally (otherPartyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ))
    (hpartyTerminalNoParty :
      activePartyCandidates partyTerminalActive partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates otherTerminalActive otherPartyCandidates = ∅)
    (hpartyFinal :
      partyElectStepCount partyCandidates partyTrace.steps ≤ stvSeatCount)
    (hotherFinal :
      partyElectStepCount otherPartyCandidates otherPartyTrace.steps ≤
        otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hpartyStartRemaining :
      (PartyQuotaStartState partyCandidates.card
        (partyShare * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card := by
    simpa [PartyQuotaStartState] using
      (activePartyCandidates_card_eq_of_subset hpartyInitialActive).symm
  have hotherStartRemaining :
      (PartyQuotaStartState otherPartyCandidates.card
        ((1 - partyShare) * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive otherPartyCandidates).card := by
    simpa [PartyQuotaStartState] using
      (activePartyCandidates_card_eq_of_subset hotherInitialActive).symm
  have hpartyLaw :
      FractionalPartySTVSourceTraceLaw partyCandidates
        (STVQuota seats voters : ℝ) rule.fractionalTally
        partyTrace.steps
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))) :=
    fractionalPartySTVSourceTraceLaw_of_executableTrace_solidCoalition_left
      (rule := rule) (trace := partyTrace)
      (allVoters := allVoters) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := partyShare * (voters : ℝ))
      (initialActive := initialActive)
      (terminalActive := partyTerminalActive)
      (initialWeight := initialWeight)
      (partyInitialWeight := partyInitialWeight)
      hpartyRun hvoterPartition hvoterDisjoint hcandidateDisjoint
      hpartySolid hotherSolid hpartyTracePartyActive hpartyTraceOtherActive
      hpartyInitialWeightEq hpartyInitialMass hpartyStartRemaining
  have hvoterPartition_symm : allVoters = otherPartyVoters ∪ partyVoters := by
    rw [hvoterPartition, Finset.union_comm]
  have hotherLaw :
      FractionalPartySTVSourceTraceLaw otherPartyCandidates
        (STVQuota seats voters : ℝ) rule.fractionalTally
        otherPartyTrace.steps
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) :=
    fractionalPartySTVSourceTraceLaw_of_executableTrace_solidCoalition_left
      (rule := rule) (trace := otherPartyTrace)
      (allVoters := allVoters) (partyVoters := otherPartyVoters)
      (otherPartyVoters := partyVoters) (ballots := ballots)
      (partyCandidates := otherPartyCandidates)
      (otherPartyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := (1 - partyShare) * (voters : ℝ))
      (initialActive := initialActive)
      (terminalActive := otherTerminalActive)
      (initialWeight := initialWeight)
      (partyInitialWeight := otherPartyInitialWeight)
      hotherRun hvoterPartition_symm hvoterDisjoint.symm
      hcandidateDisjoint.symm hotherSolid hpartySolid hotherTraceOtherActive
      hotherTracePartyActive hotherInitialWeightEq hotherInitialMass
      hotherStartRemaining
  have hpartySteps :
      ∀ step, step ∈ partyTrace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    rcases (FractionalSTVExecutableTrace.concreteStepLaw hpartyRun) ⟨n, hn⟩ with
      ⟨hremove, focused, hfocus, hfocused_active, _hnonneg,
        hkind_allowed, _hquota_if_elect⟩
    exact ⟨focused, hfocus, hfocused_active, hremove, hkind_allowed⟩
  have hotherSteps :
      ∀ step, step ∈ otherPartyTrace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    rcases (FractionalSTVExecutableTrace.concreteStepLaw hotherRun) ⟨n, hn⟩ with
      ⟨hremove, focused, hfocus, hfocused_active, _hnonneg,
        hkind_allowed, _hquota_if_elect⟩
    exact ⟨focused, hfocus, hfocused_active, hremove, hkind_allowed⟩
  exact
    proposition1_seatSharesRounded_of_sourceTraceLaw_capacityTerminals_and_pavMinArgmax
      (rule := rule) (partyTrace := partyTrace)
      (otherPartyTrace := otherPartyTrace)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (partyStartActive := initialActive)
      (partyTerminalActive := partyTerminalActive)
      (otherStartActive := initialActive)
      (otherTerminalActive := otherTerminalActive)
      hpos hle htotal hvoters hpartyLaw hpartyStartCapacity
      hpartyNoquotaOnEliminate hpartyRun.activeReplay hpartyStartRemaining
      hpartySteps hpartyTerminalNoParty hpartyFinal hotherLaw
      hotherStartCapacity hotherNoquotaOnEliminate hotherRun.activeReplay
      hotherStartRemaining hotherSteps hotherTerminalNoParty hotherFinal hpav

/--
Proposition 1 from indexed executable fractional STV simulator prefixes.

The indexed simulator supplies the concrete transfer dynamics.  The only
rule-facing obligation is that the paper's transfer-rule tally agrees with the
simulator's round tally on active candidates.
-/
theorem proposition1_seatSharesRounded_of_indexedExecutableTrace_capacityTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {partyTrace otherPartyTrace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive partyTerminalActive otherTerminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyRun :
      FractionalSTVIndexedExecutableTrace partyTrace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive partyTerminalActive
        initialWeight)
    (hotherRun :
      FractionalSTVIndexedExecutableTrace otherPartyTrace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive otherTerminalActive
        initialWeight)
    (hpartyRuleTallyEq :
      ∀ i : Fin partyTrace.steps.length, ∀ candidate,
        candidate ∈ (partyTrace.steps.get i).beforeActive →
          rule.fractionalTally (partyTrace.steps.get i) candidate =
            hpartyRun.roundTally i candidate)
    (hotherRuleTallyEq :
      ∀ i : Fin otherPartyTrace.steps.length, ∀ candidate,
        candidate ∈ (otherPartyTrace.steps.get i).beforeActive →
          rule.fractionalTally (otherPartyTrace.steps.get i) candidate =
            hotherRun.roundTally i candidate)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyTracePartyActive :
      ∀ i : Fin partyTrace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (partyTrace.steps.get i).beforeActive)
    (hpartyTraceOtherActive :
      ∀ i : Fin partyTrace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (partyTrace.steps.get i).beforeActive)
    (hotherTracePartyActive :
      ∀ i : Fin otherPartyTrace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (otherPartyTrace.steps.get i).beforeActive)
    (hotherTraceOtherActive :
      ∀ i : Fin otherPartyTrace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (otherPartyTrace.steps.get i).beforeActive)
    (hpartyStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))))
    (hotherStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))))
    (hpartyRoundNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              hpartyRun.roundTally i candidate < (STVQuota seats voters : ℝ))
    (hotherRoundNoquotaOnEliminate :
      ∀ i : Fin otherPartyTrace.steps.length,
        (otherPartyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  (otherPartyTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              hotherRun.roundTally i candidate < (STVQuota seats voters : ℝ))
    (hpartyTerminalNoParty :
      activePartyCandidates partyTerminalActive partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates otherTerminalActive otherPartyCandidates = ∅)
    (hpartyFinal :
      partyElectStepCount partyCandidates partyTrace.steps ≤ stvSeatCount)
    (hotherFinal :
      partyElectStepCount otherPartyCandidates otherPartyTrace.steps ≤
        otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hpartyExec :
      FractionalSTVExecutableTrace rule partyTrace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive partyTerminalActive
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := rule) hpartyRun hpartyRuleTallyEq
  have hotherExec :
      FractionalSTVExecutableTrace rule otherPartyTrace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive otherTerminalActive
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := rule) hotherRun hotherRuleTallyEq
  have hpartyNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (partyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hactive : candidate ∈ (partyTrace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    rw [hpartyRuleTallyEq i candidate hactive]
    exact hpartyRoundNoquotaOnEliminate i hkind candidate hcandidate
  have hotherNoquotaOnEliminate :
      ∀ i : Fin otherPartyTrace.steps.length,
        (otherPartyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  (otherPartyTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally (otherPartyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hactive : candidate ∈ (otherPartyTrace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    rw [hotherRuleTallyEq i candidate hactive]
    exact hotherRoundNoquotaOnEliminate i hkind candidate hcandidate
  exact
    proposition1_seatSharesRounded_of_executableTrace_capacityTerminals_and_pavMinArgmax
      (rule := rule) (partyTrace := partyTrace)
      (otherPartyTrace := otherPartyTrace)
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (partyTerminalActive := partyTerminalActive)
      (otherTerminalActive := otherTerminalActive)
      initialWeight partyInitialWeight otherPartyInitialWeight
      hpos hle htotal hvoters hpartyExec hotherExec hvoterPartition
      hvoterDisjoint hcandidateDisjoint hpartySolid hotherSolid
      hpartyInitialActive hotherInitialActive hpartyInitialWeightEq
      hotherInitialWeightEq hpartyInitialMass hotherInitialMass
      hpartyTracePartyActive hpartyTraceOtherActive hotherTracePartyActive
      hotherTraceOtherActive hpartyStartCapacity hotherStartCapacity
      hpartyNoquotaOnEliminate hotherNoquotaOnEliminate
      hpartyTerminalNoParty hotherTerminalNoParty hpartyFinal hotherFinal hpav

/--
Proposition 1 from quota-respecting seat-limited fractional STV simulator
prefixes.

The simulator constructs the candidate-level traces and indexed executable
certificates internally. Quota-respecting choice supplies the no-quota facts on
elimination rounds.
-/
theorem proposition1_seatSharesRounded_of_seatRunFractionalSTVTrace_capacityTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {partyRounds otherPartyRounds : ℕ}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hpartyRuleTallyEq :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
            initialWeight).steps.length,
        ∀ candidate,
          candidate ∈
              ((fractionalSTVSeatRunTrace choice allVoters ballots
                (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
                initialWeight).steps.get i).beforeActive →
            rule.fractionalTally
                ((fractionalSTVSeatRunTrace choice allVoters ballots
                  (STVQuota seats voters : ℝ) seats partyRounds 0
                  initialActive initialWeight).steps.get i) candidate =
              fractionalSTVGeneratedRoundTally allVoters ballots
                (STVQuota seats voters : ℝ)
                (fractionalSTVSeatRunFocuses choice allVoters ballots
                  (STVQuota seats voters : ℝ) seats partyRounds 0
                  initialActive initialWeight)
                initialActive initialWeight i candidate)
    (hotherRuleTallyEq :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats otherPartyRounds 0
            initialActive initialWeight).steps.length,
        ∀ candidate,
          candidate ∈
              ((fractionalSTVSeatRunTrace choice allVoters ballots
                (STVQuota seats voters : ℝ) seats otherPartyRounds 0
                initialActive initialWeight).steps.get i).beforeActive →
            rule.fractionalTally
                ((fractionalSTVSeatRunTrace choice allVoters ballots
                  (STVQuota seats voters : ℝ) seats otherPartyRounds 0
                  initialActive initialWeight).steps.get i) candidate =
              fractionalSTVGeneratedRoundTally allVoters ballots
                (STVQuota seats voters : ℝ)
                (fractionalSTVSeatRunFocuses choice allVoters ballots
                  (STVQuota seats voters : ℝ) seats otherPartyRounds 0
                  initialActive initialWeight)
                initialActive initialWeight i candidate)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyTracePartyActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
            initialWeight).steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
              initialWeight).steps.get i).beforeActive)
    (hpartyTraceOtherActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
            initialWeight).steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
              initialWeight).steps.get i).beforeActive)
    (hotherTracePartyActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats otherPartyRounds 0
            initialActive initialWeight).steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) seats otherPartyRounds 0
              initialActive initialWeight).steps.get i).beforeActive)
    (hotherTraceOtherActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats otherPartyRounds 0
            initialActive initialWeight).steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) seats otherPartyRounds 0
              initialActive initialWeight).steps.get i).beforeActive)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyTerminalNoParty :
      activePartyCandidates
          (fractionalSTVSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
            initialWeight)
          partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates
          (fractionalSTVSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) seats otherPartyRounds 0
            initialActive initialWeight)
          otherPartyCandidates = ∅)
    (hpartyFinal :
      partyElectStepCount partyCandidates
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
            initialWeight).steps ≤ stvSeatCount)
    (hotherFinal :
      partyElectStepCount otherPartyCandidates
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats otherPartyRounds 0
            initialActive initialWeight).steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let partyRun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
      initialWeight hquota_pos hinitialWeightNonneg
  let otherRun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) seats otherPartyRounds 0 initialActive
      initialWeight hquota_pos hinitialWeightNonneg
  have hpartyRuleTallyEq' :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
            initialWeight).steps.length,
        ∀ candidate,
          candidate ∈
              ((fractionalSTVSeatRunTrace choice allVoters ballots
                (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
                initialWeight).steps.get i).beforeActive →
            rule.fractionalTally
                ((fractionalSTVSeatRunTrace choice allVoters ballots
                  (STVQuota seats voters : ℝ) seats partyRounds 0
                  initialActive initialWeight).steps.get i) candidate =
              partyRun.roundTally i candidate := by
    intro i candidate hcandidate
    simpa [partyRun, fractionalSTVSeatRunTrace,
      fractionalSTVIndexedExecutableTrace_of_seatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      hpartyRuleTallyEq i candidate hcandidate
  have hotherRuleTallyEq' :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats otherPartyRounds 0
            initialActive initialWeight).steps.length,
        ∀ candidate,
          candidate ∈
              ((fractionalSTVSeatRunTrace choice allVoters ballots
                (STVQuota seats voters : ℝ) seats otherPartyRounds 0
                initialActive initialWeight).steps.get i).beforeActive →
            rule.fractionalTally
                ((fractionalSTVSeatRunTrace choice allVoters ballots
                  (STVQuota seats voters : ℝ) seats otherPartyRounds 0
                  initialActive initialWeight).steps.get i) candidate =
              otherRun.roundTally i candidate := by
    intro i candidate hcandidate
    simpa [otherRun, fractionalSTVSeatRunTrace,
      fractionalSTVIndexedExecutableTrace_of_seatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      hotherRuleTallyEq i candidate hcandidate
  have hpartyRoundNoquotaOnEliminate :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
            initialWeight).steps.length,
        ((fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
          initialWeight).steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((fractionalSTVSeatRunTrace choice allVoters ballots
                    (STVQuota seats voters : ℝ) seats partyRounds 0
                    initialActive initialWeight).steps.get i).beforeActive
                  partyCandidates →
              partyRun.roundTally i candidate < (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hactive :
        candidate ∈
          ((fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
            initialWeight).steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    simpa [partyRun] using
      fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
        choice allVoters ballots (STVQuota seats voters : ℝ) seats
        partyRounds 0 initialActive initialWeight hquota_pos
        hinitialWeightNonneg hchoiceRespect i candidate hactive hkind
  have hotherRoundNoquotaOnEliminate :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats otherPartyRounds 0
            initialActive initialWeight).steps.length,
        ((fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats otherPartyRounds 0 initialActive
          initialWeight).steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((fractionalSTVSeatRunTrace choice allVoters ballots
                    (STVQuota seats voters : ℝ) seats otherPartyRounds 0
                    initialActive initialWeight).steps.get i).beforeActive
                  otherPartyCandidates →
              otherRun.roundTally i candidate < (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hactive :
        candidate ∈
          ((fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats otherPartyRounds 0 initialActive
            initialWeight).steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    simpa [otherRun] using
      fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
        choice allVoters ballots (STVQuota seats voters : ℝ) seats
        otherPartyRounds 0 initialActive initialWeight hquota_pos
        hinitialWeightNonneg hchoiceRespect i candidate hactive hkind
  have hpartyStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))) :=
    partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
      (partyShare := partyShare) hle hpartyCandidates
  have hotherShare_le_one : 1 - partyShare ≤ 1 := by
    nlinarith [hpos]
  have hotherStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) :=
    partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
      (partyShare := 1 - partyShare) hotherShare_le_one
      hotherPartyCandidates
  exact
    proposition1_seatSharesRounded_of_indexedExecutableTrace_capacityTerminals_and_pavMinArgmax
      (rule := rule)
      (partyTrace :=
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
          initialWeight)
      (otherPartyTrace :=
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats otherPartyRounds 0 initialActive
          initialWeight)
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (partyTerminalActive :=
        fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) seats partyRounds 0 initialActive
          initialWeight)
      (otherTerminalActive :=
        fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) seats otherPartyRounds 0 initialActive
          initialWeight)
      initialWeight partyInitialWeight otherPartyInitialWeight hpos hle
      htotal hvoters partyRun otherRun hpartyRuleTallyEq'
      hotherRuleTallyEq' hvoterPartition hvoterDisjoint hcandidateDisjoint
      hpartySolid hotherSolid hpartyInitialActive hotherInitialActive
      hpartyInitialWeightEq hotherInitialWeightEq hpartyInitialMass
      hotherInitialMass hpartyTracePartyActive hpartyTraceOtherActive
      hotherTracePartyActive hotherTraceOtherActive hpartyStartCapacity
      hotherStartCapacity hpartyRoundNoquotaOnEliminate
      hotherRoundNoquotaOnEliminate hpartyTerminalNoParty
      hotherTerminalNoParty hpartyFinal hotherFinal hpav

/--
Proposition 1 from two executable fractional STV prefix traces, allowing the
two generated prefixes to use different step-keyed transfer rules.

This is the reusable bridge used by generated simulators: executable
candidate-level traces, solid-coalition ballots, quota-respecting elimination
facts, and capacity terminal conditions are enough to construct the two party
transfer outcomes consumed by the PAV/STV rounding argument.
-/
theorem proposition1_seatSharesRounded_of_executableTrace_twoRules_capacityTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {partyRule otherPartyRule : FractionalSTVTransferRule Candidate}
    {partyTrace otherPartyTrace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive partyTerminalActive otherTerminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyRun :
      FractionalSTVExecutableTrace partyRule partyTrace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive partyTerminalActive
        initialWeight)
    (hotherRun :
      FractionalSTVExecutableTrace otherPartyRule otherPartyTrace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive otherTerminalActive
        initialWeight)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (_hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              partyRule.fractionalTally (partyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ))
    (hotherNoquotaOnEliminate :
      ∀ i : Fin otherPartyTrace.steps.length,
        (otherPartyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  (otherPartyTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              otherPartyRule.fractionalTally
                  (otherPartyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ))
    (hpartyTerminalNoParty :
      activePartyCandidates partyTerminalActive partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates otherTerminalActive otherPartyCandidates = ∅)
    (hpartyFinal :
      partyElectStepCount partyCandidates partyTrace.steps ≤ stvSeatCount)
    (hotherFinal :
      partyElectStepCount otherPartyCandidates otherPartyTrace.steps ≤
        otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hpartyStartRemaining :
      (PartyQuotaStartState partyCandidates.card
        (partyShare * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card := by
    simpa [PartyQuotaStartState] using
      (activePartyCandidates_card_eq_of_subset hpartyInitialActive).symm
  have hotherStartRemaining :
      (PartyQuotaStartState otherPartyCandidates.card
        ((1 - partyShare) * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive otherPartyCandidates).card := by
    simpa [PartyQuotaStartState] using
      (activePartyCandidates_card_eq_of_subset hotherInitialActive).symm
  have hpartyStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))) :=
    partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
      (partyShare := partyShare) hle hpartyCandidates
  have hotherShare_le_one : 1 - partyShare ≤ 1 := by
    nlinarith [hpos]
  have hotherStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) :=
    partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
      (partyShare := 1 - partyShare) hotherShare_le_one
      hotherPartyCandidates
  have hpartyVoters_subset : partyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union.mpr (Or.inl hvoter)
  have hotherVoters_subset : otherPartyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union.mpr (Or.inr hvoter)
  have hpartyLowerRaw :
      ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ ≤
        stvSeatCount :=
    floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityTerminal
      (rule := partyRule) (trace := partyTrace)
      (allVoters := allVoters) (partyVoters := partyVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := partyShare * (voters : ℝ))
      (finalSeats := stvSeatCount) (initialActive := initialActive)
      (terminalActive := partyTerminalActive)
      (initialWeight := initialWeight)
      (partyInitialWeight := partyInitialWeight) hpartyRun
      hpartySolid hpartyVoters_subset
      hpartyInitialWeightEq hpartyInitialMass hpartyStartCapacity
      hpartyStartRemaining hpartyNoquotaOnEliminate hpartyTerminalNoParty
      hpartyFinal
  have hpartyLower :
      ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤
        stvSeatCount := by
    simpa [mul_div_assoc] using hpartyLowerRaw
  have hotherLowerRaw :
      ⌊((1 - partyShare) * (voters : ℝ)) /
          (STVQuota seats voters : ℝ)⌋₊ ≤
        otherPartySeatCount :=
    floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityTerminal
      (rule := otherPartyRule) (trace := otherPartyTrace)
      (allVoters := allVoters) (partyVoters := otherPartyVoters)
      (ballots := ballots) (partyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := (1 - partyShare) * (voters : ℝ))
      (finalSeats := otherPartySeatCount) (initialActive := initialActive)
      (terminalActive := otherTerminalActive)
      (initialWeight := initialWeight)
      (partyInitialWeight := otherPartyInitialWeight) hotherRun
      hotherSolid hotherVoters_subset
      hotherInitialWeightEq hotherInitialMass hotherStartCapacity
      hotherStartRemaining hotherNoquotaOnEliminate hotherTerminalNoParty
      hotherFinal
  have hotherLower :
      ⌊(1 - partyShare) *
          ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤
        otherPartySeatCount := by
    simpa [mul_div_assoc] using hotherLowerRaw
  exact
    proposition1_seatSharesRounded_of_stvQuotaLowerBounds_and_pavMinArgmax
      hpos hle
      ⟨otherPartySeatCount, htotal, hpos.le, hle, hvoters, hpartyLower,
        hotherLower⟩
      hpav

/--
Proposition 1 from one executable fractional STV trace and two exhausted-party
prefixes.

The final STV seat count is read from the full trace, while each party's quota
lower bound is proved on the prefix at which that party has no active
same-party candidates.  This is the source-shaped bridge needed for total-seat
STV runs where a party may exhaust before the global stopping round.
-/
theorem proposition1_seatSharesRounded_of_executableTrace_prefixTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive terminalActive partyTerminalActive otherTerminalActive :
      Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {partyPrefixLength otherPrefixLength pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hrun :
      FractionalSTVExecutableTrace rule trace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive terminalActive
        initialWeight)
    (hpartyPrefixReplay :
      STVTrace.replayStepsFrom (trace.steps.take partyPrefixLength)
        initialActive partyTerminalActive)
    (hotherPrefixReplay :
      STVTrace.replayStepsFrom (trace.steps.take otherPrefixLength)
        initialActive otherTerminalActive)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyNoquotaOnEliminate :
      ∀ i : Fin (trace.steps.take partyPrefixLength).length,
        ((trace.steps.take partyPrefixLength).get i).kind =
            StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((trace.steps.take partyPrefixLength).get i).beforeActive
                  partyCandidates →
              rule.fractionalTally
                  ((trace.steps.take partyPrefixLength).get i) candidate <
                (STVQuota seats voters : ℝ))
    (hotherNoquotaOnEliminate :
      ∀ i : Fin (trace.steps.take otherPrefixLength).length,
        ((trace.steps.take otherPrefixLength).get i).kind =
            StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((trace.steps.take otherPrefixLength).get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally
                  ((trace.steps.take otherPrefixLength).get i) candidate <
                (STVQuota seats voters : ℝ))
    (hpartyTerminalNoParty :
      activePartyCandidates partyTerminalActive partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates otherTerminalActive otherPartyCandidates = ∅)
    (hseatUpper :
      partyElectStepCount partyCandidates trace.steps +
          partyElectStepCount otherPartyCandidates trace.steps ≤
        seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded (partyElectStepCount partyCandidates trace.steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hpartyStartRemaining :
      (PartyQuotaStartState partyCandidates.card
        (partyShare * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card := by
    simpa [PartyQuotaStartState] using
      (activePartyCandidates_card_eq_of_subset hpartyInitialActive).symm
  have hotherStartRemaining :
      (PartyQuotaStartState otherPartyCandidates.card
        ((1 - partyShare) * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive otherPartyCandidates).card := by
    simpa [PartyQuotaStartState] using
      (activePartyCandidates_card_eq_of_subset hotherInitialActive).symm
  have hpartyStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))) :=
    partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
      (partyShare := partyShare) hle hpartyCandidates
  have hotherShare_le_one : 1 - partyShare ≤ 1 := by
    nlinarith [hpos]
  have hotherStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) :=
    partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
      (partyShare := 1 - partyShare) hotherShare_le_one
      hotherPartyCandidates
  have hpartyVoters_subset : partyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union.mpr (Or.inl hvoter)
  have hotherVoters_subset : otherPartyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union.mpr (Or.inr hvoter)
  have hpartyPrefixFinal :
      partyElectStepCount partyCandidates
          (trace.steps.take partyPrefixLength) ≤
        partyElectStepCount partyCandidates trace.steps :=
    partyElectStepCount_take_le partyCandidates trace.steps partyPrefixLength
  have hotherPrefixFinal :
      partyElectStepCount otherPartyCandidates
          (trace.steps.take otherPrefixLength) ≤
        partyElectStepCount otherPartyCandidates trace.steps :=
    partyElectStepCount_take_le otherPartyCandidates trace.steps
      otherPrefixLength
  have hpartyLowerRaw :
      ⌊(partyShare * (voters : ℝ)) / (STVQuota seats voters : ℝ)⌋₊ ≤
        partyElectStepCount partyCandidates trace.steps :=
    floor_votes_div_quota_le_finalSeats_of_executableTrace_take_solidCoalition_left_lowerBound_capacityTerminal
      (rule := rule) (trace := trace)
      (allVoters := allVoters) (partyVoters := partyVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := partyShare * (voters : ℝ))
      (finalSeats := partyElectStepCount partyCandidates trace.steps)
      (n := partyPrefixLength) (initialActive := initialActive)
      (terminalActive := terminalActive)
      (prefixTerminalActive := partyTerminalActive)
      (initialWeight := initialWeight)
      (partyInitialWeight := partyInitialWeight) hrun hpartyPrefixReplay
      hpartySolid hpartyVoters_subset hpartyInitialWeightEq
      hpartyInitialMass hpartyStartCapacity hpartyStartRemaining
      hpartyNoquotaOnEliminate hpartyTerminalNoParty hpartyPrefixFinal
  have hpartyLower :
      ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤
        partyElectStepCount partyCandidates trace.steps := by
    simpa [mul_div_assoc] using hpartyLowerRaw
  have hotherLowerRaw :
      ⌊((1 - partyShare) * (voters : ℝ)) /
          (STVQuota seats voters : ℝ)⌋₊ ≤
        partyElectStepCount otherPartyCandidates trace.steps :=
    floor_votes_div_quota_le_finalSeats_of_executableTrace_take_solidCoalition_left_lowerBound_capacityTerminal
      (rule := rule) (trace := trace)
      (allVoters := allVoters) (partyVoters := otherPartyVoters)
      (ballots := ballots) (partyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := (1 - partyShare) * (voters : ℝ))
      (finalSeats := partyElectStepCount otherPartyCandidates trace.steps)
      (n := otherPrefixLength) (initialActive := initialActive)
      (terminalActive := terminalActive)
      (prefixTerminalActive := otherTerminalActive)
      (initialWeight := initialWeight)
      (partyInitialWeight := otherPartyInitialWeight) hrun hotherPrefixReplay
      hotherSolid hotherVoters_subset hotherInitialWeightEq
      hotherInitialMass hotherStartCapacity hotherStartRemaining
      hotherNoquotaOnEliminate hotherTerminalNoParty hotherPrefixFinal
  have hotherLower :
      ⌊(1 - partyShare) *
          ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤
        partyElectStepCount otherPartyCandidates trace.steps := by
    simpa [mul_div_assoc] using hotherLowerRaw
  have hpartyFloorLower :
      ⌊partyShare * (seats : ℝ)⌋₊ ≤
        partyElectStepCount partyCandidates trace.steps :=
    le_trans
      (floor_partyShare_mul_seats_le_floor_partyShare_mul_voters_div_quota
        (seats := seats) (voters := voters) (partyShare := partyShare)
        hpos.le hvoters)
      hpartyLower
  have hotherFloorLower :
      ⌊(1 - partyShare) * (seats : ℝ)⌋₊ ≤
        partyElectStepCount otherPartyCandidates trace.steps :=
    le_trans
      (floor_partyShare_mul_seats_le_floor_partyShare_mul_voters_div_quota
        (seats := seats) (voters := voters) (partyShare := 1 - partyShare)
        (sub_nonneg.mpr hle) hvoters)
      hotherLower
  exact
    proposition1_seatSharesRounded_of_stvBounds_and_pavMinArgmax
      hpos hle
      (stvSeatShareBounds_of_twoPartyLowerBounds_le_total hseatUpper
        hpartyFloorLower hotherFloorLower)
      hpav

/--
Proposition 1 from one executable fractional STV trace and two indexed
exhausted-party prefixes.

Compared with
`proposition1_seatSharesRounded_of_executableTrace_prefixTerminals_and_pavMinArgmax`,
the prefix replay facts are no longer assumptions: they are derived from the
candidate-level executable trace at the supplied source-step indices.
-/
theorem proposition1_seatSharesRounded_of_executableTrace_prefixIndices_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive terminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {partyPrefixIndex otherPrefixIndex : Fin trace.steps.length}
    {pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hrun :
      FractionalSTVExecutableTrace rule trace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive terminalActive
        initialWeight)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyNoquotaOnEliminate :
      ∀ i : Fin (trace.steps.take partyPrefixIndex.1).length,
        ((trace.steps.take partyPrefixIndex.1).get i).kind =
            StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((trace.steps.take partyPrefixIndex.1).get i).beforeActive
                  partyCandidates →
              rule.fractionalTally
                  ((trace.steps.take partyPrefixIndex.1).get i) candidate <
                (STVQuota seats voters : ℝ))
    (hotherNoquotaOnEliminate :
      ∀ i : Fin (trace.steps.take otherPrefixIndex.1).length,
        ((trace.steps.take otherPrefixIndex.1).get i).kind =
            StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((trace.steps.take otherPrefixIndex.1).get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally
                  ((trace.steps.take otherPrefixIndex.1).get i) candidate <
                (STVQuota seats voters : ℝ))
    (hpartyTerminalNoParty :
      activePartyCandidates (trace.steps.get partyPrefixIndex).beforeActive
        partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates (trace.steps.get otherPrefixIndex).beforeActive
        otherPartyCandidates = ∅)
    (hseatUpper :
      partyElectStepCount partyCandidates trace.steps +
          partyElectStepCount otherPartyCandidates trace.steps ≤
        seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded (partyElectStepCount partyCandidates trace.steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  exact
    proposition1_seatSharesRounded_of_executableTrace_prefixTerminals_and_pavMinArgmax
      (rule := rule) (trace := trace)
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) (terminalActive := terminalActive)
      (partyTerminalActive := (trace.steps.get partyPrefixIndex).beforeActive)
      (otherTerminalActive := (trace.steps.get otherPrefixIndex).beforeActive)
      initialWeight partyInitialWeight otherPartyInitialWeight
      (partyPrefixLength := partyPrefixIndex.1)
      (otherPrefixLength := otherPrefixIndex.1)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hvoters hpartyCandidates
      hotherPartyCandidates hrun
      (FractionalSTVExecutableTrace.prefixReplay hrun partyPrefixIndex)
      (FractionalSTVExecutableTrace.prefixReplay hrun otherPrefixIndex)
      hvoterPartition hvoterDisjoint hpartySolid hotherSolid
      hpartyInitialActive hotherInitialActive hpartyInitialWeightEq
      hotherInitialWeightEq hpartyInitialMass hotherInitialMass
      hpartyNoquotaOnEliminate hotherNoquotaOnEliminate
      hpartyTerminalNoParty hotherTerminalNoParty hseatUpper hpav

/--
Proposition 1 from a quota-respecting total-seat fractional STV simulator run
and exhausted-party prefixes.

The full trace is generated by the concrete seat-limited simulator.  The
quota-respecting choice rule supplies the no-quota facts on elimination rounds;
the caller supplies the source prefix at which each party has no active
same-party candidates.
-/
theorem proposition1_seatSharesRounded_of_seatRunFractionalSTVTrace_prefixTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive partyTerminalActive otherTerminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {rounds partyPrefixLength otherPrefixLength pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hpartyPrefixReplay :
      STVTrace.replayStepsFrom
        ((fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight).steps.take partyPrefixLength)
        initialActive partyTerminalActive)
    (hotherPrefixReplay :
      STVTrace.replayStepsFrom
        ((fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight).steps.take otherPrefixLength)
        initialActive otherTerminalActive)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyTerminalNoParty :
      activePartyCandidates partyTerminalActive partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates otherTerminalActive otherPartyCandidates = ∅)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded
        (partyElectStepCount partyCandidates
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight).steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let focuses :=
    fractionalSTVSeatRunFocuses choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
  let trace :=
    fractionalSTVSeatRunTrace choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
  let rule :=
    fractionalSTVGeneratedTransferRule allVoters ballots
      (STVQuota seats voters : ℝ) focuses initialActive initialWeight
  let indexedRun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
      hquota_pos hinitialWeightNonneg
  have hruleTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈ (trace.steps.get i).beforeActive →
          rule.fractionalTally (trace.steps.get i) candidate =
            indexedRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [trace, rule, indexedRun, focuses, fractionalSTVSeatRunTrace,
      fractionalSTVIndexedExecutableTrace_of_seatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots
        (STVQuota seats voters : ℝ) focuses initialActive initialWeight
        i candidate
  have hexec :
      FractionalSTVExecutableTrace rule trace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive
        (fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := rule) indexedRun hruleTallyEq
  have hpartyNoquotaOnEliminate :
      ∀ i : Fin (trace.steps.take partyPrefixLength).length,
        ((trace.steps.take partyPrefixLength).get i).kind =
            StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((trace.steps.take partyPrefixLength).get i).beforeActive
                  partyCandidates →
              rule.fractionalTally
                  ((trace.steps.take partyPrefixLength).get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hlen : (trace.steps.take partyPrefixLength).length ≤
        trace.steps.length := by
      simp [List.length_take]
    have hi : i.1 < trace.steps.length := lt_of_lt_of_le i.2 hlen
    have hkind_full :
        (trace.steps.get ⟨i.1, hi⟩).kind = StepKind.eliminate := by
      simpa [List.get_eq_getElem, List.getElem_take] using hkind
    have hactive_full :
        candidate ∈ (trace.steps.get ⟨i.1, hi⟩).beforeActive := by
      simpa [List.get_eq_getElem, List.getElem_take] using
        (Finset.mem_filter.mp hcandidate).1
    have hround_lt :
        indexedRun.roundTally ⟨i.1, hi⟩ candidate <
          (STVQuota seats voters : ℝ) := by
      simpa [trace, indexedRun] using
        fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
          choice allVoters ballots (STVQuota seats voters : ℝ) seats rounds
          0 initialActive initialWeight hquota_pos hinitialWeightNonneg
          hchoiceRespect ⟨i.1, hi⟩ candidate hactive_full hkind_full
    have hrule_lt :
        rule.fractionalTally (trace.steps.get ⟨i.1, hi⟩) candidate <
          (STVQuota seats voters : ℝ) := by
      rw [hruleTallyEq ⟨i.1, hi⟩ candidate hactive_full]
      exact hround_lt
    simpa [List.get_eq_getElem, List.getElem_take] using hrule_lt
  have hotherNoquotaOnEliminate :
      ∀ i : Fin (trace.steps.take otherPrefixLength).length,
        ((trace.steps.take otherPrefixLength).get i).kind =
            StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((trace.steps.take otherPrefixLength).get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally
                  ((trace.steps.take otherPrefixLength).get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hlen : (trace.steps.take otherPrefixLength).length ≤
        trace.steps.length := by
      simp [List.length_take]
    have hi : i.1 < trace.steps.length := lt_of_lt_of_le i.2 hlen
    have hkind_full :
        (trace.steps.get ⟨i.1, hi⟩).kind = StepKind.eliminate := by
      simpa [List.get_eq_getElem, List.getElem_take] using hkind
    have hactive_full :
        candidate ∈ (trace.steps.get ⟨i.1, hi⟩).beforeActive := by
      simpa [List.get_eq_getElem, List.getElem_take] using
        (Finset.mem_filter.mp hcandidate).1
    have hround_lt :
        indexedRun.roundTally ⟨i.1, hi⟩ candidate <
          (STVQuota seats voters : ℝ) := by
      simpa [trace, indexedRun] using
        fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
          choice allVoters ballots (STVQuota seats voters : ℝ) seats rounds
          0 initialActive initialWeight hquota_pos hinitialWeightNonneg
          hchoiceRespect ⟨i.1, hi⟩ candidate hactive_full hkind_full
    have hrule_lt :
        rule.fractionalTally (trace.steps.get ⟨i.1, hi⟩) candidate <
          (STVQuota seats voters : ℝ) := by
      rw [hruleTallyEq ⟨i.1, hi⟩ candidate hactive_full]
      exact hround_lt
    simpa [List.get_eq_getElem, List.getElem_take] using hrule_lt
  have hpartyOtherLeElect :
      partyElectStepCount partyCandidates trace.steps +
          partyElectStepCount otherPartyCandidates trace.steps ≤
        electStepCount trace.steps :=
    partyElectStepCount_add_le_electStepCount_of_disjoint
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      hcandidateDisjoint trace.steps
  have helectLeSeats :
      electStepCount trace.steps ≤ seats := by
    simpa [trace] using
      electStepCount_fractionalSTVSeatRunTrace_le_seatLimit choice allVoters
        ballots (STVQuota seats voters : ℝ) seats rounds initialActive
        initialWeight
  have hseatUpper :
      partyElectStepCount partyCandidates trace.steps +
          partyElectStepCount otherPartyCandidates trace.steps ≤ seats :=
    le_trans hpartyOtherLeElect helectLeSeats
  exact
    proposition1_seatSharesRounded_of_executableTrace_prefixTerminals_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (allVoters := allVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (terminalActive :=
        fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      (partyTerminalActive := partyTerminalActive)
      (otherTerminalActive := otherTerminalActive)
      initialWeight partyInitialWeight otherPartyInitialWeight
      (partyPrefixLength := partyPrefixLength)
      (otherPrefixLength := otherPrefixLength)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hvoters hpartyCandidates
      hotherPartyCandidates hexec
      (by simpa [trace] using hpartyPrefixReplay)
      (by simpa [trace] using hotherPrefixReplay)
      hvoterPartition hvoterDisjoint hpartySolid hotherSolid
      hpartyInitialActive hotherInitialActive hpartyInitialWeightEq
      hotherInitialWeightEq hpartyInitialMass hotherInitialMass
      hpartyNoquotaOnEliminate hotherNoquotaOnEliminate
      hpartyTerminalNoParty hotherTerminalNoParty
      hseatUpper hpav

/--
Proposition 1 from a quota-respecting total-seat fractional STV simulator run
whose terminal active set exhausts both parties.

The replay premises of the prefix-terminal theorem are derived from the
generated trace itself by taking the full generated trace as the prefix.
-/
theorem proposition1_seatSharesRounded_of_seatRunFractionalSTVTrace_terminalExhaustion_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {rounds pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyTerminalNoParty :
      activePartyCandidates
          (fractionalSTVSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight)
          partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates
          (fractionalSTVSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight)
          otherPartyCandidates = ∅)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded
        (partyElectStepCount partyCandidates
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight).steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  let focuses :=
    fractionalSTVSeatRunFocuses choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
  let trace :=
    fractionalSTVSeatRunTrace choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
  let terminalActive :=
    fractionalSTVSeatRunTerminalActive choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
  have hreplay :
      STVTrace.replayStepsFrom (trace.steps.take trace.steps.length)
        initialActive terminalActive := by
    simpa [trace, terminalActive, focuses, fractionalSTVSeatRunTrace,
      fractionalSTVGeneratedTrace, fractionalSTVSeatRunTerminalActive] using
      fractionalSTVGeneratedSteps_replayStepsFrom allVoters ballots
        (STVQuota seats voters : ℝ) focuses initialActive initialWeight
  simpa [trace, terminalActive] using
    (proposition1_seatSharesRounded_of_seatRunFractionalSTVTrace_prefixTerminals_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) choice
      (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (allVoters := allVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (partyTerminalActive := terminalActive)
      (otherTerminalActive := terminalActive)
      initialWeight partyInitialWeight otherPartyInitialWeight
      (rounds := rounds) (partyPrefixLength := trace.steps.length)
      (otherPrefixLength := trace.steps.length)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hvoters hinitialWeightNonneg
      hchoiceRespect hreplay hreplay hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartySolid hotherSolid hpartyInitialActive
      hotherInitialActive hpartyInitialWeightEq hotherInitialWeightEq
      hpartyInitialMass hotherInitialMass hpartyCandidates
      hotherPartyCandidates
      (by simpa [terminalActive] using hpartyTerminalNoParty)
      (by simpa [terminalActive] using hotherTerminalNoParty) hpav)

/--
Proposition 1 from a quota-respecting total-seat fractional STV simulator run
and indexed exhausted-party prefixes.

The source model identifies the generated trace and the concrete source-step
indices whose `beforeActive` sets have no remaining same-party candidates. The
active-set replay for each prefix is derived from the simulator's executable
trace rather than supplied as a paper-facing premise.
-/
theorem proposition1_seatSharesRounded_of_seatRunFractionalSTVTrace_prefixIndices_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (rounds : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {partyPrefixIndex otherPrefixIndex : Fin trace.steps.length}
    {pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (htrace_seat :
      trace =
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyTerminalNoParty :
      activePartyCandidates (trace.steps.get partyPrefixIndex).beforeActive
        partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates (trace.steps.get otherPrefixIndex).beforeActive
        otherPartyCandidates = ∅)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded (partyElectStepCount partyCandidates trace.steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  subst trace
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let focuses :=
    fractionalSTVSeatRunFocuses choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
  let trace :=
    fractionalSTVSeatRunTrace choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
  let rule :=
    fractionalSTVGeneratedTransferRule allVoters ballots
      (STVQuota seats voters : ℝ) focuses initialActive initialWeight
  let indexedRun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
      hquota_pos hinitialWeightNonneg
  have hruleTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈ (trace.steps.get i).beforeActive →
          rule.fractionalTally (trace.steps.get i) candidate =
            indexedRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [trace, rule, indexedRun, focuses, fractionalSTVSeatRunTrace,
      fractionalSTVIndexedExecutableTrace_of_seatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots
        (STVQuota seats voters : ℝ) focuses initialActive initialWeight
        i candidate
  have hexec :
      FractionalSTVExecutableTrace rule trace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive
        (fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := rule) indexedRun hruleTallyEq
  have hfullNoquotaOnEliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈ (trace.steps.get i).beforeActive →
              rule.fractionalTally (trace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hround_lt :
        indexedRun.roundTally i candidate < (STVQuota seats voters : ℝ) := by
      simpa [trace, indexedRun] using
        fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
          choice allVoters ballots (STVQuota seats voters : ℝ) seats rounds
          0 initialActive initialWeight hquota_pos hinitialWeightNonneg
          hchoiceRespect i candidate hcandidate hkind
    rw [hruleTallyEq i candidate hcandidate]
    exact hround_lt
  have hpartyNoquotaFull :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (trace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (trace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    exact hfullNoquotaOnEliminate i hkind candidate
      (Finset.mem_filter.mp hcandidate).1
  have hotherNoquotaFull :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (trace.steps.get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally (trace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    exact hfullNoquotaOnEliminate i hkind candidate
      (Finset.mem_filter.mp hcandidate).1
  have hpartyNoquotaOnEliminate :
      ∀ i : Fin (trace.steps.take partyPrefixIndex.1).length,
        ((trace.steps.take partyPrefixIndex.1).get i).kind =
            StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((trace.steps.take partyPrefixIndex.1).get i).beforeActive
                  partyCandidates →
              rule.fractionalTally
                  ((trace.steps.take partyPrefixIndex.1).get i) candidate <
                (STVQuota seats voters : ℝ) :=
    noquotaOnEliminate_take_of_noquotaOnEliminate
      (rule := rule) (steps := trace.steps)
      (partyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (n := partyPrefixIndex.1) hpartyNoquotaFull
  have hotherNoquotaOnEliminate :
      ∀ i : Fin (trace.steps.take otherPrefixIndex.1).length,
        ((trace.steps.take otherPrefixIndex.1).get i).kind =
            StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates
                  ((trace.steps.take otherPrefixIndex.1).get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally
                  ((trace.steps.take otherPrefixIndex.1).get i) candidate <
                (STVQuota seats voters : ℝ) :=
    noquotaOnEliminate_take_of_noquotaOnEliminate
      (rule := rule) (steps := trace.steps)
      (partyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (n := otherPrefixIndex.1) hotherNoquotaFull
  have hpartyOtherLeElect :
      partyElectStepCount partyCandidates trace.steps +
          partyElectStepCount otherPartyCandidates trace.steps ≤
        electStepCount trace.steps :=
    partyElectStepCount_add_le_electStepCount_of_disjoint
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      hcandidateDisjoint trace.steps
  have helectLeSeats :
      electStepCount trace.steps ≤ seats := by
    simpa [trace] using
      electStepCount_fractionalSTVSeatRunTrace_le_seatLimit choice allVoters
        ballots (STVQuota seats voters : ℝ) seats rounds initialActive
        initialWeight
  have hseatUpper :
      partyElectStepCount partyCandidates trace.steps +
          partyElectStepCount otherPartyCandidates trace.steps ≤ seats :=
    le_trans hpartyOtherLeElect helectLeSeats
  exact
    proposition1_seatSharesRounded_of_executableTrace_prefixIndices_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (allVoters := allVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (terminalActive :=
        fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      initialWeight partyInitialWeight otherPartyInitialWeight
      (partyPrefixIndex := partyPrefixIndex)
      (otherPrefixIndex := otherPrefixIndex)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hvoters hpartyCandidates
      hotherPartyCandidates hexec hvoterPartition hvoterDisjoint
      hpartySolid hotherSolid hpartyInitialActive hotherInitialActive
      hpartyInitialWeightEq hotherInitialWeightEq hpartyInitialMass
      hotherInitialMass hpartyNoquotaOnEliminate hotherNoquotaOnEliminate
      (by simpa [trace] using hpartyTerminalNoParty)
      (by simpa [trace] using hotherTerminalNoParty)
      hseatUpper hpav

/--
Proposition 1 from quota-respecting seat-limited fractional STV simulator
prefixes, with the transfer-rule interpretation generated internally from
each simulator prefix.

This removes the paper-facing round-tally agreement premise: the concrete
transfer rule used for each prefix is the one induced by that generated
candidate trace.
-/
theorem proposition1_seatSharesRounded_of_generatedSeatRunFractionalSTVTrace_capacityTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {partyRounds otherPartyRounds : ℕ}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyTracePartyActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0
            initialActive initialWeight).steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0
              initialActive initialWeight).steps.get i).beforeActive)
    (hpartyTraceOtherActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0
            initialActive initialWeight).steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0
              initialActive initialWeight).steps.get i).beforeActive)
    (hotherTracePartyActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) otherPartySeatCount otherPartyRounds 0
            initialActive initialWeight).steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) otherPartySeatCount
              otherPartyRounds 0 initialActive initialWeight).steps.get i).beforeActive)
    (hotherTraceOtherActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) otherPartySeatCount otherPartyRounds 0
            initialActive initialWeight).steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) otherPartySeatCount
              otherPartyRounds 0 initialActive initialWeight).steps.get i).beforeActive)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyTerminalNoParty :
      activePartyCandidates
          (fractionalSTVSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0
            initialActive initialWeight)
          partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates
          (fractionalSTVSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) otherPartySeatCount
            otherPartyRounds 0 initialActive initialWeight)
          otherPartyCandidates = ∅)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let partyFocuses :=
    fractionalSTVSeatRunFocuses choice allVoters ballots
      (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0 initialActive
      initialWeight
  let otherFocuses :=
    fractionalSTVSeatRunFocuses choice allVoters ballots
      (STVQuota seats voters : ℝ) otherPartySeatCount otherPartyRounds 0
      initialActive initialWeight
  let partyTrace :=
    fractionalSTVSeatRunTrace choice allVoters ballots
      (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0 initialActive
      initialWeight
  let otherTrace :=
    fractionalSTVSeatRunTrace choice allVoters ballots
      (STVQuota seats voters : ℝ) otherPartySeatCount otherPartyRounds 0
      initialActive initialWeight
  let partyRule :=
    fractionalSTVGeneratedTransferRule allVoters ballots
      (STVQuota seats voters : ℝ) partyFocuses initialActive initialWeight
  let otherRule :=
    fractionalSTVGeneratedTransferRule allVoters ballots
      (STVQuota seats voters : ℝ) otherFocuses initialActive initialWeight
  let partyRun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0 initialActive
      initialWeight hquota_pos hinitialWeightNonneg
  let otherRun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) otherPartySeatCount otherPartyRounds 0
      initialActive initialWeight hquota_pos hinitialWeightNonneg
  have hpartyRuleTallyEq :
      ∀ i : Fin partyTrace.steps.length, ∀ candidate,
        candidate ∈ (partyTrace.steps.get i).beforeActive →
          partyRule.fractionalTally (partyTrace.steps.get i) candidate =
            partyRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [partyTrace, partyRule, partyRun, partyFocuses,
      fractionalSTVSeatRunTrace, fractionalSTVIndexedExecutableTrace_of_seatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots
        (STVQuota seats voters : ℝ) partyFocuses initialActive initialWeight
        i candidate
  have hotherRuleTallyEq :
      ∀ i : Fin otherTrace.steps.length, ∀ candidate,
        candidate ∈ (otherTrace.steps.get i).beforeActive →
          otherRule.fractionalTally (otherTrace.steps.get i) candidate =
            otherRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [otherTrace, otherRule, otherRun, otherFocuses,
      fractionalSTVSeatRunTrace, fractionalSTVIndexedExecutableTrace_of_seatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots
        (STVQuota seats voters : ℝ) otherFocuses initialActive initialWeight
        i candidate
  have hpartyExec :
      FractionalSTVExecutableTrace partyRule partyTrace allVoters ballots
        (STVQuota seats voters : ℝ)
        initialActive
        (fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0
          initialActive initialWeight)
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := partyRule) partyRun hpartyRuleTallyEq
  have hotherExec :
      FractionalSTVExecutableTrace otherRule otherTrace allVoters ballots
        (STVQuota seats voters : ℝ)
        initialActive
        (fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) otherPartySeatCount otherPartyRounds 0
          initialActive initialWeight)
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := otherRule) otherRun hotherRuleTallyEq
  have hpartyRoundNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              partyRun.roundTally i candidate < (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hactive : candidate ∈ (partyTrace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    simpa [partyTrace, partyRun] using
      fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
        choice allVoters ballots (STVQuota seats voters : ℝ) stvSeatCount
        partyRounds 0 initialActive initialWeight hquota_pos
        hinitialWeightNonneg hchoiceRespect i candidate hactive hkind
  have hotherRoundNoquotaOnEliminate :
      ∀ i : Fin otherTrace.steps.length,
        (otherTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (otherTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              otherRun.roundTally i candidate < (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hactive : candidate ∈ (otherTrace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    simpa [otherTrace, otherRun] using
      fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
        choice allVoters ballots (STVQuota seats voters : ℝ)
        otherPartySeatCount otherPartyRounds 0 initialActive initialWeight hquota_pos
        hinitialWeightNonneg hchoiceRespect i candidate hactive hkind
  have hpartyNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              partyRule.fractionalTally (partyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    rw [hpartyRuleTallyEq i candidate (Finset.mem_filter.mp hcandidate).1]
    exact hpartyRoundNoquotaOnEliminate i hkind candidate hcandidate
  have hotherNoquotaOnEliminate :
      ∀ i : Fin otherTrace.steps.length,
        (otherTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (otherTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              otherRule.fractionalTally (otherTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    rw [hotherRuleTallyEq i candidate (Finset.mem_filter.mp hcandidate).1]
    exact hotherRoundNoquotaOnEliminate i hkind candidate hcandidate
  have hpartyStartRemaining :
      (PartyQuotaStartState partyCandidates.card
        (partyShare * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card := by
    simpa [PartyQuotaStartState] using
      (activePartyCandidates_card_eq_of_subset hpartyInitialActive).symm
  have hotherStartRemaining :
      (PartyQuotaStartState otherPartyCandidates.card
        ((1 - partyShare) * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive otherPartyCandidates).card := by
    simpa [PartyQuotaStartState] using
      (activePartyCandidates_card_eq_of_subset hotherInitialActive).symm
  have hpartyStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))) :=
    partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
      (partyShare := partyShare) hle hpartyCandidates
  have hotherShare_le_one : 1 - partyShare ≤ 1 := by
    nlinarith [hpos]
  have hotherStartCapacity :
      PartyQuotaCapacityBound (STVQuota seats voters : ℝ)
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) :=
    partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
      (partyShare := 1 - partyShare) hotherShare_le_one
      hotherPartyCandidates
  have hvoterPartition_symm : allVoters = otherPartyVoters ∪ partyVoters := by
    rw [hvoterPartition, Finset.union_comm]
  have hpartyFinal :
      partyElectStepCount partyCandidates partyTrace.steps ≤ stvSeatCount := by
    simpa [partyTrace] using
      partyElectStepCount_fractionalSTVSeatRunTrace_le_seatLimit
        choice allVoters ballots (STVQuota seats voters : ℝ) stvSeatCount
        partyRounds initialActive initialWeight partyCandidates
  have hotherFinal :
      partyElectStepCount otherPartyCandidates otherTrace.steps ≤
        otherPartySeatCount := by
    simpa [otherTrace] using
      partyElectStepCount_fractionalSTVSeatRunTrace_le_seatLimit
        choice allVoters ballots (STVQuota seats voters : ℝ)
        otherPartySeatCount otherPartyRounds initialActive initialWeight
        otherPartyCandidates
  have hpartyOutcome :
      PartyTransferPreservationTraceOutcome partyRule partyTrace
        partyCandidates (partyShare * (voters : ℝ))
        (STVQuota seats voters : ℝ) stvSeatCount :=
    partyTransferPreservationTraceOutcome_of_executableTrace_solidCoalition_left_capacityTerminal
      (rule := partyRule) (trace := partyTrace)
      (allVoters := allVoters) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := partyShare * (voters : ℝ))
      (finalSeats := stvSeatCount) (initialActive := initialActive)
      (terminalActive :=
        fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) stvSeatCount partyRounds 0
          initialActive initialWeight)
      (initialWeight := initialWeight)
      (partyInitialWeight := partyInitialWeight) hpartyExec
      hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
      hotherSolid hpartyTracePartyActive hpartyTraceOtherActive
      hpartyInitialWeightEq hpartyInitialMass hpartyStartCapacity
      hpartyStartRemaining hpartyNoquotaOnEliminate hpartyTerminalNoParty
      hpartyFinal
  have hotherOutcome :
      PartyTransferPreservationTraceOutcome otherRule otherTrace
        otherPartyCandidates ((1 - partyShare) * (voters : ℝ))
        (STVQuota seats voters : ℝ) otherPartySeatCount :=
    partyTransferPreservationTraceOutcome_of_executableTrace_solidCoalition_left_capacityTerminal
      (rule := otherRule) (trace := otherTrace)
      (allVoters := allVoters) (partyVoters := otherPartyVoters)
      (otherPartyVoters := partyVoters) (ballots := ballots)
      (partyCandidates := otherPartyCandidates)
      (otherPartyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := (1 - partyShare) * (voters : ℝ))
      (finalSeats := otherPartySeatCount) (initialActive := initialActive)
      (terminalActive :=
        fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) otherPartySeatCount otherPartyRounds 0
          initialActive initialWeight)
      (initialWeight := initialWeight)
      (partyInitialWeight := otherPartyInitialWeight) hotherExec
      hvoterPartition_symm hvoterDisjoint.symm hcandidateDisjoint.symm
      hotherSolid hpartySolid hotherTraceOtherActive hotherTracePartyActive
      hotherInitialWeightEq hotherInitialMass hotherStartCapacity
      hotherStartRemaining hotherNoquotaOnEliminate hotherTerminalNoParty
      hotherFinal
  exact
    proposition1_seatSharesRounded_of_partyTransferTraceOutcomes_twoRules_and_pavMinArgmax
      (partyRule := partyRule) (otherPartyRule := otherRule)
      (partyTrace := partyTrace) (otherPartyTrace := otherTrace)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      hpos hle htotal hvoters hpartyOutcome hotherOutcome hpav

/--
Proposition 1 from party-seat-limited generated fractional STV simulator
prefixes.

The generated party prefix stops only after the named party has reached its
claimed STV seat count, so the final-count inclusion used by the
solid-coalition quota process is derived from the executable simulator rather
than supplied as a theorem premise.
-/
theorem proposition1_seatSharesRounded_of_generatedPartySeatRunFractionalSTVTrace_capacityTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {partyRounds otherPartyRounds : ℕ}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyTerminalNoParty :
      activePartyCandidates
          (fractionalSTVPartySeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) partyCandidates stvSeatCount
            partyRounds 0 initialActive initialWeight)
          partyCandidates = ∅)
    (hotherTerminalNoParty :
      activePartyCandidates
          (fractionalSTVPartySeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) otherPartyCandidates
            otherPartySeatCount otherPartyRounds 0 initialActive
            initialWeight)
          otherPartyCandidates = ∅)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let partyFocuses :=
    fractionalSTVPartySeatRunFocuses choice allVoters ballots
      (STVQuota seats voters : ℝ) partyCandidates stvSeatCount
      partyRounds 0 initialActive initialWeight
  let otherFocuses :=
    fractionalSTVPartySeatRunFocuses choice allVoters ballots
      (STVQuota seats voters : ℝ) otherPartyCandidates otherPartySeatCount
      otherPartyRounds 0 initialActive initialWeight
  let partyTrace :=
    fractionalSTVPartySeatRunTrace choice allVoters ballots
      (STVQuota seats voters : ℝ) partyCandidates stvSeatCount
      partyRounds 0 initialActive initialWeight
  let otherTrace :=
    fractionalSTVPartySeatRunTrace choice allVoters ballots
      (STVQuota seats voters : ℝ) otherPartyCandidates otherPartySeatCount
      otherPartyRounds 0 initialActive initialWeight
  let partyRule :=
    fractionalSTVGeneratedTransferRule allVoters ballots
      (STVQuota seats voters : ℝ) partyFocuses initialActive initialWeight
  let otherRule :=
    fractionalSTVGeneratedTransferRule allVoters ballots
      (STVQuota seats voters : ℝ) otherFocuses initialActive initialWeight
  let partyRun :=
    fractionalSTVIndexedExecutableTrace_of_partySeatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) partyCandidates stvSeatCount partyRounds 0
      initialActive initialWeight hquota_pos hinitialWeightNonneg
  let otherRun :=
    fractionalSTVIndexedExecutableTrace_of_partySeatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) otherPartyCandidates otherPartySeatCount
      otherPartyRounds 0 initialActive initialWeight hquota_pos
      hinitialWeightNonneg
  have hpartyRuleTallyEq :
      ∀ i : Fin partyTrace.steps.length, ∀ candidate,
        candidate ∈ (partyTrace.steps.get i).beforeActive →
          partyRule.fractionalTally (partyTrace.steps.get i) candidate =
            partyRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [partyTrace, partyRule, partyRun, partyFocuses,
      fractionalSTVPartySeatRunTrace,
      fractionalSTVIndexedExecutableTrace_of_partySeatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots
        (STVQuota seats voters : ℝ) partyFocuses initialActive initialWeight
        i candidate
  have hotherRuleTallyEq :
      ∀ i : Fin otherTrace.steps.length, ∀ candidate,
        candidate ∈ (otherTrace.steps.get i).beforeActive →
          otherRule.fractionalTally (otherTrace.steps.get i) candidate =
            otherRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [otherTrace, otherRule, otherRun, otherFocuses,
      fractionalSTVPartySeatRunTrace,
      fractionalSTVIndexedExecutableTrace_of_partySeatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots
        (STVQuota seats voters : ℝ) otherFocuses initialActive initialWeight
        i candidate
  have hpartyExec :
      FractionalSTVExecutableTrace partyRule partyTrace allVoters ballots
        (STVQuota seats voters : ℝ)
        initialActive
        (fractionalSTVPartySeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) partyCandidates stvSeatCount
          partyRounds 0 initialActive initialWeight)
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := partyRule) partyRun hpartyRuleTallyEq
  have hotherExec :
      FractionalSTVExecutableTrace otherRule otherTrace allVoters ballots
        (STVQuota seats voters : ℝ)
        initialActive
        (fractionalSTVPartySeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) otherPartyCandidates
          otherPartySeatCount otherPartyRounds 0 initialActive initialWeight)
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := otherRule) otherRun hotherRuleTallyEq
  have hpartyRoundNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              partyRun.roundTally i candidate < (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hactive : candidate ∈ (partyTrace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    simpa [partyTrace, partyRun] using
      fractionalSTVIndexedExecutableTrace_of_partySeatRun_get_noquota_if_eliminate
        choice allVoters ballots (STVQuota seats voters : ℝ)
        partyCandidates stvSeatCount partyRounds 0 initialActive
        initialWeight hquota_pos hinitialWeightNonneg hchoiceRespect i
        candidate hactive hkind
  have hotherRoundNoquotaOnEliminate :
      ∀ i : Fin otherTrace.steps.length,
        (otherTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (otherTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              otherRun.roundTally i candidate < (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    have hactive : candidate ∈ (otherTrace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    simpa [otherTrace, otherRun] using
      fractionalSTVIndexedExecutableTrace_of_partySeatRun_get_noquota_if_eliminate
        choice allVoters ballots (STVQuota seats voters : ℝ)
        otherPartyCandidates otherPartySeatCount otherPartyRounds 0
        initialActive initialWeight hquota_pos hinitialWeightNonneg
        hchoiceRespect i candidate hactive hkind
  have hpartyNoquotaOnEliminate :
      ∀ i : Fin partyTrace.steps.length,
        (partyTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (partyTrace.steps.get i).beforeActive
                  partyCandidates →
              partyRule.fractionalTally (partyTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    rw [hpartyRuleTallyEq i candidate (Finset.mem_filter.mp hcandidate).1]
    exact hpartyRoundNoquotaOnEliminate i hkind candidate hcandidate
  have hotherNoquotaOnEliminate :
      ∀ i : Fin otherTrace.steps.length,
        (otherTrace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (otherTrace.steps.get i).beforeActive
                  otherPartyCandidates →
              otherRule.fractionalTally (otherTrace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    rw [hotherRuleTallyEq i candidate (Finset.mem_filter.mp hcandidate).1]
    exact hotherRoundNoquotaOnEliminate i hkind candidate hcandidate
  have hpartyFinal :
      partyElectStepCount partyCandidates partyTrace.steps ≤ stvSeatCount := by
    simpa [partyTrace] using
      partyElectStepCount_fractionalSTVPartySeatRunTrace_le_partySeatLimit
        choice allVoters ballots (STVQuota seats voters : ℝ) partyCandidates
        stvSeatCount partyRounds initialActive initialWeight
  have hotherFinal :
      partyElectStepCount otherPartyCandidates otherTrace.steps ≤
        otherPartySeatCount := by
    simpa [otherTrace] using
      partyElectStepCount_fractionalSTVPartySeatRunTrace_le_partySeatLimit
        choice allVoters ballots (STVQuota seats voters : ℝ)
        otherPartyCandidates otherPartySeatCount otherPartyRounds
        initialActive initialWeight
  exact
    proposition1_seatSharesRounded_of_executableTrace_twoRules_capacityTerminals_and_pavMinArgmax
      (partyRule := partyRule) (otherPartyRule := otherRule)
      (partyTrace := partyTrace) (otherPartyTrace := otherTrace)
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (partyTerminalActive :=
        fractionalSTVPartySeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) partyCandidates stvSeatCount
          partyRounds 0 initialActive initialWeight)
      (otherTerminalActive :=
        fractionalSTVPartySeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) otherPartyCandidates
          otherPartySeatCount otherPartyRounds 0 initialActive initialWeight)
      initialWeight partyInitialWeight otherPartyInitialWeight hpos hle
      htotal hvoters hpartyCandidates hotherPartyCandidates hpartyExec
      hotherExec hvoterPartition hvoterDisjoint hcandidateDisjoint
      hpartySolid hotherSolid hpartyInitialActive hotherInitialActive
      hpartyInitialWeightEq hotherInitialWeightEq hpartyInitialMass
      hotherInitialMass hpartyNoquotaOnEliminate hotherNoquotaOnEliminate
      hpartyTerminalNoParty hotherTerminalNoParty hpartyFinal hotherFinal hpav

/--
Proposition 1 from a full generated fractional STV choice-rule run.

This is the source-closed simulator route for the GGRS STV side: the concrete
choice rule is total on nonempty active sets, the run has enough rounds to
exhaust the initial active set, quota-respecting choice derives all no-quota
elimination facts, and the final party seat counts are read from the generated
candidate-level STV trace.
-/
theorem proposition1_seatSharesRounded_of_choiceRunFractionalSTVTrace_lowerBoundTerminals_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {rounds : ℕ}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hchoiceTotal : choice.Total)
    (hrounds : initialActive.card ≤ rounds)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyFinal :
      partyElectStepCount partyCandidates
          (fractionalSTVChoiceRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive
            initialWeight).steps ≤
        stvSeatCount)
    (hotherFinal :
      partyElectStepCount otherPartyCandidates
          (fractionalSTVChoiceRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive
            initialWeight).steps ≤
        otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let focuses :=
    fractionalSTVChoiceRunFocuses choice allVoters ballots
      (STVQuota seats voters : ℝ) rounds initialActive initialWeight
  let trace :=
    fractionalSTVChoiceRunTrace choice allVoters ballots
      (STVQuota seats voters : ℝ) rounds initialActive initialWeight
  let rule :=
    fractionalSTVGeneratedTransferRule allVoters ballots
      (STVQuota seats voters : ℝ) focuses initialActive initialWeight
  let indexedRun :=
    fractionalSTVIndexedExecutableTrace_of_choiceRun choice allVoters ballots
      (STVQuota seats voters : ℝ) rounds initialActive initialWeight
      hquota_pos hinitialWeightNonneg
  have hruleTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈ (trace.steps.get i).beforeActive →
          rule.fractionalTally (trace.steps.get i) candidate =
            indexedRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [trace, rule, indexedRun, focuses, fractionalSTVChoiceRunTrace,
      fractionalSTVIndexedExecutableTrace_of_choiceRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots
        (STVQuota seats voters : ℝ) focuses initialActive initialWeight
        i candidate
  have hexec :
      FractionalSTVExecutableTrace rule trace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive
        (fractionalSTVChoiceRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) rounds initialActive initialWeight)
        initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := rule) indexedRun hruleTallyEq
  have hroundNoquotaOnEliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈ (trace.steps.get i).beforeActive →
              indexedRun.roundTally i candidate < (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    simpa [trace, indexedRun, focuses, fractionalSTVChoiceRunTrace,
      fractionalSTVIndexedExecutableTrace_of_choiceRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVChoiceRun_get_noquota_if_eliminate choice allVoters ballots
        (STVQuota seats voters : ℝ) hchoiceRespect rounds initialActive
        initialWeight i candidate hcandidate hkind
  have hnoquotaOnEliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈ (trace.steps.get i).beforeActive →
              rule.fractionalTally (trace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    rw [hruleTallyEq i candidate hcandidate]
    exact hroundNoquotaOnEliminate i hkind candidate hcandidate
  have hpartyNoquotaOnEliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (trace.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (trace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    exact hnoquotaOnEliminate i hkind candidate
      (Finset.mem_filter.mp hcandidate).1
  have hotherNoquotaOnEliminate :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (trace.steps.get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally (trace.steps.get i) candidate <
                (STVQuota seats voters : ℝ) := by
    intro i hkind candidate hcandidate
    exact hnoquotaOnEliminate i hkind candidate
      (Finset.mem_filter.mp hcandidate).1
  have hterminalEmpty :
      fractionalSTVChoiceRunTerminalActive choice allVoters ballots
        (STVQuota seats voters : ℝ) rounds initialActive initialWeight = ∅ :=
    fractionalSTVChoiceRunTerminalActive_eq_empty_of_total choice allVoters
      ballots (STVQuota seats voters : ℝ) hchoiceTotal rounds initialActive
      initialWeight hrounds
  have hpartyTerminalNoParty :
      activePartyCandidates
          (fractionalSTVChoiceRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive initialWeight)
          partyCandidates = ∅ := by
    rw [hterminalEmpty]
    simp [activePartyCandidates]
  have hotherTerminalNoParty :
      activePartyCandidates
          (fractionalSTVChoiceRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive initialWeight)
          otherPartyCandidates = ∅ := by
    rw [hterminalEmpty]
    simp [activePartyCandidates]
  have hpartyFinal' :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount := by
    simpa [trace] using hpartyFinal
  have hotherFinal' :
      partyElectStepCount otherPartyCandidates trace.steps ≤
        otherPartySeatCount := by
    simpa [trace] using hotherFinal
  exact
    proposition1_seatSharesRounded_of_executableTrace_twoRules_capacityTerminals_and_pavMinArgmax
      (partyRule := rule) (otherPartyRule := rule)
      (partyTrace := trace) (otherPartyTrace := trace)
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (partyTerminalActive :=
        fractionalSTVChoiceRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) rounds initialActive initialWeight)
      (otherTerminalActive :=
        fractionalSTVChoiceRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) rounds initialActive initialWeight)
      initialWeight partyInitialWeight otherPartyInitialWeight hpos hle
      htotal hvoters hpartyCandidates hotherPartyCandidates hexec hexec
      hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
      hotherSolid hpartyInitialActive hotherInitialActive
      hpartyInitialWeightEq hotherInitialWeightEq hpartyInitialMass
      hotherInitialMass hpartyNoquotaOnEliminate hotherNoquotaOnEliminate
      hpartyTerminalNoParty hotherTerminalNoParty hpartyFinal' hotherFinal'
      hpav

/--
Proposition 1 from a filled full fractional STV choice-rule run.

This wrapper reads the STV party seat count directly from the generated
candidate-level trace.  Compared with
`proposition1_seatSharesRounded_of_choiceRunFractionalSTVTrace_lowerBoundTerminals_and_pavMinArgmax`,
the final same-party elected-count inclusions are discharged by reflexivity and
the source model supplies only the filled-seat conservation equation.
-/
theorem proposition1_seatSharesRounded_of_filledChoiceRunFractionalSTVTrace_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {rounds pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hchoiceTotal : choice.Total)
    (hrounds : initialActive.card ≤ rounds)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hfilled :
      partyElectStepCount partyCandidates
          (fractionalSTVChoiceRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive
            initialWeight).steps +
        partyElectStepCount otherPartyCandidates
          (fractionalSTVChoiceRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive
            initialWeight).steps =
          seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded
        (partyElectStepCount partyCandidates
          (fractionalSTVChoiceRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive
            initialWeight).steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  exact
    proposition1_seatSharesRounded_of_choiceRunFractionalSTVTrace_lowerBoundTerminals_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) choice
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      initialWeight partyInitialWeight otherPartyInitialWeight
      (rounds := rounds)
      (stvSeatCount :=
        partyElectStepCount partyCandidates
          (fractionalSTVChoiceRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive
            initialWeight).steps)
      (otherPartySeatCount :=
        partyElectStepCount otherPartyCandidates
          (fractionalSTVChoiceRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive
            initialWeight).steps)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hfilled hvoters
      hinitialWeightNonneg hchoiceRespect hchoiceTotal hrounds
      hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
      hotherSolid hpartyInitialActive hotherInitialActive
      hpartyInitialWeightEq hotherInitialWeightEq hpartyInitialMass
      hotherInitialMass hpartyCandidates hotherPartyCandidates
      (Nat.le_refl _) (Nat.le_refl _) hpav

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

/--
Proposition 1 reduced to the source-primitive candidate-level STV trace
boundary and the PAV min-argmax characterization.
-/
theorem proposition1_seatSharesRounded_of_sourcePrimitiveTransferTraceBounds_and_pavMinArgmax
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv :
      stvSolidCoalitionSourcePrimitiveTransferTraceBounds
        (Candidate := Candidate) rule trace partyCandidates
        otherPartyCandidates stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
    hpos hle
    (stvSolidCoalitionQuotaWitnessBounds_of_sourcePrimitiveTransferTraceBounds
      hstv)
    hpav

/--
Proposition 1 reduced to the stronger shared fractional STV replay boundary and
the PAV min-argmax characterization.
-/
theorem proposition1_seatSharesRounded_of_stvFractionalReplayBounds_and_pavMinArgmax
    {Candidate : Type*} [DecidableEq Candidate]
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv :
      stvSolidCoalitionFractionalReplayBounds
        (Candidate := Candidate) stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
    hpos hle (stvSolidCoalitionQuotaWitnessBounds_of_fractionalReplayBounds hstv)
    hpav

/--
Proposition 1 reduced to a transfer-rule-parametric STV preservation boundary
and the PAV min-argmax characterization.

This is the rule-explicit GGRS route: the conclusion holds for any transfer
rule whose candidate-level trace satisfies the paper's same-party quota and
surplus-transfer preservation laws under solid coalitions.
-/
theorem proposition1_seatSharesRounded_of_stvTransferRuleReplayBounds_and_pavMinArgmax
    {Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate}
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv :
      stvSolidCoalitionTransferRuleReplayBounds
        (Candidate := Candidate) rule stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
    hpos hle
    (stvSolidCoalitionQuotaWitnessBounds_of_transferRuleReplayBounds hstv)
    hpav

/--
Proposition 1 from fully expanded source primitives: raw solid-coalition
ballots plus primitive per-step transfer laws for the concrete rule and trace
construct the STV quota witnesses internally, then the PAV min-argmax
characterization supplies the PAV side.
-/
theorem proposition1_seatSharesRounded_of_solidCoalitionPrimitiveTraceBounds_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv :
      stvSolidCoalitionPrimitiveTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
    hpos hle
    (stvSolidCoalitionQuotaWitnessBounds_of_solidCoalitionPrimitiveTraceBounds
      hstv)
    hpav

/--
Proposition 1 from indexed source primitives: raw solid-coalition ballots plus
per-concrete-step primitive transfer facts for the concrete rule and trace
construct the STV quota witnesses internally, then the PAV min-argmax
characterization supplies the PAV side.
-/
theorem proposition1_seatSharesRounded_of_indexedPrimitiveTraceBounds_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv :
      stvSolidCoalitionIndexedPrimitiveTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
    hpos hle
    (stvSolidCoalitionQuotaWitnessBounds_of_indexedPrimitiveTraceBounds hstv)
    hpav

/--
Proposition 1 from source-step trace dynamics: raw solid-coalition ballots plus
per-concrete-step source STV dynamics construct the STV quota witnesses
internally, then the PAV min-argmax characterization supplies the PAV side.
-/
theorem proposition1_seatSharesRounded_of_sourceStepTraceBounds_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {stvSeatCount pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hstv :
      stvSolidCoalitionSourceStepTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        stvSeatCount partyShare seats voters)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats :=
  proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
    hpos hle
    (stvSolidCoalitionQuotaWitnessBounds_of_sourceStepTraceBounds hstv)
    hpav

/--
Proposition 1 from fully explicit source-step trace facts: the theorem does
not take a packaged STV boundary.  The source model supplies the two-party seat
conservation facts, raw solid-coalition ballots, per-index source step laws,
terminal below-quota residuals, and final-seat inclusions.
-/
theorem proposition1_seatSharesRounded_of_explicitSourceStepTraceFacts_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hpartySteps :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVSourceStepLaw partyCandidates
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i)
          (partyTransferPreservationTerminalState partyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ)))))
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherSteps :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVSourceStepLaw otherPartyCandidates
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i)
          (partyTransferPreservationTerminalState otherPartyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ)))))
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hbounds :
      stvSolidCoalitionSourceStepTraceBounds
        (Voter := Voter) (Candidate := Candidate) rule trace partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        stvSeatCount partyShare seats voters := by
    refine ⟨otherPartySeatCount, ?_⟩
    have hpartyTraceLaw :
        FractionalPartySTVSourceTraceLaw partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally trace.steps
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ))) := by
      intro i
      exact hpartySteps i
    have hotherTraceLaw :
        FractionalPartySTVSourceTraceLaw otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally trace.steps
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ))) := by
      intro i
      exact hotherSteps i
    have hpartyTerminal :
        PartyQuotaTerminalBelowQuota (STVQuota seats voters : ℝ)
          (partyTransferPreservationTerminalState partyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally trace.steps
            (PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ)))) :=
      terminalBelowQuota_of_partyElectStepCount_residual_lt
        (partyCandidates := partyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (initialVotes := partyShare * (voters : ℝ))
        (fractionalTally := rule.fractionalTally)
        (steps := trace.steps) hpartyResidual
    have hotherTerminal :
        PartyQuotaTerminalBelowQuota (STVQuota seats voters : ℝ)
          (partyTransferPreservationTerminalState otherPartyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally trace.steps
            (PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ)))) :=
      terminalBelowQuota_of_partyElectStepCount_residual_lt
        (partyCandidates := otherPartyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (initialVotes := (1 - partyShare) * (voters : ℝ))
        (fractionalTally := rule.fractionalTally)
        (steps := trace.steps) hotherResidual
    have hpartyFinal :
        (partyTransferPreservationTerminalState partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally trace.steps
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))).quotaWinners ≤ stvSeatCount :=
      quotaWinners_terminalState_le_of_partyElectStepCount_le
        (partyCandidates := partyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (initialVotes := partyShare * (voters : ℝ))
        (fractionalTally := rule.fractionalTally)
        (steps := trace.steps) hpartyElectCount
    have hotherFinal :
        (partyTransferPreservationTerminalState otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally trace.steps
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))).quotaWinners ≤
          otherPartySeatCount :=
      quotaWinners_terminalState_le_of_partyElectStepCount_le
        (partyCandidates := otherPartyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (initialVotes := (1 - partyShare) * (voters : ℝ))
        (fractionalTally := rule.fractionalTally)
        (steps := trace.steps) hotherElectCount
    dsimp [stvTwoPartySolidCoalitionSourceStepTraceBounds,
      PartyTransferSourceTraceOutcome]
    exact ⟨htotal, hpos.le, hle, hvoters, hpartyCandidates,
      hotherPartyCandidates, hpartySolid, hotherSolid,
      ⟨hpartyTraceLaw, hpartyTerminal, hpartyFinal⟩,
      ⟨hotherTraceLaw, hotherTerminal, hotherFinal⟩⟩
  exact
    proposition1_seatSharesRounded_of_sourceStepTraceBounds_and_pavMinArgmax
      hpos hle hbounds hpav

/--
Proposition 1 from explicit concrete fractional STV trace facts: the theorem
separates global candidate-level step validity from party projection-state
identities, then constructs the party source-step laws internally.
-/
theorem proposition1_seatSharesRounded_of_explicitConcreteStepTraceFacts_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i))
    (hpartyProjection :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVProjectionStateLaw partyCandidates
          (rule.fractionalTally (trace.steps.get i)) (trace.steps.get i)
          (partyTransferPreservationTerminalState partyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ)))))
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherProjection :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVProjectionStateLaw otherPartyCandidates
          (rule.fractionalTally (trace.steps.get i)) (trace.steps.get i)
          (partyTransferPreservationTerminalState otherPartyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ)))))
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hpartySteps :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVSourceStepLaw partyCandidates
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i)
          (partyTransferPreservationTerminalState partyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ)))) := by
    intro i
    exact fractionalPartySTVSourceStepLaw_of_concreteStepLaw
      (htraceSteps i) (hpartyProjection i)
  have hotherSteps :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVSourceStepLaw otherPartyCandidates
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i)
          (partyTransferPreservationTerminalState otherPartyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ)))) := by
    intro i
    exact fractionalPartySTVSourceStepLaw_of_concreteStepLaw
      (htraceSteps i) (hotherProjection i)
  exact
    proposition1_seatSharesRounded_of_explicitSourceStepTraceFacts_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid hpartySteps
      hpartyResidual hpartyElectCount hotherSteps hotherResidual
      hotherElectCount hpav

/--
Proposition 1 from weighted concrete fractional STV trace facts: the theorem
expands the party projection-state laws into weighted active-support tally
equalities, party-state count equalities, and party-state mass equalities.
-/
theorem proposition1_seatSharesRounded_of_weightedConcreteTraceFacts_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    (partyWeight otherPartyWeight : STVStep Candidate → Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i))
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (partyWeight (trace.steps.get i))
              (trace.steps.get i).beforeActive candidate)
    (hpartyRemaining :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))).remainingCandidates =
          (activePartyCandidates (trace.steps.get i).beforeActive
            partyCandidates).card)
    (hpartyMass :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))).voteMass =
          ∑ voter ∈ partyVoters, partyWeight (trace.steps.get i) voter)
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally otherPartyVoters ballots
              (otherPartyWeight (trace.steps.get i))
              (trace.steps.get i).beforeActive candidate)
    (hotherRemaining :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))).remainingCandidates =
          (activePartyCandidates (trace.steps.get i).beforeActive
            otherPartyCandidates).card)
    (hotherMass :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))).voteMass =
          ∑ voter ∈ otherPartyVoters, otherPartyWeight (trace.steps.get i) voter)
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hpartyProjection :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVProjectionStateLaw partyCandidates
          (rule.fractionalTally (trace.steps.get i)) (trace.steps.get i)
          (partyTransferPreservationTerminalState partyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ)))) := by
    intro i
    exact
      fractionalPartySTVProjectionStateLaw_of_solidCoalition_weightMass_of_tally_eq
        (voters := partyVoters) (ballots := ballots)
        (weight := partyWeight (trace.steps.get i))
        (partyCandidates := partyCandidates)
        (fractionalTally := rule.fractionalTally (trace.steps.get i))
        (step := trace.steps.get i)
        (before :=
          partyTransferPreservationTerminalState partyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ))))
        hpartySolid (hpartyActive i) (hpartyTallyEq i)
        (hpartyRemaining i) (hpartyMass i)
  have hotherProjection :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVProjectionStateLaw otherPartyCandidates
          (rule.fractionalTally (trace.steps.get i)) (trace.steps.get i)
          (partyTransferPreservationTerminalState otherPartyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ)))) := by
    intro i
    exact
      fractionalPartySTVProjectionStateLaw_of_solidCoalition_weightMass_of_tally_eq
        (voters := otherPartyVoters) (ballots := ballots)
        (weight := otherPartyWeight (trace.steps.get i))
        (partyCandidates := otherPartyCandidates)
        (fractionalTally := rule.fractionalTally (trace.steps.get i))
        (step := trace.steps.get i)
        (before :=
          partyTransferPreservationTerminalState otherPartyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ))))
        hotherSolid (hotherActive i) (hotherTallyEq i)
        (hotherRemaining i) (hotherMass i)
  exact
    proposition1_seatSharesRounded_of_explicitConcreteStepTraceFacts_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid htraceSteps
      hpartyProjection hpartyResidual hpartyElectCount hotherProjection
      hotherResidual hotherElectCount hpav

/--
Proposition 1 from recursive fractional STV weight dynamics: this removes the
per-round party-mass assumptions by deriving them from the source transfer
update that scales elected supporters by the surplus factor and preserves
total weight on all non-party-election rounds.
-/
theorem proposition1_seatSharesRounded_of_fractionalWeightDynamics_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    (partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i))
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyWeightTrace :
      FractionalSTVPartyWeightTraceLaw partyVoters ballots partyCandidates
        (STVQuota seats voters : ℝ) trace.steps partyInitialWeight)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (fractionalSTVWeightAfterSteps partyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                partyInitialWeight)
              (trace.steps.get i).beforeActive candidate)
    (hpartyRemaining :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))).remainingCandidates =
          (activePartyCandidates (trace.steps.get i).beforeActive
            partyCandidates).card)
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherWeightTrace :
      FractionalSTVPartyWeightTraceLaw otherPartyVoters ballots
        otherPartyCandidates (STVQuota seats voters : ℝ) trace.steps
        otherPartyInitialWeight)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally otherPartyVoters ballots
              (fractionalSTVWeightAfterSteps otherPartyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                otherPartyInitialWeight)
              (trace.steps.get i).beforeActive candidate)
    (hotherRemaining :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))).remainingCandidates =
          (activePartyCandidates (trace.steps.get i).beforeActive
            otherPartyCandidates).card)
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  have hpartyProjection :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVProjectionStateLaw partyCandidates
          (rule.fractionalTally (trace.steps.get i)) (trace.steps.get i)
          (partyTransferPreservationTerminalState partyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ)))) := by
    intro i
    have hprefixLaw :
        FractionalSTVPartyWeightTraceLaw partyVoters ballots partyCandidates
          (STVQuota seats voters : ℝ) (trace.steps.take i.1)
          partyInitialWeight :=
      fractionalSTVPartyWeightTraceLaw_take hpartyWeightTrace i.1
    have hmass :
        (partyTransferPreservationTerminalState partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))).voteMass =
          ∑ voter ∈ partyVoters,
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight voter :=
      voteMass_partyTransferPreservationTerminalState_eq_sum_fractionalSTVWeightAfterSteps
        (voters := partyVoters) (ballots := ballots)
        (partyCandidates := partyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (initialVotes := partyShare * (voters : ℝ))
        (fractionalTally := rule.fractionalTally)
        (steps := trace.steps.take i.1)
        (initialWeight := partyInitialWeight)
        hpartyInitialMass hquota_pos hprefixLaw
    exact
      fractionalPartySTVProjectionStateLaw_of_solidCoalition_weightMass_of_tally_eq
        (voters := partyVoters) (ballots := ballots)
        (weight :=
          fractionalSTVWeightAfterSteps partyVoters ballots
            (STVQuota seats voters : ℝ) (trace.steps.take i.1)
            partyInitialWeight)
        (partyCandidates := partyCandidates)
        (fractionalTally := rule.fractionalTally (trace.steps.get i))
        (step := trace.steps.get i)
        (before :=
          partyTransferPreservationTerminalState partyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ))))
        hpartySolid (hpartyActive i) (hpartyTallyEq i)
        (hpartyRemaining i) hmass
  have hotherProjection :
      ∀ i : Fin trace.steps.length,
        FractionalPartySTVProjectionStateLaw otherPartyCandidates
          (rule.fractionalTally (trace.steps.get i)) (trace.steps.get i)
          (partyTransferPreservationTerminalState otherPartyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ)))) := by
    intro i
    have hprefixLaw :
        FractionalSTVPartyWeightTraceLaw otherPartyVoters ballots
          otherPartyCandidates (STVQuota seats voters : ℝ)
          (trace.steps.take i.1) otherPartyInitialWeight :=
      fractionalSTVPartyWeightTraceLaw_take hotherWeightTrace i.1
    have hmass :
        (partyTransferPreservationTerminalState otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))).voteMass =
          ∑ voter ∈ otherPartyVoters,
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight voter :=
      voteMass_partyTransferPreservationTerminalState_eq_sum_fractionalSTVWeightAfterSteps
        (voters := otherPartyVoters) (ballots := ballots)
        (partyCandidates := otherPartyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (initialVotes := (1 - partyShare) * (voters : ℝ))
        (fractionalTally := rule.fractionalTally)
        (steps := trace.steps.take i.1)
        (initialWeight := otherPartyInitialWeight)
        hotherInitialMass hquota_pos hprefixLaw
    exact
      fractionalPartySTVProjectionStateLaw_of_solidCoalition_weightMass_of_tally_eq
        (voters := otherPartyVoters) (ballots := ballots)
        (weight :=
          fractionalSTVWeightAfterSteps otherPartyVoters ballots
            (STVQuota seats voters : ℝ) (trace.steps.take i.1)
            otherPartyInitialWeight)
        (partyCandidates := otherPartyCandidates)
        (fractionalTally := rule.fractionalTally (trace.steps.get i))
        (step := trace.steps.get i)
        (before :=
          partyTransferPreservationTerminalState otherPartyCandidates
            (STVQuota seats voters : ℝ) rule.fractionalTally
            (trace.steps.take i.1)
            (PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ))))
        hotherSolid (hotherActive i) (hotherTallyEq i)
        (hotherRemaining i) hmass
  exact
    proposition1_seatSharesRounded_of_explicitConcreteStepTraceFacts_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid htraceSteps
      hpartyProjection hpartyResidual hpartyElectCount hotherProjection
      hotherResidual hotherElectCount hpav

/--
Proposition 1 from recursive fractional STV weight dynamics plus concrete
active-set replay: this derives both party vote-mass and remaining-candidate
projection facts before invoking the source-step STV bridge.
-/
theorem proposition1_seatSharesRounded_of_fractionalWeightDynamics_replay_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i))
    (hprefixReplay :
      ∀ i : Fin trace.steps.length,
        STVTrace.replayStepsFrom (trace.steps.take i.1) initialActive
          (trace.steps.get i).beforeActive)
    (hpartyInitialActive :
      (activePartyCandidates initialActive partyCandidates).card =
        partyCandidates.card)
    (hotherInitialActive :
      (activePartyCandidates initialActive otherPartyCandidates).card =
        otherPartyCandidates.card)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyWeightTrace :
      FractionalSTVPartyWeightTraceLaw partyVoters ballots partyCandidates
        (STVQuota seats voters : ℝ) trace.steps partyInitialWeight)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (fractionalSTVWeightAfterSteps partyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                partyInitialWeight)
              (trace.steps.get i).beforeActive candidate)
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherWeightTrace :
      FractionalSTVPartyWeightTraceLaw otherPartyVoters ballots
        otherPartyCandidates (STVQuota seats voters : ℝ) trace.steps
        otherPartyInitialWeight)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally otherPartyVoters ballots
              (fractionalSTVWeightAfterSteps otherPartyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                otherPartyInitialWeight)
              (trace.steps.get i).beforeActive candidate)
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hordinarySteps :
      ∀ step, step ∈ trace.steps →
        ∃ focused, step.focus = some focused ∧
          focused ∈ step.beforeActive ∧ step.removesFocusedCandidate ∧
          (step.kind = StepKind.elect ∨ step.kind = StepKind.eliminate) := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, rfl⟩
    rcases htraceSteps ⟨n, hn⟩ with
      ⟨hremove, focused, hfocus, hfocused_active, _hnonneg,
        hkind_allowed, _hquota⟩
    exact ⟨focused, hfocus, hfocused_active, hremove, hkind_allowed⟩
  have hpartyRemaining :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))).remainingCandidates =
          (activePartyCandidates (trace.steps.get i).beforeActive
            partyCandidates).card := by
    intro i
    have hstart :
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))).remainingCandidates =
          (activePartyCandidates initialActive partyCandidates).card := by
      simpa [PartyQuotaStartState] using hpartyInitialActive.symm
    exact
      remainingCandidates_partyTransferPreservationTerminalState_eq_activePartyCandidates_of_replayStepsFrom
        (partyCandidates := partyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (fractionalTally := rule.fractionalTally)
        (steps := trace.steps.take i.1)
        (startActive := initialActive)
        (terminalActive := (trace.steps.get i).beforeActive)
        (state :=
          PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))
        (hprefixReplay i) hstart (by
          intro step hstep
          exact hordinarySteps step (List.mem_of_mem_take hstep))
  have hotherRemaining :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))).remainingCandidates =
          (activePartyCandidates (trace.steps.get i).beforeActive
            otherPartyCandidates).card := by
    intro i
    have hstart :
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))).remainingCandidates =
          (activePartyCandidates initialActive otherPartyCandidates).card := by
      simpa [PartyQuotaStartState] using hotherInitialActive.symm
    exact
      remainingCandidates_partyTransferPreservationTerminalState_eq_activePartyCandidates_of_replayStepsFrom
        (partyCandidates := otherPartyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (fractionalTally := rule.fractionalTally)
        (steps := trace.steps.take i.1)
        (startActive := initialActive)
        (terminalActive := (trace.steps.get i).beforeActive)
        (state :=
          PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))
        (hprefixReplay i) hstart (by
          intro step hstep
          exact hordinarySteps step (List.mem_of_mem_take hstep))
  exact
    proposition1_seatSharesRounded_of_fractionalWeightDynamics_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      partyInitialWeight otherPartyInitialWeight
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid htraceSteps
      hpartyInitialMass hpartyWeightTrace hpartyActive hpartyTallyEq
      hpartyRemaining hpartyResidual hpartyElectCount
      hotherInitialMass hotherWeightTrace hotherActive hotherTallyEq
      hotherRemaining hotherResidual hotherElectCount hpav

/--
Proposition 1 from concrete fractional transfer replay primitives: recursive
party weight dynamics are derived from candidate-level concrete STV step laws,
solid-coalition ballots, and active same-party tally equalities.
-/
theorem proposition1_seatSharesRounded_of_fractionalTransferReplay_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i))
    (hprefixReplay :
      ∀ i : Fin trace.steps.length,
        STVTrace.replayStepsFrom (trace.steps.take i.1) initialActive
          (trace.steps.get i).beforeActive)
    (hpartyInitialActive :
      (activePartyCandidates initialActive partyCandidates).card =
        partyCandidates.card)
    (hotherInitialActive :
      (activePartyCandidates initialActive otherPartyCandidates).card =
        otherPartyCandidates.card)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (fractionalSTVWeightAfterSteps partyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                partyInitialWeight)
              (trace.steps.get i).beforeActive candidate)
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally otherPartyVoters ballots
              (fractionalSTVWeightAfterSteps otherPartyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                otherPartyInitialWeight)
              (trace.steps.get i).beforeActive candidate)
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hpartyWeightTrace :
      FractionalSTVPartyWeightTraceLaw partyVoters ballots partyCandidates
        (STVQuota seats voters : ℝ) trace.steps partyInitialWeight := by
    apply fractionalSTVPartyWeightTraceLaw_of_getElem
    intro i
    constructor
    · intro focused hfocus helect hfocused_party
      rcases htraceSteps i with
        ⟨_hremove, concreteFocused, hconcreteFocus, hfocused_active,
          _hnonneg, _hkind_allowed, hquota_if_elect⟩
      have hfocused_eq : concreteFocused = focused :=
        Option.some.inj (hconcreteFocus.symm.trans hfocus)
      subst concreteFocused
      have hactive_party :
          focused ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates := by
        exact Finset.mem_filter.mpr ⟨hfocused_active, hfocused_party⟩
      have hquota_rule :
          (STVQuota seats voters : ℝ) ≤
            rule.fractionalTally (trace.steps.get i) focused :=
        hquota_if_elect helect
      rw [hpartyTallyEq i focused hactive_party] at hquota_rule
      exact hquota_rule
    · intro focused _hfocus _helect hfocused_not_party
      exact activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hpartySolid (hpartyActive i) hfocused_not_party
  have hotherWeightTrace :
      FractionalSTVPartyWeightTraceLaw otherPartyVoters ballots
        otherPartyCandidates (STVQuota seats voters : ℝ) trace.steps
        otherPartyInitialWeight := by
    apply fractionalSTVPartyWeightTraceLaw_of_getElem
    intro i
    constructor
    · intro focused hfocus helect hfocused_party
      rcases htraceSteps i with
        ⟨_hremove, concreteFocused, hconcreteFocus, hfocused_active,
          _hnonneg, _hkind_allowed, hquota_if_elect⟩
      have hfocused_eq : concreteFocused = focused :=
        Option.some.inj (hconcreteFocus.symm.trans hfocus)
      subst concreteFocused
      have hactive_party :
          focused ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates := by
        exact Finset.mem_filter.mpr ⟨hfocused_active, hfocused_party⟩
      have hquota_rule :
          (STVQuota seats voters : ℝ) ≤
            rule.fractionalTally (trace.steps.get i) focused :=
        hquota_if_elect helect
      rw [hotherTallyEq i focused hactive_party] at hquota_rule
      exact hquota_rule
    · intro focused _hfocus _helect hfocused_not_party
      exact activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hotherSolid (hotherActive i) hfocused_not_party
  exact
    proposition1_seatSharesRounded_of_fractionalWeightDynamics_replay_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      partyInitialWeight otherPartyInitialWeight
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid htraceSteps hprefixReplay
      hpartyInitialActive hotherInitialActive hpartyInitialMass
      hpartyWeightTrace hpartyActive hpartyTallyEq hpartyResidual
      hpartyElectCount hotherInitialMass hotherWeightTrace hotherActive
      hotherTallyEq hotherResidual hotherElectCount hpav

/--
Proposition 1 from explicit candidate-level fractional STV round facts and
concrete fractional transfer replay primitives.
-/
theorem proposition1_seatSharesRounded_of_fractionalTransferRoundReplay_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive terminalActive : Finset Candidate}
    (roundWeight : STVStep Candidate → Voter → ℝ)
    (partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hremove :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).removesFocusedCandidate)
    (hfocus :
      ∀ i : Fin trace.steps.length,
        ∃ focused, (trace.steps.get i).focus = some focused ∧
          focused ∈ (trace.steps.get i).beforeActive)
    (hroundWeightNonneg :
      ∀ i : Fin trace.steps.length, ∀ voter,
        voter ∈ allVoters → 0 ≤ roundWeight (trace.steps.get i) voter)
    (hroundTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈ (trace.steps.get i).beforeActive →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (roundWeight (trace.steps.get i))
              (trace.steps.get i).beforeActive candidate)
    (hkind_allowed :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.elect ∨
          (trace.steps.get i).kind = StepKind.eliminate)
    (hquota_if_elect :
      ∀ i : Fin trace.steps.length, ∀ focused,
        (trace.steps.get i).focus = some focused →
          (trace.steps.get i).kind = StepKind.elect →
            (STVQuota seats voters : ℝ) ≤
              fractionalActiveTally allVoters ballots
                (roundWeight (trace.steps.get i))
                (trace.steps.get i).beforeActive focused)
    (htraceReplay : trace.replaysFrom initialActive terminalActive)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyRoundWeightEq :
      ∀ i : Fin trace.steps.length, ∀ voter,
        voter ∈ partyVoters →
          roundWeight (trace.steps.get i) voter =
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight voter)
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherRoundWeightEq :
      ∀ i : Fin trace.steps.length, ∀ voter,
        voter ∈ otherPartyVoters →
          roundWeight (trace.steps.get i) voter =
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight voter)
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i) := by
    intro i
    rcases hfocus i with ⟨focused, hfocused, hfocused_active⟩
    exact fractionalSTVConcreteStepLaw_of_weightedActiveTally_of_tally_eq
      (voters := allVoters) (ballots := ballots)
      (weight := roundWeight (trace.steps.get i))
      (fractionalTally := rule.fractionalTally (trace.steps.get i))
      (quota := (STVQuota seats voters : ℝ)) (step := trace.steps.get i)
      (hremove i) hfocused hfocused_active (hroundWeightNonneg i)
      (hroundTallyEq i) (hkind_allowed i)
      (hquota_if_elect i focused hfocused)
  have hprefixReplay :
      ∀ i : Fin trace.steps.length,
        STVTrace.replayStepsFrom (trace.steps.take i.1) initialActive
          (trace.steps.get i).beforeActive := by
    intro i
    exact STVTrace.replaysFrom_take_get_beforeActive htraceReplay i
  have hpartyInitialActiveCard :
      (activePartyCandidates initialActive partyCandidates).card =
        partyCandidates.card :=
    activePartyCandidates_card_eq_of_subset hpartyInitialActive
  have hotherInitialActiveCard :
      (activePartyCandidates initialActive otherPartyCandidates).card =
        otherPartyCandidates.card :=
    activePartyCandidates_card_eq_of_subset hotherInitialActive
  have hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (fractionalSTVWeightAfterSteps partyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                partyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_party : candidate ∈ partyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_other : candidate ∉ otherPartyCandidates := by
      intro hcandidate_other
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hother_empty :
        Ballot.activeSupport otherPartyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hotherSolid (hotherActive i) hcandidate_not_other
    calc
      rule.fractionalTally (trace.steps.get i) candidate
          =
          fractionalActiveTally allVoters ballots
            (roundWeight (trace.steps.get i))
            (trace.steps.get i).beforeActive candidate :=
        hroundTallyEq i candidate hcandidate_active
      _ =
          fractionalActiveTally partyVoters ballots
            (fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_left_of_union_right_support_empty
          (allVoters := allVoters) (voters₁ := partyVoters)
          (voters₂ := otherPartyVoters) (ballots := ballots)
          (weight := roundWeight (trace.steps.get i))
          (leftWeight :=
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition hvoterDisjoint hother_empty
          (hpartyRoundWeightEq i)
  have hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally otherPartyVoters ballots
              (fractionalSTVWeightAfterSteps otherPartyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                otherPartyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_other : candidate ∈ otherPartyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_party : candidate ∉ partyCandidates := by
      intro hcandidate_party
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hparty_empty :
        Ballot.activeSupport partyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hpartySolid (hpartyActive i) hcandidate_not_party
    calc
      rule.fractionalTally (trace.steps.get i) candidate
          =
          fractionalActiveTally allVoters ballots
            (roundWeight (trace.steps.get i))
            (trace.steps.get i).beforeActive candidate :=
        hroundTallyEq i candidate hcandidate_active
      _ =
          fractionalActiveTally otherPartyVoters ballots
            (fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_right_of_union_left_support_empty
          (allVoters := allVoters) (voters₁ := partyVoters)
          (voters₂ := otherPartyVoters) (ballots := ballots)
          (weight := roundWeight (trace.steps.get i))
          (rightWeight :=
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition hvoterDisjoint hparty_empty
          (hotherRoundWeightEq i)
  exact
    proposition1_seatSharesRounded_of_fractionalTransferReplay_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      partyInitialWeight otherPartyInitialWeight
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid htraceSteps hprefixReplay
      hpartyInitialActiveCard hotherInitialActiveCard hpartyInitialMass
      hpartyActive hpartyTallyEq hpartyResidual hpartyElectCount
      hotherInitialMass hotherActive hotherTallyEq hotherResidual
      hotherElectCount hpav

/--
Proposition 1 from a concrete executable fractional STV transfer trace.  The
round tallies are those induced by the recursive global fractional weight fold;
under solid coalitions, the global fold restricts to the two party folds, so
the party replay/source-step facts are derived internally.
-/
theorem proposition1_seatSharesRounded_of_executableFractionalTransferTrace_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive terminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hremove :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).removesFocusedCandidate)
    (hfocus :
      ∀ i : Fin trace.steps.length,
        ∃ focused, (trace.steps.get i).focus = some focused ∧
          focused ∈ (trace.steps.get i).beforeActive)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hroundTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈ (trace.steps.get i).beforeActive →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (fractionalSTVWeightAfterSteps allVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                initialWeight)
              (trace.steps.get i).beforeActive candidate)
    (hkind_allowed :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.elect ∨
          (trace.steps.get i).kind = StepKind.eliminate)
    (hquota_if_elect :
      ∀ i : Fin trace.steps.length, ∀ focused,
        (trace.steps.get i).focus = some focused →
          (trace.steps.get i).kind = StepKind.elect →
            (STVQuota seats voters : ℝ) ≤
              fractionalActiveTally allVoters ballots
                (fractionalSTVWeightAfterSteps allVoters ballots
                  (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                  initialWeight)
                (trace.steps.get i).beforeActive focused)
    (htraceReplay : trace.replaysFrom initialActive terminalActive)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  have hglobalWeightNonneg :
      ∀ i : Fin trace.steps.length, ∀ voter,
        voter ∈ allVoters →
          0 ≤
            fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight voter := by
    intro i
    exact
      fractionalSTVWeightAfterSteps_take_nonneg
        (voters := allVoters) (ballots := ballots)
        (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
        (initialWeight := initialWeight)
        hinitialWeightNonneg hquota_pos hquota_if_elect i.1
  have htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i) := by
    intro i
    rcases hfocus i with ⟨focused, hfocused, hfocused_active⟩
    exact fractionalSTVConcreteStepLaw_of_weightedActiveTally_of_tally_eq
      (voters := allVoters) (ballots := ballots)
      (weight :=
        fractionalSTVWeightAfterSteps allVoters ballots
          (STVQuota seats voters : ℝ) (trace.steps.take i.1)
          initialWeight)
      (fractionalTally := rule.fractionalTally (trace.steps.get i))
      (quota := (STVQuota seats voters : ℝ)) (step := trace.steps.get i)
      (hremove i) hfocused hfocused_active (hglobalWeightNonneg i)
      (hroundTallyEq i) (hkind_allowed i)
      (hquota_if_elect i focused hfocused)
  have hprefixReplay :
      ∀ i : Fin trace.steps.length,
        STVTrace.replayStepsFrom (trace.steps.take i.1) initialActive
          (trace.steps.get i).beforeActive := by
    intro i
    exact STVTrace.replaysFrom_take_get_beforeActive htraceReplay i
  have hpartyInitialActiveCard :
      (activePartyCandidates initialActive partyCandidates).card =
        partyCandidates.card :=
    activePartyCandidates_card_eq_of_subset hpartyInitialActive
  have hotherInitialActiveCard :
      (activePartyCandidates initialActive otherPartyCandidates).card =
        otherPartyCandidates.card :=
    activePartyCandidates_card_eq_of_subset hotherInitialActive
  have hpartyActive_mem :
      ∀ step, step ∈ trace.steps →
        ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hpartyActive ⟨n, hn⟩
  have hotherActive_mem :
      ∀ step, step ∈ trace.steps →
        ∃ same, same ∈ otherPartyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hotherActive ⟨n, hn⟩
  have hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (fractionalSTVWeightAfterSteps partyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                partyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_party : candidate ∈ partyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_other : candidate ∉ otherPartyCandidates := by
      intro hcandidate_other
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hother_empty :
        Ballot.activeSupport otherPartyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hotherSolid (hotherActive i) hcandidate_not_other
    have hweight_eq :
        ∀ voter, voter ∈ partyVoters →
          fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight voter =
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight voter :=
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := partyVoters)
        (otherVoters := otherPartyVoters) (ballots := ballots)
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (steps := trace.steps.take i.1)
        (initialAllWeight := initialWeight)
        (initialWeight := partyInitialWeight)
        hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
        hotherSolid
        (by
          intro step hstep
          exact hpartyActive_mem step (List.mem_of_mem_take hstep))
        (by
          intro step hstep
          exact hotherActive_mem step (List.mem_of_mem_take hstep))
        hpartyInitialWeightEq
    calc
      rule.fractionalTally (trace.steps.get i) candidate
          =
          fractionalActiveTally allVoters ballots
            (fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
            (trace.steps.get i).beforeActive candidate :=
        hroundTallyEq i candidate hcandidate_active
      _ =
          fractionalActiveTally partyVoters ballots
            (fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_left_of_union_right_support_empty
          (allVoters := allVoters) (voters₁ := partyVoters)
          (voters₂ := otherPartyVoters) (ballots := ballots)
          (weight :=
            fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
          (leftWeight :=
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition hvoterDisjoint hother_empty hweight_eq
  have hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally otherPartyVoters ballots
              (fractionalSTVWeightAfterSteps otherPartyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                otherPartyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_other : candidate ∈ otherPartyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_party : candidate ∉ partyCandidates := by
      intro hcandidate_party
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hparty_empty :
        Ballot.activeSupport partyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hpartySolid (hpartyActive i) hcandidate_not_party
    have hvoterPartition_symm :
        allVoters = otherPartyVoters ∪ partyVoters := by
      rw [hvoterPartition, Finset.union_comm]
    have hweight_eq :
        ∀ voter, voter ∈ otherPartyVoters →
          fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight voter =
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight voter :=
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := otherPartyVoters)
        (otherVoters := partyVoters) (ballots := ballots)
        (partyCandidates := otherPartyCandidates)
        (otherPartyCandidates := partyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (steps := trace.steps.take i.1)
        (initialAllWeight := initialWeight)
        (initialWeight := otherPartyInitialWeight)
        hvoterPartition_symm hvoterDisjoint.symm hcandidateDisjoint.symm
        hotherSolid hpartySolid
        (by
          intro step hstep
          exact hotherActive_mem step (List.mem_of_mem_take hstep))
        (by
          intro step hstep
          exact hpartyActive_mem step (List.mem_of_mem_take hstep))
        hotherInitialWeightEq
    calc
      rule.fractionalTally (trace.steps.get i) candidate
          =
          fractionalActiveTally allVoters ballots
            (fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
            (trace.steps.get i).beforeActive candidate :=
        hroundTallyEq i candidate hcandidate_active
      _ =
          fractionalActiveTally otherPartyVoters ballots
            (fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_left_of_union_right_support_empty
          (allVoters := allVoters) (voters₁ := otherPartyVoters)
          (voters₂ := partyVoters) (ballots := ballots)
          (weight :=
            fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
          (leftWeight :=
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition_symm hvoterDisjoint.symm hparty_empty hweight_eq
  exact
    proposition1_seatSharesRounded_of_fractionalTransferReplay_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      partyInitialWeight otherPartyInitialWeight
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid htraceSteps hprefixReplay
      hpartyInitialActiveCard hotherInitialActiveCard hpartyInitialMass
      hpartyActive hpartyTallyEq hpartyResidual hpartyElectCount
      hotherInitialMass hotherActive hotherTallyEq hotherResidual
      hotherElectCount hpav

/--
Proposition 1 from a concrete executable fractional STV transfer trace and
terminal concrete party weights below quota.  The residual inequalities used by
the party quota-process layer are derived from the executable transfer fold.
-/
theorem proposition1_seatSharesRounded_of_executableFractionalTransferTrace_terminalWeights_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive terminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hremove :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).removesFocusedCandidate)
    (hfocus :
      ∀ i : Fin trace.steps.length,
        ∃ focused, (trace.steps.get i).focus = some focused ∧
          focused ∈ (trace.steps.get i).beforeActive)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hroundTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈ (trace.steps.get i).beforeActive →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (fractionalSTVWeightAfterSteps allVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                initialWeight)
              (trace.steps.get i).beforeActive candidate)
    (hkind_allowed :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.elect ∨
          (trace.steps.get i).kind = StepKind.eliminate)
    (hquota_if_elect :
      ∀ i : Fin trace.steps.length, ∀ focused,
        (trace.steps.get i).focus = some focused →
          (trace.steps.get i).kind = StepKind.elect →
            (STVQuota seats voters : ℝ) ≤
              fractionalActiveTally allVoters ballots
                (fractionalSTVWeightAfterSteps allVoters ballots
                  (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                  initialWeight)
                (trace.steps.get i).beforeActive focused)
    (htraceReplay : trace.replaysFrom initialActive terminalActive)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTerminalWeightBelow :
      (∑ voter ∈ partyVoters,
        fractionalSTVWeightAfterSteps partyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTerminalWeightBelow :
      (∑ voter ∈ otherPartyVoters,
        fractionalSTVWeightAfterSteps otherPartyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps otherPartyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  have hglobalWeightNonneg :
      ∀ i : Fin trace.steps.length, ∀ voter,
        voter ∈ allVoters →
          0 ≤
            fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight voter := by
    intro i
    exact
      fractionalSTVWeightAfterSteps_take_nonneg
        (voters := allVoters) (ballots := ballots)
        (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
        (initialWeight := initialWeight)
        hinitialWeightNonneg hquota_pos hquota_if_elect i.1
  have htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i) := by
    intro i
    rcases hfocus i with ⟨focused, hfocused, hfocused_active⟩
    exact fractionalSTVConcreteStepLaw_of_weightedActiveTally_of_tally_eq
      (voters := allVoters) (ballots := ballots)
      (weight :=
        fractionalSTVWeightAfterSteps allVoters ballots
          (STVQuota seats voters : ℝ) (trace.steps.take i.1)
          initialWeight)
      (fractionalTally := rule.fractionalTally (trace.steps.get i))
      (quota := (STVQuota seats voters : ℝ)) (step := trace.steps.get i)
      (hremove i) hfocused hfocused_active (hglobalWeightNonneg i)
      (hroundTallyEq i) (hkind_allowed i)
      (hquota_if_elect i focused hfocused)
  have hpartyActive_mem :
      ∀ step, step ∈ trace.steps →
        ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hpartyActive ⟨n, hn⟩
  have hotherActive_mem :
      ∀ step, step ∈ trace.steps →
        ∃ same, same ∈ otherPartyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hotherActive ⟨n, hn⟩
  have hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (fractionalSTVWeightAfterSteps partyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                partyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_party : candidate ∈ partyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_other : candidate ∉ otherPartyCandidates := by
      intro hcandidate_other
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hother_empty :
        Ballot.activeSupport otherPartyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hotherSolid (hotherActive i) hcandidate_not_other
    have hweight_eq :
        ∀ voter, voter ∈ partyVoters →
          fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight voter =
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight voter :=
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := partyVoters)
        (otherVoters := otherPartyVoters) (ballots := ballots)
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (steps := trace.steps.take i.1)
        (initialAllWeight := initialWeight)
        (initialWeight := partyInitialWeight)
        hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
        hotherSolid
        (by
          intro step hstep
          exact hpartyActive_mem step (List.mem_of_mem_take hstep))
        (by
          intro step hstep
          exact hotherActive_mem step (List.mem_of_mem_take hstep))
        hpartyInitialWeightEq
    calc
      rule.fractionalTally (trace.steps.get i) candidate
          =
          fractionalActiveTally allVoters ballots
            (fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
            (trace.steps.get i).beforeActive candidate :=
        hroundTallyEq i candidate hcandidate_active
      _ =
          fractionalActiveTally partyVoters ballots
            (fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_left_of_union_right_support_empty
          (allVoters := allVoters) (voters₁ := partyVoters)
          (voters₂ := otherPartyVoters) (ballots := ballots)
          (weight :=
            fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
          (leftWeight :=
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition hvoterDisjoint hother_empty hweight_eq
  have hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally otherPartyVoters ballots
              (fractionalSTVWeightAfterSteps otherPartyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                otherPartyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_other : candidate ∈ otherPartyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_party : candidate ∉ partyCandidates := by
      intro hcandidate_party
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hparty_empty :
        Ballot.activeSupport partyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hpartySolid (hpartyActive i) hcandidate_not_party
    have hvoterPartition_symm :
        allVoters = otherPartyVoters ∪ partyVoters := by
      rw [hvoterPartition, Finset.union_comm]
    have hweight_eq :
        ∀ voter, voter ∈ otherPartyVoters →
          fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight voter =
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight voter :=
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := otherPartyVoters)
        (otherVoters := partyVoters) (ballots := ballots)
        (partyCandidates := otherPartyCandidates)
        (otherPartyCandidates := partyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (steps := trace.steps.take i.1)
        (initialAllWeight := initialWeight)
        (initialWeight := otherPartyInitialWeight)
        hvoterPartition_symm hvoterDisjoint.symm hcandidateDisjoint.symm
        hotherSolid hpartySolid
        (by
          intro step hstep
          exact hotherActive_mem step (List.mem_of_mem_take hstep))
        (by
          intro step hstep
          exact hpartyActive_mem step (List.mem_of_mem_take hstep))
        hotherInitialWeightEq
    calc
      rule.fractionalTally (trace.steps.get i) candidate
          =
          fractionalActiveTally allVoters ballots
            (fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
            (trace.steps.get i).beforeActive candidate :=
        hroundTallyEq i candidate hcandidate_active
      _ =
          fractionalActiveTally otherPartyVoters ballots
            (fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_left_of_union_right_support_empty
          (allVoters := allVoters) (voters₁ := otherPartyVoters)
          (voters₂ := partyVoters) (ballots := ballots)
          (weight :=
            fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
          (leftWeight :=
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition_symm hvoterDisjoint.symm hparty_empty hweight_eq
  have hpartyWeightTrace :
      FractionalSTVPartyWeightTraceLaw partyVoters ballots partyCandidates
        (STVQuota seats voters : ℝ) trace.steps partyInitialWeight :=
    fractionalSTVPartyWeightTraceLaw_of_concreteStepLaw_solidCoalition
      (voters := partyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (fractionalTally := rule.fractionalTally)
      (steps := trace.steps) (initialWeight := partyInitialWeight)
      hpartySolid htraceSteps hpartyActive hpartyTallyEq
  have hotherWeightTrace :
      FractionalSTVPartyWeightTraceLaw otherPartyVoters ballots
        otherPartyCandidates (STVQuota seats voters : ℝ) trace.steps
        otherPartyInitialWeight :=
    fractionalSTVPartyWeightTraceLaw_of_concreteStepLaw_solidCoalition
      (voters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (fractionalTally := rule.fractionalTally)
      (steps := trace.steps) (initialWeight := otherPartyInitialWeight)
      hotherSolid htraceSteps hotherActive hotherTallyEq
  have hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ) :=
    residual_lt_quota_of_sum_fractionalSTVWeightAfterSteps_lt
      (voters := partyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := partyShare * (voters : ℝ))
      (steps := trace.steps) (initialWeight := partyInitialWeight)
      hquota_pos hpartyInitialMass hpartyWeightTrace hpartyTerminalWeightBelow
  have hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ) :=
    residual_lt_quota_of_sum_fractionalSTVWeightAfterSteps_lt
      (voters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ))
      (initialVotes := (1 - partyShare) * (voters : ℝ))
      (steps := trace.steps) (initialWeight := otherPartyInitialWeight)
      hquota_pos hotherInitialMass hotherWeightTrace hotherTerminalWeightBelow
  exact
    proposition1_seatSharesRounded_of_executableFractionalTransferTrace_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (allVoters := allVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) (terminalActive := terminalActive)
      initialWeight partyInitialWeight otherPartyInitialWeight
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid hremove hfocus
      hinitialWeightNonneg hroundTallyEq hkind_allowed hquota_if_elect
      htraceReplay hvoterPartition hvoterDisjoint hcandidateDisjoint
      hpartyInitialActive hotherInitialActive hpartyInitialWeightEq
      hotherInitialWeightEq hpartyInitialMass hpartyActive hpartyResidual
      hpartyElectCount hotherInitialMass hotherActive hotherResidual
      hotherElectCount hpav

/--
Proposition 1 from a two-party executable fractional STV source certificate.
The candidate-level concrete source-step laws are derived from the executable
recursive transfer trace inside the library certificate.
-/
theorem proposition1_seatSharesRounded_of_twoPartyExecutableFractionalSTVTrace_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive terminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hrun :
      FractionalSTVTwoPartyExecutableTrace rule trace allVoters partyVoters
        otherPartyVoters ballots partyCandidates otherPartyCandidates
        (STVQuota seats voters : ℝ) (partyShare * (voters : ℝ))
        ((1 - partyShare) * (voters : ℝ)) initialActive terminalActive
        initialWeight partyInitialWeight otherPartyInitialWeight stvSeatCount
        otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  exact
    proposition1_seatSharesRounded_of_executableFractionalTransferTrace_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (allVoters := allVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) (terminalActive := terminalActive)
      initialWeight partyInitialWeight otherPartyInitialWeight
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hrun.partySolid hrun.otherPartySolid
      hrun.executableTrace.step_removes
      hrun.executableTrace.step_focus_active
      hrun.executableTrace.initialWeight_nonneg
      hrun.executableTrace.tally_eq
      hrun.executableTrace.kind_allowed
      hrun.executableTrace.quota_if_elect
      hrun.executableTrace.activeReplay
      hrun.voterPartition hrun.voterDisjoint hrun.candidateDisjoint
      hrun.partyInitialActive hrun.otherPartyInitialActive
      hrun.partyInitialWeight_eq hrun.otherPartyInitialWeight_eq
      hrun.partyInitialMass hrun.partyActive hrun.partyResidualBelowQuota
      hrun.partyElectCount_le_finalSeats hrun.otherPartyInitialMass
      hrun.otherPartyActive hrun.otherPartyResidualBelowQuota
      hrun.otherPartyElectCount_le_finalSeats hpav

/--
Proposition 1 from an indexed executable fractional STV simulator trace.

This route consumes the simulator-facing indexed real-valued round tallies
directly.  It derives the party weight-trace laws under solid coalitions,
converts terminal concrete party weights below quota into the residual STV
boundary, and finishes through the existing quota/residual arithmetic.
-/
theorem proposition1_seatSharesRounded_of_indexedExecutableFractionalSTVTrace_terminalWeights_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive terminalActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hrun :
      FractionalSTVIndexedExecutableTrace trace allVoters ballots
        (STVQuota seats voters : ℝ) initialActive terminalActive initialWeight)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTerminalWeightBelow :
      (∑ voter ∈ partyVoters,
        fractionalSTVWeightAfterSteps partyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTerminalWeightBelow :
      (∑ voter ∈ otherPartyVoters,
        fractionalSTVWeightAfterSteps otherPartyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps otherPartyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  have htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (hrun.roundTally i) (STVQuota seats voters : ℝ)
          (trace.steps.get i) :=
    FractionalSTVIndexedExecutableTrace.concreteStepLaw hrun
  have hpartyActive_mem :
      ∀ step, step ∈ trace.steps →
        ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hpartyActive ⟨n, hn⟩
  have hotherActive_mem :
      ∀ step, step ∈ trace.steps →
        ∃ same, same ∈ otherPartyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hotherActive ⟨n, hn⟩
  have hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          hrun.roundTally i candidate =
            fractionalActiveTally partyVoters ballots
              (fractionalSTVWeightAfterSteps partyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                partyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_party : candidate ∈ partyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_other : candidate ∉ otherPartyCandidates := by
      intro hcandidate_other
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hother_empty :
        Ballot.activeSupport otherPartyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hotherSolid (hotherActive i) hcandidate_not_other
    have hweight_eq :
        ∀ voter, voter ∈ partyVoters →
          fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight voter =
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight voter :=
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := partyVoters)
        (otherVoters := otherPartyVoters) (ballots := ballots)
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (steps := trace.steps.take i.1)
        (initialAllWeight := initialWeight)
        (initialWeight := partyInitialWeight)
        hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
        hotherSolid
        (by
          intro step hstep
          exact hpartyActive_mem step (List.mem_of_mem_take hstep))
        (by
          intro step hstep
          exact hotherActive_mem step (List.mem_of_mem_take hstep))
        hpartyInitialWeightEq
    calc
      hrun.roundTally i candidate
          =
          fractionalActiveTally allVoters ballots
            (fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
            (trace.steps.get i).beforeActive candidate :=
        hrun.tally_eq i candidate hcandidate_active
      _ =
          fractionalActiveTally partyVoters ballots
            (fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_left_of_union_right_support_empty
          (allVoters := allVoters) (voters₁ := partyVoters)
          (voters₂ := otherPartyVoters) (ballots := ballots)
          (weight :=
            fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
          (leftWeight :=
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              partyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition hvoterDisjoint hother_empty hweight_eq
  have hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          hrun.roundTally i candidate =
            fractionalActiveTally otherPartyVoters ballots
              (fractionalSTVWeightAfterSteps otherPartyVoters ballots
                (STVQuota seats voters : ℝ) (trace.steps.take i.1)
                otherPartyInitialWeight)
              (trace.steps.get i).beforeActive candidate := by
    intro i candidate hcandidate
    have hcandidate_active :
        candidate ∈ (trace.steps.get i).beforeActive :=
      (Finset.mem_filter.mp hcandidate).1
    have hcandidate_other : candidate ∈ otherPartyCandidates :=
      (Finset.mem_filter.mp hcandidate).2
    have hcandidate_not_party : candidate ∉ partyCandidates := by
      intro hcandidate_party
      exact (Finset.disjoint_left.mp hcandidateDisjoint)
        hcandidate_party hcandidate_other
    have hparty_empty :
        Ballot.activeSupport partyVoters ballots
          (trace.steps.get i).beforeActive candidate = ∅ :=
      activeSupport_eq_empty_of_solidCoalitionBallots_outside
        hpartySolid (hpartyActive i) hcandidate_not_party
    have hvoterPartition_symm :
        allVoters = otherPartyVoters ∪ partyVoters := by
      rw [hvoterPartition, Finset.union_comm]
    have hweight_eq :
        ∀ voter, voter ∈ otherPartyVoters →
          fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight voter =
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight voter :=
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := otherPartyVoters)
        (otherVoters := partyVoters) (ballots := ballots)
        (partyCandidates := otherPartyCandidates)
        (otherPartyCandidates := partyCandidates)
        (quota := (STVQuota seats voters : ℝ))
        (steps := trace.steps.take i.1)
        (initialAllWeight := initialWeight)
        (initialWeight := otherPartyInitialWeight)
        hvoterPartition_symm hvoterDisjoint.symm hcandidateDisjoint.symm
        hotherSolid hpartySolid
        (by
          intro step hstep
          exact hotherActive_mem step (List.mem_of_mem_take hstep))
        (by
          intro step hstep
          exact hpartyActive_mem step (List.mem_of_mem_take hstep))
        hotherInitialWeightEq
    calc
      hrun.roundTally i candidate
          =
          fractionalActiveTally allVoters ballots
            (fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
            (trace.steps.get i).beforeActive candidate :=
        hrun.tally_eq i candidate hcandidate_active
      _ =
          fractionalActiveTally otherPartyVoters ballots
            (fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight)
            (trace.steps.get i).beforeActive candidate :=
        fractionalActiveTally_eq_left_of_union_right_support_empty
          (allVoters := allVoters) (voters₁ := otherPartyVoters)
          (voters₂ := partyVoters) (ballots := ballots)
          (weight :=
            fractionalSTVWeightAfterSteps allVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              initialWeight)
          (leftWeight :=
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) (trace.steps.take i.1)
              otherPartyInitialWeight)
          (active := (trace.steps.get i).beforeActive)
          (candidate := candidate)
          hvoterPartition_symm hvoterDisjoint.symm hparty_empty hweight_eq
  have hpartyWeightTrace :
      FractionalSTVPartyWeightTraceLaw partyVoters ballots partyCandidates
        (STVQuota seats voters : ℝ) trace.steps partyInitialWeight :=
    fractionalSTVPartyWeightTraceLaw_of_indexedConcreteStepLaw_solidCoalition
      (voters := partyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
      (initialWeight := partyInitialWeight)
      (roundTally := hrun.roundTally) hpartySolid htraceSteps hpartyActive
      hpartyTallyEq
  have hotherWeightTrace :
      FractionalSTVPartyWeightTraceLaw otherPartyVoters ballots
        otherPartyCandidates (STVQuota seats voters : ℝ) trace.steps
        otherPartyInitialWeight :=
    fractionalSTVPartyWeightTraceLaw_of_indexedConcreteStepLaw_solidCoalition
      (voters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
      (initialWeight := otherPartyInitialWeight)
      (roundTally := hrun.roundTally) hotherSolid htraceSteps hotherActive
      hotherTallyEq
  have hglobalFinalNonneg :
      ∀ voter, voter ∈ allVoters →
        0 ≤
          fractionalSTVWeightAfterSteps allVoters ballots
            (STVQuota seats voters : ℝ) trace.steps initialWeight voter :=
    fractionalSTVWeightAfterSteps_nonneg
      (voters := allVoters) (ballots := ballots)
      (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
      (initialWeight := initialWeight)
      hrun.initialWeight_nonneg hquota_pos hrun.quota_if_elect
  have hpartyFinalWeightEq :
      ∀ voter, voter ∈ partyVoters →
        fractionalSTVWeightAfterSteps allVoters ballots
            (STVQuota seats voters : ℝ) trace.steps initialWeight voter =
          fractionalSTVWeightAfterSteps partyVoters ballots
            (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter :=
    fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
      (allVoters := allVoters) (voters := partyVoters)
      (otherVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
      (initialAllWeight := initialWeight)
      (initialWeight := partyInitialWeight)
      hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
      hotherSolid hpartyActive_mem hotherActive_mem hpartyInitialWeightEq
  have hvoterPartition_symm :
      allVoters = otherPartyVoters ∪ partyVoters := by
    rw [hvoterPartition, Finset.union_comm]
  have hotherFinalWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        fractionalSTVWeightAfterSteps allVoters ballots
            (STVQuota seats voters : ℝ) trace.steps initialWeight voter =
          fractionalSTVWeightAfterSteps otherPartyVoters ballots
            (STVQuota seats voters : ℝ) trace.steps otherPartyInitialWeight voter :=
    fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
      (allVoters := allVoters) (voters := otherPartyVoters)
      (otherVoters := partyVoters) (ballots := ballots)
      (partyCandidates := otherPartyCandidates)
      (otherPartyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
      (initialAllWeight := initialWeight)
      (initialWeight := otherPartyInitialWeight)
      hvoterPartition_symm hvoterDisjoint.symm hcandidateDisjoint.symm
      hotherSolid hpartySolid hotherActive_mem hpartyActive_mem
      hotherInitialWeightEq
  have hpartyTerminalWeightNonneg :
      0 ≤
        (∑ voter ∈ partyVoters,
          fractionalSTVWeightAfterSteps partyVoters ballots
            (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter) := by
    exact Finset.sum_nonneg fun voter hvoter => by
      rw [← hpartyFinalWeightEq voter hvoter]
      exact hglobalFinalNonneg voter (by
        rw [hvoterPartition]
        exact Finset.mem_union_left otherPartyVoters hvoter)
  have hotherTerminalWeightNonneg :
      0 ≤
        (∑ voter ∈ otherPartyVoters,
          fractionalSTVWeightAfterSteps otherPartyVoters ballots
            (STVQuota seats voters : ℝ) trace.steps
            otherPartyInitialWeight voter) := by
    exact Finset.sum_nonneg fun voter hvoter => by
      rw [← hotherFinalWeightEq voter hvoter]
      exact hglobalFinalNonneg voter (by
        rw [hvoterPartition]
        exact Finset.mem_union_right partyVoters hvoter)
  have hpartyTerminalSumEq :
      (∑ voter ∈ partyVoters,
          fractionalSTVWeightAfterSteps partyVoters ballots
            (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter) =
        (∑ voter ∈ partyVoters, partyInitialWeight voter) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) :=
    sum_fractionalSTVWeightAfterSteps_eq_sum_sub_partyElectStepCount
      (voters := partyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
      (initialWeight := partyInitialWeight) hquota_pos hpartyWeightTrace
  have hotherTerminalSumEq :
      (∑ voter ∈ otherPartyVoters,
          fractionalSTVWeightAfterSteps otherPartyVoters ballots
            (STVQuota seats voters : ℝ) trace.steps
            otherPartyInitialWeight voter) =
        (∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) :=
    sum_fractionalSTVWeightAfterSteps_eq_sum_sub_partyElectStepCount
      (voters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := otherPartyCandidates)
      (quota := (STVQuota seats voters : ℝ)) (steps := trace.steps)
      (initialWeight := otherPartyInitialWeight) hquota_pos hotherWeightTrace
  have hpartyDecomp :
      partyShare * (voters : ℝ) =
        (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) +
          (∑ voter ∈ partyVoters,
            fractionalSTVWeightAfterSteps partyVoters ballots
              (STVQuota seats voters : ℝ) trace.steps
              partyInitialWeight voter) := by
    have hsum :
        (∑ voter ∈ partyVoters, partyInitialWeight voter) =
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
              (STVQuota seats voters : ℝ) +
            (∑ voter ∈ partyVoters,
              fractionalSTVWeightAfterSteps partyVoters ballots
                (STVQuota seats voters : ℝ) trace.steps
                partyInitialWeight voter) := by
      rw [hpartyTerminalSumEq]
      ring
    exact hpartyInitialMass.trans hsum
  have hotherDecomp :
      (1 - partyShare) * (voters : ℝ) =
        (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) +
          (∑ voter ∈ otherPartyVoters,
            fractionalSTVWeightAfterSteps otherPartyVoters ballots
              (STVQuota seats voters : ℝ) trace.steps
              otherPartyInitialWeight voter) := by
    have hsum :
        (∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter) =
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
              (STVQuota seats voters : ℝ) +
            (∑ voter ∈ otherPartyVoters,
              fractionalSTVWeightAfterSteps otherPartyVoters ballots
                (STVQuota seats voters : ℝ) trace.steps
                otherPartyInitialWeight voter) := by
      rw [hotherTerminalSumEq]
      ring
    exact hotherInitialMass.trans hsum
  have hpartyWitness :
      QuotaLowerBoundWitness stvSeatCount
        (partyShare * (voters : ℝ)) (STVQuota seats voters : ℝ) :=
    ⟨partyElectStepCount partyCandidates trace.steps, hpartyElectCount,
      hquota_pos,
      (∑ voter ∈ partyVoters,
        fractionalSTVWeightAfterSteps partyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter),
      hpartyTerminalWeightNonneg, hpartyTerminalWeightBelow, hpartyDecomp⟩
  have hotherWitness :
      QuotaLowerBoundWitness otherPartySeatCount
        ((1 - partyShare) * (voters : ℝ)) (STVQuota seats voters : ℝ) :=
    ⟨partyElectStepCount otherPartyCandidates trace.steps, hotherElectCount,
      hquota_pos,
      (∑ voter ∈ otherPartyVoters,
        fractionalSTVWeightAfterSteps otherPartyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps otherPartyInitialWeight voter),
      hotherTerminalWeightNonneg, hotherTerminalWeightBelow, hotherDecomp⟩
  have hstv :
      stvSolidCoalitionQuotaWitnessBounds stvSeatCount partyShare seats voters :=
    ⟨otherPartySeatCount, htotal, hpos.le, hle, hvoters,
      hpartyWitness, hotherWitness⟩
  exact
    proposition1_seatSharesRounded_of_stvQuotaWitnessBounds_and_pavMinArgmax
      hpos hle hstv hpav

/--
Proposition 1 from the concrete generated fractional STV simulator trace.

The source model supplies the deterministic focus list and identifies the
candidate trace with the library simulator output.  The indexed executable
trace certificate is constructed internally from that generated run.
-/
theorem proposition1_seatSharesRounded_of_generatedFractionalSTVTrace_terminalWeights_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (focuses : List Candidate)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (htrace_generated :
      trace =
        fractionalSTVGeneratedTrace allVoters ballots
          (STVQuota seats voters : ℝ) focuses initialActive initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTerminalWeightBelow :
      (∑ voter ∈ partyVoters,
        fractionalSTVWeightAfterSteps partyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTerminalWeightBelow :
      (∑ voter ∈ otherPartyVoters,
        fractionalSTVWeightAfterSteps otherPartyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps otherPartyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  subst trace
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let hrun :=
    fractionalSTVIndexedExecutableTrace_of_generated allVoters ballots
      (STVQuota seats voters : ℝ) focuses initialActive initialWeight
      hquota_pos hinitialWeightNonneg
  exact
    proposition1_seatSharesRounded_of_indexedExecutableFractionalSTVTrace_terminalWeights_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate)
      (trace :=
        fractionalSTVGeneratedTrace allVoters ballots
          (STVQuota seats voters : ℝ) focuses initialActive initialWeight)
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (terminalActive :=
        fractionalSTVGeneratedTerminalActive allVoters ballots
          (STVQuota seats voters : ℝ) focuses initialActive initialWeight)
      initialWeight partyInitialWeight otherPartyInitialWeight
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid hrun hvoterPartition
      hvoterDisjoint hcandidateDisjoint hpartyInitialWeightEq
      hotherInitialWeightEq hpartyInitialMass hpartyActive
      hpartyTerminalWeightBelow hpartyElectCount hotherInitialMass hotherActive
      hotherTerminalWeightBelow hotherElectCount hpav

/--
Proposition 1 from the concrete choice-rule fractional STV simulator trace.

The source model supplies a deterministic STV choice rule and a finite round
budget. The simulator computes the focused-candidate sequence internally, then
the generated-run constructor builds the indexed executable trace certificate.
-/
theorem proposition1_seatSharesRounded_of_choiceRunFractionalSTVTrace_terminalWeights_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    (rounds : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (htrace_choice :
      trace =
        fractionalSTVChoiceRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) rounds initialActive initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTerminalWeightBelow :
      (∑ voter ∈ partyVoters,
        fractionalSTVWeightAfterSteps partyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTerminalWeightBelow :
      (∑ voter ∈ otherPartyVoters,
        fractionalSTVWeightAfterSteps otherPartyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps otherPartyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have htrace_generated :
      trace =
        fractionalSTVGeneratedTrace allVoters ballots
          (STVQuota seats voters : ℝ)
          (fractionalSTVChoiceRunFocuses choice allVoters ballots
            (STVQuota seats voters : ℝ) rounds initialActive initialWeight)
          initialActive initialWeight := by
    simpa [fractionalSTVChoiceRunTrace] using htrace_choice
  exact
    proposition1_seatSharesRounded_of_generatedFractionalSTVTrace_terminalWeights_and_pavMinArgmax
      (focuses :=
        fractionalSTVChoiceRunFocuses choice allVoters ballots
          (STVQuota seats voters : ℝ) rounds initialActive initialWeight)
      initialWeight partyInitialWeight otherPartyInitialWeight
      htrace_generated hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid hinitialWeightNonneg
      hvoterPartition hvoterDisjoint hcandidateDisjoint
      hpartyInitialWeightEq hotherInitialWeightEq hpartyInitialMass
      hpartyActive hpartyTerminalWeightBelow hpartyElectCount
      hotherInitialMass hotherActive hotherTerminalWeightBelow
      hotherElectCount hpav

/--
Proposition 1 from the concrete seat-limited fractional STV simulator trace.

The source model supplies the deterministic STV choice rule, the seat limit,
and a finite round budget. The simulator stops once the requested number of
election rounds has occurred, and the generated-run constructor builds the
indexed executable trace certificate internally.
-/
theorem proposition1_seatSharesRounded_of_seatRunFractionalSTVTrace_terminalWeights_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    (seatLimit rounds initialElected : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (htrace_seat :
      trace =
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seatLimit rounds initialElected
          initialActive initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTerminalWeightBelow :
      (∑ voter ∈ partyVoters,
        fractionalSTVWeightAfterSteps partyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps partyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTerminalWeightBelow :
      (∑ voter ∈ otherPartyVoters,
        fractionalSTVWeightAfterSteps otherPartyVoters ballots
          (STVQuota seats voters : ℝ) trace.steps otherPartyInitialWeight voter) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have htrace_generated :
      trace =
        fractionalSTVGeneratedTrace allVoters ballots
          (STVQuota seats voters : ℝ)
          (fractionalSTVSeatRunFocuses choice allVoters ballots
            (STVQuota seats voters : ℝ) seatLimit rounds initialElected
            initialActive initialWeight)
          initialActive initialWeight := by
    simpa [fractionalSTVSeatRunTrace] using htrace_seat
  exact
    proposition1_seatSharesRounded_of_generatedFractionalSTVTrace_terminalWeights_and_pavMinArgmax
      (focuses :=
        fractionalSTVSeatRunFocuses choice allVoters ballots
          (STVQuota seats voters : ℝ) seatLimit rounds initialElected
          initialActive initialWeight)
      initialWeight partyInitialWeight otherPartyInitialWeight
      htrace_generated hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid hinitialWeightNonneg
      hvoterPartition hvoterDisjoint hcandidateDisjoint
      hpartyInitialWeightEq hotherInitialWeightEq hpartyInitialMass
      hpartyActive hpartyTerminalWeightBelow hpartyElectCount
      hotherInitialMass hotherActive hotherTerminalWeightBelow
      hotherElectCount hpav

/--
Proposition 1 from a filled concrete total-seat fractional STV simulator run.

This route defines the STV party seat count as the number of same-party election
steps in the generated candidate-level trace.  When the total-seat run has
filled exactly `seats`, the library's total-weight residual theorem derives
the below-quota terminal residuals for both solid coalitions, so the proof no
longer needs final-count or terminal-exhaustion premises as separate inputs.
-/
theorem proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (rounds : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (htrace_seat :
      trace =
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hinitialTotalMass :
      (voters : ℝ) = ∑ voter ∈ allVoters, initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hfilled :
      partyElectStepCount partyCandidates trace.steps +
          partyElectStepCount otherPartyCandidates trace.steps =
        seats)
    (helectCount : electStepCount trace.steps = seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded (partyElectStepCount partyCandidates trace.steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  subst trace
  let quota : ℝ := STVQuota seats voters
  let traceRun :=
    fractionalSTVSeatRunTrace choice allVoters ballots quota seats rounds 0
      initialActive initialWeight
  let globalFinalWeight : Voter → ℝ :=
    fractionalSTVWeightAfterSteps allVoters ballots quota traceRun.steps
      initialWeight
  let partyFinalWeight : Voter → ℝ :=
    fractionalSTVWeightAfterSteps partyVoters ballots quota traceRun.steps
      partyInitialWeight
  let otherFinalWeight : Voter → ℝ :=
    fractionalSTVWeightAfterSteps otherPartyVoters ballots quota traceRun.steps
      otherPartyInitialWeight
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < quota := by
    dsimp [quota]
    exact_mod_cast hquota_pos_nat
  let hrun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      quota seats rounds 0 initialActive initialWeight hquota_pos
      hinitialWeightNonneg
  have hglobalBelow :
      (∑ voter ∈ allVoters, globalFinalWeight voter) < quota := by
    simpa [globalFinalWeight, traceRun, quota] using
      sum_fractionalSTVWeightAfterSteps_lt_STVQuota_of_electStepCount_eq
        (votersFin := allVoters) (ballots := ballots)
        (steps := traceRun.steps) (initialWeight := initialWeight)
        (seats := seats) (voters := voters) hinitialTotalMass
        (by simpa [traceRun] using helectCount)
        hrun.step_focus_active hrun.quota_if_elect
  have hglobalFinalNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ globalFinalWeight voter := by
    intro voter hvoter
    simpa [globalFinalWeight, traceRun, quota] using
      fractionalSTVWeightAfterSteps_nonneg
        (voters := allVoters) (ballots := ballots) (quota := quota)
        (steps := traceRun.steps) (initialWeight := initialWeight)
        hrun.initialWeight_nonneg hrun.quota_pos hrun.quota_if_elect
        voter hvoter
  have hpartyActive_mem :
      ∀ step, step ∈ traceRun.steps →
        ∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    simpa [traceRun] using hpartyActive ⟨n, by simpa [traceRun] using hn⟩
  have hotherActive_mem :
      ∀ step, step ∈ traceRun.steps →
        ∃ same, same ∈ otherPartyCandidates ∧ same ∈ step.beforeActive := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    simpa [traceRun] using hotherActive ⟨n, by simpa [traceRun] using hn⟩
  have hpartyFinalWeightEq :
      ∀ voter, voter ∈ partyVoters →
        globalFinalWeight voter = partyFinalWeight voter := by
    intro voter hvoter
    simpa [globalFinalWeight, partyFinalWeight, traceRun, quota] using
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := partyVoters)
        (otherVoters := otherPartyVoters) (ballots := ballots)
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        (quota := quota) (steps := traceRun.steps)
        (initialAllWeight := initialWeight)
        (initialWeight := partyInitialWeight)
        hvoterPartition hvoterDisjoint hcandidateDisjoint hpartySolid
        hotherSolid hpartyActive_mem hotherActive_mem hpartyInitialWeightEq
        voter hvoter
  have hvoterPartition_symm :
      allVoters = otherPartyVoters ∪ partyVoters := by
    rw [hvoterPartition, Finset.union_comm]
  have hotherFinalWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        globalFinalWeight voter = otherFinalWeight voter := by
    intro voter hvoter
    simpa [globalFinalWeight, otherFinalWeight, traceRun, quota] using
      fractionalSTVWeightAfterSteps_eq_on_solidCoalition_left_of_mem
        (allVoters := allVoters) (voters := otherPartyVoters)
        (otherVoters := partyVoters) (ballots := ballots)
        (partyCandidates := otherPartyCandidates)
        (otherPartyCandidates := partyCandidates)
        (quota := quota) (steps := traceRun.steps)
        (initialAllWeight := initialWeight)
        (initialWeight := otherPartyInitialWeight)
        hvoterPartition_symm hvoterDisjoint.symm hcandidateDisjoint.symm
        hotherSolid hpartySolid hotherActive_mem hpartyActive_mem
        hotherInitialWeightEq voter hvoter
  have hglobalFinalSumUnion :
      (∑ voter ∈ allVoters, globalFinalWeight voter) =
        (∑ voter ∈ partyVoters, globalFinalWeight voter) +
          (∑ voter ∈ otherPartyVoters, globalFinalWeight voter) := by
    rw [hvoterPartition]
    exact Finset.sum_union hvoterDisjoint
  have hpartyTerminalLeGlobal :
      (∑ voter ∈ partyVoters, partyFinalWeight voter) ≤
        ∑ voter ∈ allVoters, globalFinalWeight voter := by
    have hpartyEq :
        (∑ voter ∈ partyVoters, partyFinalWeight voter) =
          ∑ voter ∈ partyVoters, globalFinalWeight voter := by
      apply Finset.sum_congr rfl
      intro voter hvoter
      exact (hpartyFinalWeightEq voter hvoter).symm
    have hotherNonneg :
        0 ≤ ∑ voter ∈ otherPartyVoters, globalFinalWeight voter :=
      Finset.sum_nonneg fun voter hvoter =>
        hglobalFinalNonneg voter (by
          rw [hvoterPartition]
          exact Finset.mem_union_right partyVoters hvoter)
    calc
      (∑ voter ∈ partyVoters, partyFinalWeight voter)
          = ∑ voter ∈ partyVoters, globalFinalWeight voter := hpartyEq
      _ ≤ (∑ voter ∈ partyVoters, globalFinalWeight voter) +
            ∑ voter ∈ otherPartyVoters, globalFinalWeight voter := by
          linarith
      _ = ∑ voter ∈ allVoters, globalFinalWeight voter :=
          hglobalFinalSumUnion.symm
  have hotherTerminalLeGlobal :
      (∑ voter ∈ otherPartyVoters, otherFinalWeight voter) ≤
        ∑ voter ∈ allVoters, globalFinalWeight voter := by
    have hotherEq :
        (∑ voter ∈ otherPartyVoters, otherFinalWeight voter) =
          ∑ voter ∈ otherPartyVoters, globalFinalWeight voter := by
      apply Finset.sum_congr rfl
      intro voter hvoter
      exact (hotherFinalWeightEq voter hvoter).symm
    have hpartyNonneg :
        0 ≤ ∑ voter ∈ partyVoters, globalFinalWeight voter :=
      Finset.sum_nonneg fun voter hvoter =>
        hglobalFinalNonneg voter (by
          rw [hvoterPartition]
          exact Finset.mem_union_left otherPartyVoters hvoter)
    calc
      (∑ voter ∈ otherPartyVoters, otherFinalWeight voter)
          = ∑ voter ∈ otherPartyVoters, globalFinalWeight voter := hotherEq
      _ ≤ (∑ voter ∈ partyVoters, globalFinalWeight voter) +
            ∑ voter ∈ otherPartyVoters, globalFinalWeight voter := by
          linarith
      _ = ∑ voter ∈ allVoters, globalFinalWeight voter :=
          hglobalFinalSumUnion.symm
  have hpartyTerminalBelow :
      (∑ voter ∈ partyVoters, partyFinalWeight voter) < quota :=
    lt_of_le_of_lt hpartyTerminalLeGlobal hglobalBelow
  have hotherTerminalBelow :
      (∑ voter ∈ otherPartyVoters, otherFinalWeight voter) < quota :=
    lt_of_le_of_lt hotherTerminalLeGlobal hglobalBelow
  simpa [traceRun, quota, partyFinalWeight, otherFinalWeight] using
    (proposition1_seatSharesRounded_of_seatRunFractionalSTVTrace_terminalWeights_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate)
      (trace := traceRun) choice seats rounds 0 initialWeight
      partyInitialWeight otherPartyInitialWeight
      (stvSeatCount := partyElectStepCount partyCandidates traceRun.steps)
      (otherPartySeatCount :=
        partyElectStepCount otherPartyCandidates traceRun.steps)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) (by rfl) hpos hle
      (by simpa [traceRun] using hfilled) hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid hinitialWeightNonneg
      hvoterPartition hvoterDisjoint hcandidateDisjoint hpartyInitialWeightEq
      hotherInitialWeightEq hpartyInitialMass
      (by simpa [traceRun] using hpartyActive) hpartyTerminalBelow
      (Nat.le_refl _) hotherInitialMass
      (by simpa [traceRun] using hotherActive) hotherTerminalBelow
      (Nat.le_refl _) hpav)

/--
Filled total-seat simulator route where the party fill equation is derived
from the source trace: every election step focuses on a candidate in one of the
two disjoint parties, and the generated run has exactly `seats` election steps.
-/
theorem proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_electFocuses_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (rounds : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (htrace_seat :
      trace =
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hinitialTotalMass :
      (voters : ℝ) = ∑ voter ∈ allVoters, initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (helectFocusMem :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.elect →
        ∃ focused, step.focus = some focused ∧
          (focused ∈ partyCandidates ∨
            focused ∈ otherPartyCandidates))
    (helectCount : electStepCount trace.steps = seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded (partyElectStepCount partyCandidates trace.steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have hfilled :
      partyElectStepCount partyCandidates trace.steps +
          partyElectStepCount otherPartyCandidates trace.steps =
        seats := by
    rw [
      partyElectStepCount_add_eq_electStepCount_of_disjoint_of_elect_focus_mem
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        hcandidateDisjoint trace.steps helectFocusMem,
      helectCount]
  exact
    proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (trace := trace) choice
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) rounds initialWeight
      partyInitialWeight otherPartyInitialWeight
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) htrace_seat hpos hle hvoters
      hpartyCandidates hotherPartyCandidates hpartySolid hotherSolid
      hinitialWeightNonneg hinitialTotalMass hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialWeightEq hotherInitialWeightEq
      hpartyInitialMass hotherInitialMass hpartyActive hotherActive
      hfilled helectCount hpav

/--
Filled total-seat simulator route deriving elected-focus party membership from
the source candidate universe: every initial active candidate is in one of the
two parties, and replayed executable STV steps only remove focused candidates.
-/
theorem proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_initialActiveCovered_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (rounds : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (htrace_seat :
      trace =
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hinitialTotalMass :
      (voters : ℝ) = ∑ voter ∈ allVoters, initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hinitialActiveSubset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (helectCount : electStepCount trace.steps = seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded (partyElectStepCount partyCandidates trace.steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  subst trace
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let hrun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
      hquota_pos hinitialWeightNonneg
  have helectFocusMem :
      ∀ step,
        step ∈
            (fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) seats rounds 0 initialActive
              initialWeight).steps →
          step.kind = StepKind.elect →
            ∃ focused, step.focus = some focused ∧
              (focused ∈ partyCandidates ∨
                focused ∈ otherPartyCandidates) :=
    FractionalSTVIndexedExecutableTrace.elect_focus_mem_of_initialActive_subset_union
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      hrun hinitialActiveSubset
  exact
    proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_electFocuses_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate)
      (trace :=
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      choice (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (allVoters := allVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) rounds initialWeight
      partyInitialWeight otherPartyInitialWeight
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) (by rfl) hpos hle hvoters
      hpartyCandidates hotherPartyCandidates hpartySolid hotherSolid
      hinitialWeightNonneg hinitialTotalMass hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialWeightEq hotherInitialWeightEq
      hpartyInitialMass hotherInitialMass hpartyActive hotherActive
      helectFocusMem helectCount hpav

/--
Filled total-seat simulator route deriving the per-step party-active witnesses
from terminal active same-party candidates and the executable active-set replay.
-/
theorem proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_terminalActive_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (rounds : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (htrace_seat :
      trace =
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hinitialTotalMass :
      (voters : ℝ) = ∑ voter ∈ allVoters, initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hinitialActiveSubset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyTerminalActive :
      ∃ same, same ∈ partyCandidates ∧
        same ∈
          fractionalSTVSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight)
    (hotherTerminalActive :
      ∃ same, same ∈ otherPartyCandidates ∧
        same ∈
          fractionalSTVSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (helectCount : electStepCount trace.steps = seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded (partyElectStepCount partyCandidates trace.steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  subst trace
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast hquota_pos_nat
  let hrun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      (STVQuota seats voters : ℝ) seats rounds 0 initialActive initialWeight
      hquota_pos hinitialWeightNonneg
  have hremove :
      ∀ step,
        step ∈
            (fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) seats rounds 0 initialActive
              initialWeight).steps →
          step.removesFocusedCandidate := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact hrun.step_removes ⟨n, hn⟩
  have hpartyActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight).steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) seats rounds 0 initialActive
              initialWeight).steps.get i).beforeActive :=
    step_activePartyWitness_of_terminal_activePartyCandidate
      (trace :=
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      (startActive := initialActive)
      (terminalActive :=
        fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      (partyCandidates := partyCandidates)
      hrun.activeReplay hremove hpartyTerminalActive
  have hotherActive :
      ∀ i : Fin
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight).steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈
            ((fractionalSTVSeatRunTrace choice allVoters ballots
              (STVQuota seats voters : ℝ) seats rounds 0 initialActive
              initialWeight).steps.get i).beforeActive :=
    step_activePartyWitness_of_terminal_activePartyCandidate
      (trace :=
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      (startActive := initialActive)
      (terminalActive :=
        fractionalSTVSeatRunTerminalActive choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      (partyCandidates := otherPartyCandidates)
      hrun.activeReplay hremove hotherTerminalActive
  exact
    proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_initialActiveCovered_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate)
      (trace :=
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      choice (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (allVoters := allVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) rounds initialWeight
      partyInitialWeight otherPartyInitialWeight
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) (by rfl) hpos hle hvoters
      hpartyCandidates hotherPartyCandidates hpartySolid hotherSolid
      hinitialWeightNonneg hinitialTotalMass hvoterPartition hvoterDisjoint
      hcandidateDisjoint hinitialActiveSubset hpartyInitialWeightEq
      hotherInitialWeightEq hpartyInitialMass hotherInitialMass hpartyActive
      hotherActive (by simpa using helectCount) hpav

/--
Filled total-seat simulator route closed from executable fractional STV source
dynamics. The lower-bound party processes are terminated by comparing their
residual vote mass with the concrete global post-run voter weights, so the
theorem does not need per-step party-active witnesses or terminal party
exhaustion as inputs.
-/
theorem proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_globalWeightTerminal_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (rounds : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (htrace_seat :
      trace =
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hinitialTotalMass :
      (voters : ℝ) = ∑ voter ∈ allVoters, initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (helectCount : electStepCount trace.steps = seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded (partyElectStepCount partyCandidates trace.steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  subst trace
  let quota : ℝ := STVQuota seats voters
  let traceRun :=
    fractionalSTVSeatRunTrace choice allVoters ballots quota seats rounds 0
      initialActive initialWeight
  let terminalActive :=
    fractionalSTVSeatRunTerminalActive choice allVoters ballots quota seats
      rounds 0 initialActive initialWeight
  let focuses :=
    fractionalSTVSeatRunFocuses choice allVoters ballots quota seats rounds 0
      initialActive initialWeight
  let rule :=
    fractionalSTVGeneratedTransferRule allVoters ballots quota focuses
      initialActive initialWeight
  let globalFinalWeight : Voter → ℝ :=
    fractionalSTVWeightAfterSteps allVoters ballots quota traceRun.steps
      initialWeight
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < quota := by
    dsimp [quota]
    exact_mod_cast hquota_pos_nat
  let indexedRun :=
    fractionalSTVIndexedExecutableTrace_of_seatRun choice allVoters ballots
      quota seats rounds 0 initialActive initialWeight hquota_pos
      hinitialWeightNonneg
  have hruleTallyEq :
      ∀ i : Fin traceRun.steps.length, ∀ candidate,
        candidate ∈ (traceRun.steps.get i).beforeActive →
          rule.fractionalTally (traceRun.steps.get i) candidate =
            indexedRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [traceRun, rule, indexedRun, focuses, quota,
      fractionalSTVSeatRunTrace, fractionalSTVIndexedExecutableTrace_of_seatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots quota
        focuses initialActive initialWeight i candidate
  have hexec :
      FractionalSTVExecutableTrace rule traceRun allVoters ballots quota
        initialActive terminalActive initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := rule) indexedRun hruleTallyEq
  have hglobalBelow :
      (∑ voter ∈ allVoters, globalFinalWeight voter) < quota := by
    simpa [globalFinalWeight, traceRun, quota] using
      sum_fractionalSTVWeightAfterSteps_lt_STVQuota_of_electStepCount_eq
        (votersFin := allVoters) (ballots := ballots)
        (steps := traceRun.steps) (initialWeight := initialWeight)
        (seats := seats) (voters := voters) hinitialTotalMass
        (by simpa [traceRun] using helectCount)
        indexedRun.step_focus_active indexedRun.quota_if_elect
  have hglobalFinalNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ globalFinalWeight voter := by
    intro voter hvoter
    simpa [globalFinalWeight, traceRun, quota] using
      fractionalSTVWeightAfterSteps_nonneg
        (voters := allVoters) (ballots := ballots) (quota := quota)
        (steps := traceRun.steps) (initialWeight := initialWeight)
        indexedRun.initialWeight_nonneg indexedRun.quota_pos
        indexedRun.quota_if_elect voter hvoter
  have hpartySubsetAll : partyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_left otherPartyVoters hvoter
  have hotherSubsetAll : otherPartyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_right partyVoters hvoter
  have hglobalFinalSumUnion :
      (∑ voter ∈ allVoters, globalFinalWeight voter) =
        (∑ voter ∈ partyVoters, globalFinalWeight voter) +
          (∑ voter ∈ otherPartyVoters, globalFinalWeight voter) := by
    rw [hvoterPartition]
    exact Finset.sum_union hvoterDisjoint
  have hpartyGlobalBelow :
      (∑ voter ∈ partyVoters, globalFinalWeight voter) < quota := by
    have hotherNonneg :
        0 ≤ ∑ voter ∈ otherPartyVoters, globalFinalWeight voter :=
      Finset.sum_nonneg fun voter hvoter =>
        hglobalFinalNonneg voter (hotherSubsetAll hvoter)
    have hle :
        (∑ voter ∈ partyVoters, globalFinalWeight voter) ≤
          ∑ voter ∈ allVoters, globalFinalWeight voter := by
      calc
        (∑ voter ∈ partyVoters, globalFinalWeight voter)
            ≤ (∑ voter ∈ partyVoters, globalFinalWeight voter) +
                ∑ voter ∈ otherPartyVoters, globalFinalWeight voter := by
              linarith
        _ = ∑ voter ∈ allVoters, globalFinalWeight voter :=
              hglobalFinalSumUnion.symm
    exact lt_of_le_of_lt hle hglobalBelow
  have hotherGlobalBelow :
      (∑ voter ∈ otherPartyVoters, globalFinalWeight voter) < quota := by
    have hpartyNonneg :
        0 ≤ ∑ voter ∈ partyVoters, globalFinalWeight voter :=
      Finset.sum_nonneg fun voter hvoter =>
        hglobalFinalNonneg voter (hpartySubsetAll hvoter)
    have hle :
        (∑ voter ∈ otherPartyVoters, globalFinalWeight voter) ≤
          ∑ voter ∈ allVoters, globalFinalWeight voter := by
      calc
        (∑ voter ∈ otherPartyVoters, globalFinalWeight voter)
            ≤ (∑ voter ∈ partyVoters, globalFinalWeight voter) +
                ∑ voter ∈ otherPartyVoters, globalFinalWeight voter := by
              linarith
        _ = ∑ voter ∈ allVoters, globalFinalWeight voter :=
              hglobalFinalSumUnion.symm
    exact lt_of_le_of_lt hle hglobalBelow
  have hfullNoquotaOnEliminate :
      ∀ i : Fin traceRun.steps.length,
        (traceRun.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈ (traceRun.steps.get i).beforeActive →
              rule.fractionalTally (traceRun.steps.get i) candidate < quota := by
    intro i hkind candidate hcandidate
    have hround_lt :
        indexedRun.roundTally i candidate < quota := by
      simpa [traceRun, indexedRun, quota] using
        fractionalSTVIndexedExecutableTrace_of_seatRun_get_noquota_if_eliminate
          choice allVoters ballots quota seats rounds 0 initialActive
          initialWeight hquota_pos hinitialWeightNonneg hchoiceRespect i
          candidate hcandidate hkind
    rw [hruleTallyEq i candidate hcandidate]
    exact hround_lt
  have hpartyNoquotaOnEliminate :
      ∀ i : Fin traceRun.steps.length,
        (traceRun.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (traceRun.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (traceRun.steps.get i) candidate < quota := by
    intro i hkind candidate hcandidate
    exact hfullNoquotaOnEliminate i hkind candidate
      (Finset.mem_filter.mp hcandidate).1
  have hotherNoquotaOnEliminate :
      ∀ i : Fin traceRun.steps.length,
        (traceRun.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (traceRun.steps.get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally (traceRun.steps.get i) candidate < quota := by
    intro i hkind candidate hcandidate
    exact hfullNoquotaOnEliminate i hkind candidate
      (Finset.mem_filter.mp hcandidate).1
  have hpartyInitialMassGlobal :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, initialWeight voter := by
    calc
      partyShare * (voters : ℝ)
          = ∑ voter ∈ partyVoters, partyInitialWeight voter :=
            hpartyInitialMass
      _ = ∑ voter ∈ partyVoters, initialWeight voter := by
          refine Finset.sum_congr rfl ?_
          intro voter hvoter
          exact (hpartyInitialWeightEq voter hvoter).symm
  have hotherInitialMassGlobal :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, initialWeight voter := by
    calc
      (1 - partyShare) * (voters : ℝ)
          = ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter :=
            hotherInitialMass
      _ = ∑ voter ∈ otherPartyVoters, initialWeight voter := by
          refine Finset.sum_congr rfl ?_
          intro voter hvoter
          exact (hotherInitialWeightEq voter hvoter).symm
  have hpartyStartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))) := by
    simpa [quota] using
      partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
        (seats := seats) (voters := voters)
        (remainingCandidates := partyCandidates.card)
        (partyShare := partyShare) hle hpartyCandidates
  have hotherShare_le : 1 - partyShare ≤ 1 := by
    linarith [hpos]
  have hotherStartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) := by
    simpa [quota] using
      partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
        (seats := seats) (voters := voters)
        (remainingCandidates := otherPartyCandidates.card)
        (partyShare := 1 - partyShare) hotherShare_le hotherPartyCandidates
  have hpartyStartRemaining :
      (PartyQuotaStartState partyCandidates.card
        (partyShare * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card := by
    simp [PartyQuotaStartState,
      activePartyCandidates_card_eq_of_subset hpartyInitialActive]
  have hotherStartRemaining :
      (PartyQuotaStartState otherPartyCandidates.card
        ((1 - partyShare) * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive otherPartyCandidates).card := by
    simp [PartyQuotaStartState,
      activePartyCandidates_card_eq_of_subset hotherInitialActive]
  have hpartyTerminal :
      PartyQuotaTerminalBelowQuota quota
        (partyTransferPreservationTerminalState partyCandidates quota
          rule.fractionalTally traceRun.steps
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))) := by
    exact
      terminalBelowQuota_of_replaySteps_lowerBound_globalWeight_lt
        (allVoters := allVoters) (partyVoters := partyVoters)
        (ballots := ballots) (partyCandidates := partyCandidates)
        (quota := quota) (fractionalTally := rule.fractionalTally)
        (steps := traceRun.steps) (startActive := initialActive)
        (terminalActive := terminalActive) (initialWeight := initialWeight)
        (startState :=
          PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))
        hpartySolid hpartySubsetAll hinitialWeightNonneg hquota_pos
        (FractionalSTVExecutableTrace.concreteStepLaw hexec) hexec.tally_eq
        hexec.activeReplay hpartyStartCapacity hpartyStartRemaining
        (by
          intro _hremaining_pos
          simpa [PartyQuotaStartState, hpartyInitialMassGlobal])
        hpartyNoquotaOnEliminate hpartyGlobalBelow
  have hotherTerminal :
      PartyQuotaTerminalBelowQuota quota
        (partyTransferPreservationTerminalState otherPartyCandidates quota
          rule.fractionalTally traceRun.steps
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))) := by
    exact
      terminalBelowQuota_of_replaySteps_lowerBound_globalWeight_lt
        (allVoters := allVoters) (partyVoters := otherPartyVoters)
        (ballots := ballots) (partyCandidates := otherPartyCandidates)
        (quota := quota) (fractionalTally := rule.fractionalTally)
        (steps := traceRun.steps) (startActive := initialActive)
        (terminalActive := terminalActive) (initialWeight := initialWeight)
        (startState :=
          PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))
        hotherSolid hotherSubsetAll hinitialWeightNonneg hquota_pos
        (FractionalSTVExecutableTrace.concreteStepLaw hexec) hexec.tally_eq
        hexec.activeReplay hotherStartCapacity hotherStartRemaining
        (by
          intro _hremaining_pos
          simpa [PartyQuotaStartState, hotherInitialMassGlobal])
        hotherNoquotaOnEliminate hotherGlobalBelow
  have hpartyVotesNonneg : 0 ≤ partyShare * (voters : ℝ) :=
    mul_nonneg hpos.le (by positivity)
  have hotherVotesNonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  have hpartyLower :
      ⌊(partyShare * (voters : ℝ)) / quota⌋₊ ≤
        partyElectStepCount partyCandidates traceRun.steps :=
    floor_votes_div_quota_le_partyElectStepCount_of_terminalBelowQuota
      (partyCandidates := partyCandidates) (quota := quota)
      (initialVotes := partyShare * (voters : ℝ))
      (fractionalTally := rule.fractionalTally)
      (steps := traceRun.steps) hquota_pos hpartyVotesNonneg hpartyTerminal
  have hotherLower :
      ⌊((1 - partyShare) * (voters : ℝ)) / quota⌋₊ ≤
        partyElectStepCount otherPartyCandidates traceRun.steps :=
    floor_votes_div_quota_le_partyElectStepCount_of_terminalBelowQuota
      (partyCandidates := otherPartyCandidates) (quota := quota)
      (initialVotes := (1 - partyShare) * (voters : ℝ))
      (fractionalTally := rule.fractionalTally)
      (steps := traceRun.steps) hquota_pos hotherVotesNonneg hotherTerminal
  have helectFocusMem :
      ∀ step, step ∈ traceRun.steps → step.kind = StepKind.elect →
        ∃ focused, step.focus = some focused ∧
          (focused ∈ partyCandidates ∨
            focused ∈ otherPartyCandidates) :=
    FractionalSTVIndexedExecutableTrace.elect_focus_mem_of_initialActive_subset_union
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      indexedRun hinitialActiveSubset
  have hfilled :
      partyElectStepCount partyCandidates traceRun.steps +
          partyElectStepCount otherPartyCandidates traceRun.steps =
        seats := by
    have helectCountTrace : electStepCount traceRun.steps = seats := by
      simpa [traceRun] using helectCount
    rw [
      partyElectStepCount_add_eq_electStepCount_of_disjoint_of_elect_focus_mem
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        hcandidateDisjoint traceRun.steps helectFocusMem,
      helectCountTrace]
  have hquotaLower :
      stvSolidCoalitionQuotaLowerBounds
        (partyElectStepCount partyCandidates traceRun.steps) partyShare seats
        voters := by
    refine ⟨partyElectStepCount otherPartyCandidates traceRun.steps,
      hfilled, hpos.le, hle, hvoters, ?_, ?_⟩
    · simpa [quota, mul_div_assoc] using hpartyLower
    · simpa [quota, mul_div_assoc] using hotherLower
  simpa [traceRun, quota] using
    proposition1_seatSharesRounded_of_stvQuotaLowerBounds_and_pavMinArgmax
      (stvSeatCount := partyElectStepCount partyCandidates traceRun.steps)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hquotaLower hpav

/--
Generated filled total-seat simulator route: the theorem is stated directly
on the executable fractional STV seat-run trace, so no separate trace object or
trace-equality premise remains.
-/
theorem proposition1_seatSharesRounded_of_generatedFilledSeatRunFractionalSTVTrace_globalWeightTerminal_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (rounds : ℕ)
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hinitialTotalMass :
      (voters : ℝ) = ∑ voter ∈ allVoters, initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (helectCount :
      electStepCount
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight).steps = seats)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded
        (partyElectStepCount partyCandidates
          (fractionalSTVSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats rounds 0 initialActive
            initialWeight).steps)
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  exact
    proposition1_seatSharesRounded_of_filledSeatRunFractionalSTVTrace_globalWeightTerminal_and_pavMinArgmax
      (trace :=
        fractionalSTVSeatRunTrace choice allVoters ballots
          (STVQuota seats voters : ℝ) seats rounds 0 initialActive
          initialWeight)
      choice (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (allVoters := allVoters)
      (ballots := ballots) (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) rounds initialWeight
      partyInitialWeight otherPartyInitialWeight
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) rfl hpos hle hvoters hchoiceRespect
      hpartyCandidates hotherPartyCandidates hpartySolid hotherSolid
      hinitialWeightNonneg hinitialTotalMass hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherInitialActive
      hinitialActiveSubset hpartyInitialWeightEq hotherInitialWeightEq
      hpartyInitialMass hotherInitialMass helectCount hpav

/--
Generated filled-seat simulator route from source primitives.

This version uses the source filled-seat convention directly: quota-election
rounds and terminal active fills are counted by `partyFilledSeatCount`, and the
round budget is the initial active-candidate count. A total, quota-respecting
choice rule supplies the source runner; no external elected-count premise is
needed.
-/
theorem proposition1_seatSharesRounded_of_generatedFilledSeatRunFractionalSTVTrace_globalWeightTerminal_and_pavMinArgmax_of_total
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (choice : FractionalSTVChoiceRule Candidate)
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (htotalChoice : choice.Total)
    (hchoiceRespect : choice.QuotaRespecting (STVQuota seats voters : ℝ))
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hinitialTotalMass :
      (voters : ℝ) = ∑ voter ∈ allVoters, initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded
        (partyFilledSeatCount partyCandidates seats
          (fractionalSTVFilledSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats initialActive.card 0
            initialActive initialWeight).steps
          (fractionalSTVFilledSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) seats initialActive.card 0
            initialActive initialWeight))
        partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  let quota : ℝ := STVQuota seats voters
  let traceRun :=
    fractionalSTVFilledSeatRunTrace choice allVoters ballots quota seats
      initialActive.card 0 initialActive initialWeight
  let terminalActive :=
    fractionalSTVFilledSeatRunTerminalActive choice allVoters ballots quota
      seats initialActive.card 0 initialActive initialWeight
  let focuses :=
    fractionalSTVFilledSeatRunFocuses choice allVoters ballots quota seats
      initialActive.card 0 initialActive initialWeight
  let rule :=
    fractionalSTVGeneratedTransferRule allVoters ballots quota focuses
      initialActive initialWeight
  have hquota_pos_nat : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos : 0 < quota := by
    dsimp [quota]
    exact_mod_cast hquota_pos_nat
  let indexedRun :=
    fractionalSTVIndexedExecutableTrace_of_filledSeatRun choice allVoters
      ballots quota seats initialActive.card 0 initialActive initialWeight
      hquota_pos hinitialWeightNonneg
  have hruleTallyEq :
      ∀ i : Fin traceRun.steps.length, ∀ candidate,
        candidate ∈ (traceRun.steps.get i).beforeActive →
          rule.fractionalTally (traceRun.steps.get i) candidate =
            indexedRun.roundTally i candidate := by
    intro i candidate _hcandidate
    simpa [traceRun, rule, indexedRun, focuses, quota,
      fractionalSTVFilledSeatRunTrace,
      fractionalSTVIndexedExecutableTrace_of_filledSeatRun,
      fractionalSTVIndexedExecutableTrace_of_generated] using
      fractionalSTVGeneratedTransferRule_tally_eq allVoters ballots quota
        focuses initialActive initialWeight i candidate
  have hexec :
      FractionalSTVExecutableTrace rule traceRun allVoters ballots quota
        initialActive terminalActive initialWeight :=
    fractionalSTVExecutableTrace_of_indexedRoundTallyEq
      (rule := rule) indexedRun hruleTallyEq
  have hpartySubsetAll : partyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_left otherPartyVoters hvoter
  have hotherSubsetAll : otherPartyVoters ⊆ allVoters := by
    intro voter hvoter
    rw [hvoterPartition]
    exact Finset.mem_union_right partyVoters hvoter
  have hpartyStartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState partyCandidates.card
          (partyShare * (voters : ℝ))) := by
    simpa [quota] using
      partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
        (seats := seats) (voters := voters)
        (remainingCandidates := partyCandidates.card)
        (partyShare := partyShare) hle hpartyCandidates
  have hotherShare_le : 1 - partyShare ≤ 1 := by
    linarith [hpos]
  have hotherStartCapacity :
      PartyQuotaCapacityBound quota
        (PartyQuotaStartState otherPartyCandidates.card
          ((1 - partyShare) * (voters : ℝ))) := by
    simpa [quota] using
      partyQuotaStartCapacityBound_of_share_le_one_candidate_bound
        (seats := seats) (voters := voters)
        (remainingCandidates := otherPartyCandidates.card)
        (partyShare := 1 - partyShare) hotherShare_le hotherPartyCandidates
  have hpartyStartRemaining :
      (PartyQuotaStartState partyCandidates.card
        (partyShare * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive partyCandidates).card := by
    simp [PartyQuotaStartState,
      activePartyCandidates_card_eq_of_subset hpartyInitialActive]
  have hotherStartRemaining :
      (PartyQuotaStartState otherPartyCandidates.card
        ((1 - partyShare) * (voters : ℝ))).remainingCandidates =
        (activePartyCandidates initialActive otherPartyCandidates).card := by
    simp [PartyQuotaStartState,
      activePartyCandidates_card_eq_of_subset hotherInitialActive]
  have hfullNoquotaOnEliminate :
      ∀ i : Fin traceRun.steps.length,
        (traceRun.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈ (traceRun.steps.get i).beforeActive →
              rule.fractionalTally (traceRun.steps.get i) candidate < quota := by
    intro i hkind candidate hcandidate
    have hround_lt :
        indexedRun.roundTally i candidate < quota := by
      simpa [traceRun, indexedRun, quota] using
        fractionalSTVIndexedExecutableTrace_of_filledSeatRun_get_noquota_if_eliminate
          choice allVoters ballots quota seats initialActive.card 0
          initialActive initialWeight hquota_pos hinitialWeightNonneg
          hchoiceRespect i candidate hcandidate hkind
    rw [hruleTallyEq i candidate hcandidate]
    exact hround_lt
  have hpartyNoquotaOnEliminate :
      ∀ i : Fin traceRun.steps.length,
        (traceRun.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (traceRun.steps.get i).beforeActive
                  partyCandidates →
              rule.fractionalTally (traceRun.steps.get i) candidate < quota := by
    intro i hkind candidate hcandidate
    exact hfullNoquotaOnEliminate i hkind candidate
      (Finset.mem_filter.mp hcandidate).1
  have hotherNoquotaOnEliminate :
      ∀ i : Fin traceRun.steps.length,
        (traceRun.steps.get i).kind = StepKind.eliminate →
          ∀ candidate,
            candidate ∈
                activePartyCandidates (traceRun.steps.get i).beforeActive
                  otherPartyCandidates →
              rule.fractionalTally (traceRun.steps.get i) candidate < quota := by
    intro i hkind candidate hcandidate
    exact hfullNoquotaOnEliminate i hkind candidate
      (Finset.mem_filter.mp hcandidate).1
  have hpartyVotesNonneg : 0 ≤ partyShare * (voters : ℝ) :=
    mul_nonneg hpos.le (by positivity)
  have hotherVotesNonneg : 0 ≤ (1 - partyShare) * (voters : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  have hseatsInitialActive : seats ≤ initialActive.card :=
    le_trans hpartyCandidates (Finset.card_le_card hpartyInitialActive)
  have hfilledTotal :
      electStepCount traceRun.steps +
          (terminalFillActive seats traceRun.steps terminalActive).card =
        seats := by
    simpa [traceRun, terminalActive, quota] using
      electStepCount_add_terminalFillActive_card_fractionalSTVFilledSeatRunTrace_eq_seatLimit_of_total
        choice allVoters ballots quota seats initialActive initialWeight
        htotalChoice hseatsInitialActive
  have hremove_mem :
      ∀ step, step ∈ traceRun.steps → step.removesFocusedCandidate := by
    intro step hstep
    rcases List.getElem_of_mem hstep with ⟨n, hn, hget⟩
    subst hget
    exact indexedRun.step_removes ⟨n, hn⟩
  have hterminal_subset_initial :
      terminalActive ⊆ initialActive :=
    STVTrace.terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
      indexedRun.activeReplay
      (fun step hstep =>
        STVTrace.activeMonotone_of_removesFocusedCandidate
          (hremove_mem step hstep))
  have hterminalFill_subset :
      terminalFillActive seats traceRun.steps terminalActive ⊆
        partyCandidates ∪ otherPartyCandidates := by
    intro candidate hcandidate
    apply hinitialActiveSubset
    by_cases hlt : electStepCount traceRun.steps < seats
    · have hterminal : candidate ∈ terminalActive := by
        simpa [terminalFillActive, hlt] using hcandidate
      exact hterminal_subset_initial hterminal
    · simpa [terminalFillActive, hlt] using hcandidate
  have helectFocusMem :
      ∀ step, step ∈ traceRun.steps → step.kind = StepKind.elect →
        ∃ focused, step.focus = some focused ∧
          (focused ∈ partyCandidates ∨
            focused ∈ otherPartyCandidates) :=
    FractionalSTVIndexedExecutableTrace.elect_focus_mem_of_initialActive_subset_union
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      indexedRun hinitialActiveSubset
  have hfilled :
      partyFilledSeatCount partyCandidates seats traceRun.steps terminalActive +
          partyFilledSeatCount otherPartyCandidates seats traceRun.steps
            terminalActive =
        seats := by
    rw [
      partyFilledSeatCount_add_eq_electStepCount_add_terminalFillActive_card
        (partyCandidates := partyCandidates)
        (otherPartyCandidates := otherPartyCandidates)
        (seatLimit := seats) (steps := traceRun.steps)
        (terminalActive := terminalActive) hcandidateDisjoint helectFocusMem
        hterminalFill_subset,
      hfilledTotal]
  have hglobalFinalNonneg :
      ∀ voter, voter ∈ allVoters →
        0 ≤
          fractionalSTVWeightAfterSteps allVoters ballots quota traceRun.steps
            initialWeight voter := by
    intro voter hvoter
    exact
      fractionalSTVWeightAfterSteps_nonneg
        (voters := allVoters) (ballots := ballots) (quota := quota)
        (steps := traceRun.steps) (initialWeight := initialWeight)
        indexedRun.initialWeight_nonneg indexedRun.quota_pos
        indexedRun.quota_if_elect voter hvoter
  have hglobalBelow_of_full :
      electStepCount traceRun.steps = seats →
        (∑ voter ∈ allVoters,
            fractionalSTVWeightAfterSteps allVoters ballots quota traceRun.steps
              initialWeight voter) < quota := by
    intro helectCount
    simpa [quota] using
      sum_fractionalSTVWeightAfterSteps_lt_STVQuota_of_electStepCount_eq
        (votersFin := allVoters) (ballots := ballots)
        (steps := traceRun.steps) (initialWeight := initialWeight)
        (seats := seats) (voters := voters) hinitialTotalMass helectCount
        indexedRun.step_focus_active indexedRun.quota_if_elect
  have hpartyLower :
      ⌊(partyShare * (voters : ℝ)) / quota⌋₊ ≤
        partyFilledSeatCount partyCandidates seats traceRun.steps
          terminalActive := by
    by_cases hlt : electStepCount traceRun.steps < seats
    · have hfinal :
          partyElectStepCount partyCandidates traceRun.steps +
              (activePartyCandidates terminalActive partyCandidates).card ≤
            partyFilledSeatCount partyCandidates seats traceRun.steps
              terminalActive := by
        simp [partyFilledSeatCount, terminalFillActive, hlt]
      exact
        floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityFill
          (rule := rule) (trace := traceRun) (allVoters := allVoters)
          (partyVoters := partyVoters) (ballots := ballots)
          (partyCandidates := partyCandidates) (quota := quota)
          (initialVotes := partyShare * (voters : ℝ))
          (finalSeats :=
            partyFilledSeatCount partyCandidates seats traceRun.steps
              terminalActive)
          (initialActive := initialActive) (terminalActive := terminalActive)
          (initialWeight := initialWeight)
          (partyInitialWeight := partyInitialWeight) hexec hpartySolid
          hpartySubsetAll hpartyInitialWeightEq hpartyInitialMass
          hpartyStartCapacity hpartyStartRemaining hpartyNoquotaOnEliminate
          hfinal
    · have helectCount : electStepCount traceRun.steps = seats := by
        have hterminal_empty :
            terminalFillActive seats traceRun.steps terminalActive = ∅ := by
          simp [terminalFillActive, hlt]
        have hcount :
            electStepCount traceRun.steps + 0 = seats := by
          simpa [hterminal_empty] using hfilledTotal
        omega
      have hglobalBelow := hglobalBelow_of_full helectCount
      have hpartyGlobalBelow :
          (∑ voter ∈ partyVoters,
              fractionalSTVWeightAfterSteps allVoters ballots quota
                traceRun.steps initialWeight voter) < quota := by
        have hpartyLe :
            (∑ voter ∈ partyVoters,
                fractionalSTVWeightAfterSteps allVoters ballots quota
                  traceRun.steps initialWeight voter) ≤
              ∑ voter ∈ allVoters,
                fractionalSTVWeightAfterSteps allVoters ballots quota
                  traceRun.steps initialWeight voter :=
          Finset.sum_le_sum_of_subset_of_nonneg hpartySubsetAll
            (by
              intro voter hvoter _hnot
              exact hglobalFinalNonneg voter hvoter)
        exact lt_of_le_of_lt hpartyLe hglobalBelow
      have hpartyTerminal :
          PartyQuotaTerminalBelowQuota quota
            (partyTransferPreservationTerminalState partyCandidates quota
              rule.fractionalTally traceRun.steps
              (PartyQuotaStartState partyCandidates.card
                (partyShare * (voters : ℝ)))) :=
        terminalBelowQuota_of_replaySteps_lowerBound_globalWeight_lt
          (allVoters := allVoters) (partyVoters := partyVoters)
          (ballots := ballots) (partyCandidates := partyCandidates)
          (quota := quota) (fractionalTally := rule.fractionalTally)
          (steps := traceRun.steps) (startActive := initialActive)
          (terminalActive := terminalActive) (initialWeight := initialWeight)
          (startState :=
            PartyQuotaStartState partyCandidates.card
              (partyShare * (voters : ℝ)))
          hpartySolid hpartySubsetAll hinitialWeightNonneg hquota_pos
          (FractionalSTVExecutableTrace.concreteStepLaw hexec) hexec.tally_eq
          hexec.activeReplay hpartyStartCapacity hpartyStartRemaining
          (by
            intro _hremaining_pos
            have hmass :
                partyShare * (voters : ℝ) =
                  ∑ voter ∈ partyVoters, initialWeight voter := by
              calc
                partyShare * (voters : ℝ)
                    = ∑ voter ∈ partyVoters, partyInitialWeight voter :=
                      hpartyInitialMass
                _ = ∑ voter ∈ partyVoters, initialWeight voter := by
                    refine Finset.sum_congr rfl ?_
                    intro voter hvoter
                    exact (hpartyInitialWeightEq voter hvoter).symm
            simpa [PartyQuotaStartState, hmass])
          hpartyNoquotaOnEliminate hpartyGlobalBelow
      have hpartyElectLower :
          ⌊(partyShare * (voters : ℝ)) / quota⌋₊ ≤
            partyElectStepCount partyCandidates traceRun.steps :=
        floor_votes_div_quota_le_partyElectStepCount_of_terminalBelowQuota
          (partyCandidates := partyCandidates) (quota := quota)
          (initialVotes := partyShare * (voters : ℝ))
          (fractionalTally := rule.fractionalTally)
          (steps := traceRun.steps) hquota_pos hpartyVotesNonneg
          hpartyTerminal
      simpa [partyFilledSeatCount, terminalFillActive, hlt] using
        hpartyElectLower
  have hotherLower :
      ⌊((1 - partyShare) * (voters : ℝ)) / quota⌋₊ ≤
        partyFilledSeatCount otherPartyCandidates seats traceRun.steps
          terminalActive := by
    by_cases hlt : electStepCount traceRun.steps < seats
    · have hfinal :
          partyElectStepCount otherPartyCandidates traceRun.steps +
              (activePartyCandidates terminalActive otherPartyCandidates).card ≤
            partyFilledSeatCount otherPartyCandidates seats traceRun.steps
              terminalActive := by
        simp [partyFilledSeatCount, terminalFillActive, hlt]
      exact
        floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityFill
          (rule := rule) (trace := traceRun) (allVoters := allVoters)
          (partyVoters := otherPartyVoters) (ballots := ballots)
          (partyCandidates := otherPartyCandidates) (quota := quota)
          (initialVotes := (1 - partyShare) * (voters : ℝ))
          (finalSeats :=
            partyFilledSeatCount otherPartyCandidates seats traceRun.steps
              terminalActive)
          (initialActive := initialActive) (terminalActive := terminalActive)
          (initialWeight := initialWeight)
          (partyInitialWeight := otherPartyInitialWeight) hexec hotherSolid
          hotherSubsetAll hotherInitialWeightEq hotherInitialMass
          hotherStartCapacity hotherStartRemaining hotherNoquotaOnEliminate
          hfinal
    · have helectCount : electStepCount traceRun.steps = seats := by
        have hterminal_empty :
            terminalFillActive seats traceRun.steps terminalActive = ∅ := by
          simp [terminalFillActive, hlt]
        have hcount :
            electStepCount traceRun.steps + 0 = seats := by
          simpa [hterminal_empty] using hfilledTotal
        omega
      have hglobalBelow := hglobalBelow_of_full helectCount
      have hotherGlobalBelow :
          (∑ voter ∈ otherPartyVoters,
              fractionalSTVWeightAfterSteps allVoters ballots quota
                traceRun.steps initialWeight voter) < quota := by
        have hotherLe :
            (∑ voter ∈ otherPartyVoters,
                fractionalSTVWeightAfterSteps allVoters ballots quota
                  traceRun.steps initialWeight voter) ≤
              ∑ voter ∈ allVoters,
                fractionalSTVWeightAfterSteps allVoters ballots quota
                  traceRun.steps initialWeight voter :=
          Finset.sum_le_sum_of_subset_of_nonneg hotherSubsetAll
            (by
              intro voter hvoter _hnot
              exact hglobalFinalNonneg voter hvoter)
        exact lt_of_le_of_lt hotherLe hglobalBelow
      have hotherTerminal :
          PartyQuotaTerminalBelowQuota quota
            (partyTransferPreservationTerminalState otherPartyCandidates quota
              rule.fractionalTally traceRun.steps
              (PartyQuotaStartState otherPartyCandidates.card
                ((1 - partyShare) * (voters : ℝ)))) :=
        terminalBelowQuota_of_replaySteps_lowerBound_globalWeight_lt
          (allVoters := allVoters) (partyVoters := otherPartyVoters)
          (ballots := ballots) (partyCandidates := otherPartyCandidates)
          (quota := quota) (fractionalTally := rule.fractionalTally)
          (steps := traceRun.steps) (startActive := initialActive)
          (terminalActive := terminalActive) (initialWeight := initialWeight)
          (startState :=
            PartyQuotaStartState otherPartyCandidates.card
              ((1 - partyShare) * (voters : ℝ)))
          hotherSolid hotherSubsetAll hinitialWeightNonneg hquota_pos
          (FractionalSTVExecutableTrace.concreteStepLaw hexec) hexec.tally_eq
          hexec.activeReplay hotherStartCapacity hotherStartRemaining
          (by
            intro _hremaining_pos
            have hmass :
                (1 - partyShare) * (voters : ℝ) =
                  ∑ voter ∈ otherPartyVoters, initialWeight voter := by
              calc
                (1 - partyShare) * (voters : ℝ)
                    = ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter :=
                      hotherInitialMass
                _ = ∑ voter ∈ otherPartyVoters, initialWeight voter := by
                    refine Finset.sum_congr rfl ?_
                    intro voter hvoter
                    exact (hotherInitialWeightEq voter hvoter).symm
            simpa [PartyQuotaStartState, hmass])
          hotherNoquotaOnEliminate hotherGlobalBelow
      have hotherElectLower :
          ⌊((1 - partyShare) * (voters : ℝ)) / quota⌋₊ ≤
            partyElectStepCount otherPartyCandidates traceRun.steps :=
        floor_votes_div_quota_le_partyElectStepCount_of_terminalBelowQuota
          (partyCandidates := otherPartyCandidates) (quota := quota)
          (initialVotes := (1 - partyShare) * (voters : ℝ))
          (fractionalTally := rule.fractionalTally)
          (steps := traceRun.steps) hquota_pos hotherVotesNonneg
          hotherTerminal
      simpa [partyFilledSeatCount, terminalFillActive, hlt] using
        hotherElectLower
  have hquotaLower :
      stvSolidCoalitionQuotaLowerBounds
        (partyFilledSeatCount partyCandidates seats traceRun.steps
          terminalActive) partyShare seats voters := by
    refine ⟨partyFilledSeatCount otherPartyCandidates seats traceRun.steps
      terminalActive, hfilled, hpos.le, hle, hvoters, ?_, ?_⟩
    · simpa [quota, mul_div_assoc] using hpartyLower
    · simpa [quota, mul_div_assoc] using hotherLower
  simpa [traceRun, terminalActive, quota] using
    proposition1_seatSharesRounded_of_stvQuotaLowerBounds_and_pavMinArgmax
      (stvSeatCount :=
        partyFilledSeatCount partyCandidates seats traceRun.steps terminalActive)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hquotaLower hpav

/--
Proposition 1 from weighted fractional STV round facts: this expands the
global concrete step law into weighted active-support tallies and ordinary
elect/eliminate round conditions.
-/
theorem proposition1_seatSharesRounded_of_weightedRoundTraceFacts_and_pavMinArgmax
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {rule : FractionalSTVTransferRule Candidate} {trace : STVTrace Candidate}
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    (roundWeight partyWeight otherPartyWeight :
      STVStep Candidate → Voter → ℝ)
    {stvSeatCount otherPartySeatCount pavSeatCount seats voters : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (htotal : stvSeatCount + otherPartySeatCount = seats)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hremove :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).removesFocusedCandidate)
    (hfocus :
      ∀ i : Fin trace.steps.length,
        ∃ focused, (trace.steps.get i).focus = some focused ∧
          focused ∈ (trace.steps.get i).beforeActive)
    (hroundWeightNonneg :
      ∀ i : Fin trace.steps.length, ∀ voter,
        voter ∈ allVoters → 0 ≤ roundWeight (trace.steps.get i) voter)
    (hroundTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈ (trace.steps.get i).beforeActive →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally allVoters ballots
              (roundWeight (trace.steps.get i))
              (trace.steps.get i).beforeActive candidate)
    (hkind_allowed :
      ∀ i : Fin trace.steps.length,
        (trace.steps.get i).kind = StepKind.elect ∨
          (trace.steps.get i).kind = StepKind.eliminate)
    (hquota_if_elect :
      ∀ i : Fin trace.steps.length, ∀ focused,
        (trace.steps.get i).focus = some focused →
          (trace.steps.get i).kind = StepKind.elect →
            (STVQuota seats voters : ℝ) ≤
              fractionalActiveTally allVoters ballots
                (roundWeight (trace.steps.get i))
                (trace.steps.get i).beforeActive focused)
    (hpartyActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ partyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hpartyTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              partyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally partyVoters ballots
              (partyWeight (trace.steps.get i))
              (trace.steps.get i).beforeActive candidate)
    (hpartyRemaining :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))).remainingCandidates =
          (activePartyCandidates (trace.steps.get i).beforeActive
            partyCandidates).card)
    (hpartyMass :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState partyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState partyCandidates.card
            (partyShare * (voters : ℝ)))).voteMass =
          ∑ voter ∈ partyVoters, partyWeight (trace.steps.get i) voter)
    (hpartyResidual :
      partyShare * (voters : ℝ) -
          (partyElectStepCount partyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hpartyElectCount :
      partyElectStepCount partyCandidates trace.steps ≤ stvSeatCount)
    (hotherActive :
      ∀ i : Fin trace.steps.length,
        ∃ same, same ∈ otherPartyCandidates ∧
          same ∈ (trace.steps.get i).beforeActive)
    (hotherTallyEq :
      ∀ i : Fin trace.steps.length, ∀ candidate,
        candidate ∈
            activePartyCandidates (trace.steps.get i).beforeActive
              otherPartyCandidates →
          rule.fractionalTally (trace.steps.get i) candidate =
            fractionalActiveTally otherPartyVoters ballots
              (otherPartyWeight (trace.steps.get i))
              (trace.steps.get i).beforeActive candidate)
    (hotherRemaining :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))).remainingCandidates =
          (activePartyCandidates (trace.steps.get i).beforeActive
            otherPartyCandidates).card)
    (hotherMass :
      ∀ i : Fin trace.steps.length,
        (partyTransferPreservationTerminalState otherPartyCandidates
          (STVQuota seats voters : ℝ) rule.fractionalTally
          (trace.steps.take i.1)
          (PartyQuotaStartState otherPartyCandidates.card
            ((1 - partyShare) * (voters : ℝ)))).voteMass =
          ∑ voter ∈ otherPartyVoters, otherPartyWeight (trace.steps.get i) voter)
    (hotherResidual :
      (1 - partyShare) * (voters : ℝ) -
          (partyElectStepCount otherPartyCandidates trace.steps : ℝ) *
            (STVQuota seats voters : ℝ) <
        (STVQuota seats voters : ℝ))
    (hotherElectCount :
      partyElectStepCount otherPartyCandidates trace.steps ≤ otherPartySeatCount)
    (hpav : pavSeatMinArgmax pavSeatCount partyShare seats) :
    seatShareRounded stvSeatCount partyShare seats ∧
      seatShareRounded pavSeatCount partyShare seats := by
  have htraceSteps :
      ∀ i : Fin trace.steps.length,
        FractionalSTVConcreteStepLaw
          (rule.fractionalTally (trace.steps.get i))
          (STVQuota seats voters : ℝ) (trace.steps.get i) := by
    intro i
    rcases hfocus i with ⟨focused, hfocused, hfocused_active⟩
    exact fractionalSTVConcreteStepLaw_of_weightedActiveTally_of_tally_eq
      (voters := allVoters) (ballots := ballots)
      (weight := roundWeight (trace.steps.get i))
      (fractionalTally := rule.fractionalTally (trace.steps.get i))
      (quota := (STVQuota seats voters : ℝ)) (step := trace.steps.get i)
      (hremove i) hfocused hfocused_active (hroundWeightNonneg i)
      (hroundTallyEq i) (hkind_allowed i)
      (hquota_if_elect i focused hfocused)
  exact
    proposition1_seatSharesRounded_of_weightedConcreteTraceFacts_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate) (rule := rule)
      (trace := trace) (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      partyWeight otherPartyWeight
      (stvSeatCount := stvSeatCount)
      (otherPartySeatCount := otherPartySeatCount)
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle htotal hvoters hpartyCandidates
      hotherPartyCandidates hpartySolid hotherSolid htraceSteps hpartyActive
      hpartyTallyEq hpartyRemaining hpartyMass hpartyResidual
      hpartyElectCount hotherActive hotherTallyEq hotherRemaining hotherMass
      hotherResidual hotherElectCount hpav

end GGRS26CombattingGerrymanderingRCV
