import GGRS26CombattingGerrymanderingRCV.MainTheorems

/-!
# Human-Facing Paper Interface: Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the United States

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- State named results directly, with source hypotheses visible in each theorem
  signature and proof-internal bridges discharged in `MainTheorems.lean`.
- Use short proofs that call into `MainTheorems.lean` or lower proof files.
- If implementation endpoints become broad or helper-heavy, move them to
  `ProofInterface.lean`; keep this filename as the single review surface.
- Keep exhaustive endpoint aliases and proof-seam checks in `PostPaperAudit.lean`,
  not here.

## Paper Definitions

- `paper_pav_score`: PAV/Thiele score used for the `lambda_PAV` comparison.
- `paper_pav_seat_score`: the two-party PAV objective over Republican seat
  counts.
- `paper_pav_min_argmax`: the paper's tie-broken PAV seat-count selector.
- `paper_pav_marginal_conditions`: adjacent marginal inequalities from the
  proof of Lemma C.1.
- `paper_pav_seat_interval`: Lemma C.1 interval characterization for the PAV
  party seat count.
- `paper_seat_share_rounded`: floor/ceiling target used in Proposition 1.
- `paper_stv_solid_coalition_party_trace_isolation`: the STV-dynamics bridge
  justifying separate party-level analysis before party exhaustion.
- `paper_stv_quota_floors_fit`: the appendix quota-capacity step that the two
  parties' full Droop-quota floors fit into the district's seats.
- `paper_stv_solid_coalition_quota_witness_bounds`: the quota-witness
  consequence used by the STV lower-bound bridge.
- `paper_stv_solid_coalition_lower_bounds`: the proportional lower-bound
  consequence derived from the quota witness.
- `paper_stv_seat_share_bounds`: the STV floor/ceiling consequence derived from
  the cited lower-bound boundary.

## Named Results

- `paper_pav_interval_seat_share_rounded`: arithmetic bridge from the Lemma C.1
  interval to the Proposition 1 floor/ceiling target.
- `paper_pav_marginal_conditions_seat_share_rounded`: bridge from the source
  proof's adjacent PAV marginal conditions to the same floor/ceiling target.
- `paper_pav_min_argmax_seat_interval`: formalized Lemma C.1 interval statement
  from the paper's min-argmax selector.
- `paper_pav_min_argmax_seat_share_rounded`: formalized PAV component of
  Lemma C.1 / Proposition 1 from the paper's min-argmax selector.
- `paper_stv_solid_coalition_ballots_party_trace_isolation`: bridge from the
  solid-coalition ballot assumption to no cross-party active support before
  party exhaustion.
- `paper_stv_quota_floors_fit`: Appendix quota-capacity arithmetic.
- `paper_stv_solid_coalition_quota_witness_bounds_lower_bounds`: bridge from
  the quota-process witness to proportional STV lower bounds.
- `paper_stv_solid_coalition_lower_bounds_seat_share_bounds`: arithmetic bridge
  from proportional STV lower bounds to floor/ceiling bounds.
- `paper_proposition1_from_generated_filled_seat_run_fractional_stv_trace_global_weight_terminal_and_pav_min_argmax`:
  Proposition 1 from the generated, total, quota-respecting fractional STV
  filled-seat run and the PAV min-argmax input.
-/

namespace GGRS26CombattingGerrymanderingRCV

open EconCSLib.SocialChoice.Voting

/--
Paper object for the `lambda_PAV` committee-score comparison in Proposition 1.

Source status: direct PAV/Thiele score wrapper used by the Proposition 1
comparison.
-/
noncomputable def paper_pav_score {Candidate : Type*} [DecidableEq Candidate]
    (committee : Finset Candidate) (profile : List (PartyApprovalBallot Candidate)) : ℝ :=
  partyPAVScore committee profile

/--
Paper PAV objective over possible Republican seat counts:
`y_R * sum_{i=1}^{n_R} lambda_PAV(i) +
  (1 - y_R) * sum_{i=1}^{M - n_R} lambda_PAV(i)`.

Source status: direct paper formula from Lemma C.1.
-/
noncomputable def paper_pav_seat_score (partyShare : ℝ) (seats seatCount : ℕ) : ℝ :=
  partyShare * pavHarmonicSum seatCount +
    (1 - partyShare) * pavHarmonicSum (seats - seatCount)

/--
Paper selector for `n_R(y_R, lambda_PAV)`: the smallest seat count maximizing
the PAV objective among seat counts from `0` to `M`.

Source status: direct paper definition from Lemma C.1's `min arg max`.
-/
def paper_pav_min_argmax (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  seatCount ≤ seats ∧
    (∀ candidate, candidate ≤ seats →
      paper_pav_seat_score partyShare seats candidate ≤
        paper_pav_seat_score partyShare seats seatCount) ∧
    (∀ candidate, candidate ≤ seats →
      paper_pav_seat_score partyShare seats candidate =
        paper_pav_seat_score partyShare seats seatCount →
      seatCount ≤ candidate)

/--
Paper proof inequalities from Lemma C.1 after clearing positive denominators.

For a chosen Republican seat count `n_R`, the previous chosen Republican seat
has strictly larger PAV marginal value than the next Democratic seat, and the
next Republican seat has no larger PAV marginal value than the previous
Democratic seat.

Source status: proof-local inequalities from Lemma C.1.
-/
def paper_pav_marginal_conditions (seatCount : ℕ) (partyShare : ℝ)
    (seats : ℕ) : Prop :=
  pavSeatMarginalConditions seatCount partyShare seats

/--
Paper interval characterization from Lemma C.1:
`y_R (M + 1) - 1 <= n_R < y_R (M + 1)`.

Source status: direct paper interval statement.
-/
def paper_pav_seat_interval (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  pavSeatInterval seatCount partyShare seats

/--
Paper formula target for Proposition 1: a party's seat count is one of the
floor or ceiling of party vote share times the number of seats.

Source status: direct paper formula.
-/
def paper_seat_share_rounded (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  seatShareRounded seatCount partyShare seats

/--
Paper STV dynamics bridge: under the solid-coalition ballot condition, a
party's voters give no active support to outside-party candidates at any trace
step until all same-party candidates have been exhausted.

Source status: Proposition 1 proof line justifying separate party-level STV
analysis under solid coalitions.
-/
def paper_stv_solid_coalition_party_trace_isolation
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (partyCandidates : Finset Candidate) (trace : STVTrace Candidate) : Prop :=
  ∀ step, step ∈ trace.steps →
    (∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive) →
      ∀ outside, outside ∉ partyCandidates →
        (Ballot.activeSupport voters ballots step.beforeActive outside).card = 0

/--
Paper STV quota-witness consequence used by the quota arithmetic bridge.

Source status: named proof bridge extracted from the Appendix Proposition 1
argument.
-/
def paper_stv_solid_coalition_quota_witness_bounds (seatCount : ℕ)
    (partyShare : ℝ) (seats voters : ℕ) : Prop :=
  stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters

/--
Paper STV proportional lower-bound consequence used by the final
floor/ceiling bridge.

Source status: named proof bridge extracted from the Appendix Proposition 1
argument.
-/
def paper_stv_solid_coalition_lower_bounds (seatCount : ℕ) (partyShare : ℝ)
    (seats : ℕ) :
    Prop :=
  stvSolidCoalitionLowerBounds seatCount partyShare seats

/--
Paper STV floor/ceiling consequence used by Proposition 1.

Source status: direct Proposition 1 target for the STV party seat count.
-/
def paper_stv_seat_share_bounds (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) :
    Prop :=
  stvSeatShareBounds seatCount partyShare seats

/--
Arithmetic bridge used after Lemma C.1: once the source interval
`y_R (M + 1) - 1 <= n_R < y_R (M + 1)` is available, the party seat count is
one of floor or ceiling of `y_R M`.

Source status: proof step in Lemma C.1 / Proposition 1.
-/
theorem paper_pav_interval_seat_share_rounded {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hinterval : paper_pav_seat_interval seatCount partyShare seats) :
    paper_seat_share_rounded seatCount partyShare seats := by
  simpa [paper_pav_seat_interval, paper_seat_share_rounded] using
    (pavSeatInterval_seatShareRounded
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hinterval)

/--
Arithmetic bridge from the source proof's adjacent PAV marginal inequalities to
the Proposition 1 floor/ceiling target.

Source status: proof step in Lemma C.1.
-/
theorem paper_pav_marginal_conditions_seat_share_rounded {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1) (hseat : seatCount ≤ seats)
    (hmarg : paper_pav_marginal_conditions seatCount partyShare seats) :
    paper_seat_share_rounded seatCount partyShare seats := by
  simpa [paper_pav_marginal_conditions, paper_seat_share_rounded] using
    (pavSeatMarginalConditions_seatShareRounded
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hseat hmarg)

/--
Lemma C.1 PAV interval statement: the paper's leftmost maximizing PAV seat
count satisfies `y_R (M + 1) - 1 <= n_R < y_R (M + 1)`.

Source status: named Lemma C.1 statement.
-/
theorem paper_pav_min_argmax_seat_interval {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hmin : paper_pav_min_argmax seatCount partyShare seats) :
    paper_pav_seat_interval seatCount partyShare seats := by
  simpa [paper_pav_min_argmax, paper_pav_seat_score, paper_pav_seat_interval,
    pavSeatMinArgmax, pavSeatScore, pavSeatInterval] using
    (pavSeatMinArgmax_seatInterval
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hmin)

/--
PAV component of Lemma C.1 / Proposition 1: the paper's leftmost maximizing PAV
seat count is one of floor or ceiling of `y_R M`.

Source status: named Lemma C.1 / Proposition 1 consequence.
-/
theorem paper_pav_min_argmax_seat_share_rounded {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hmin : paper_pav_min_argmax seatCount partyShare seats) :
    paper_seat_share_rounded seatCount partyShare seats := by
  simpa [paper_pav_min_argmax, paper_pav_seat_score, paper_seat_share_rounded,
    pavSeatMinArgmax, pavSeatScore, seatShareRounded] using
    (pavSeatMinArgmax_seatShareRounded
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hmin)

/--
Solid-coalition STV dynamics bridge: before a party has exhausted all active
same-party candidates, its voters cannot provide active support to an
outside-party candidate.

Source status: Proposition 1 proof step justifying separate party-level STV
analysis from the solid-coalition ballot assumption.
-/
theorem paper_stv_solid_coalition_ballots_party_trace_isolation
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {trace : STVTrace Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates) :
    paper_stv_solid_coalition_party_trace_isolation
      voters ballots partyCandidates trace := by
  simpa [paper_stv_solid_coalition_party_trace_isolation,
    NoCrossPartyTransferBeforeExhaustion] using
    (stvSolidCoalitionBallots_partyTraceIsolation
      (voters := voters) (ballots := ballots)
      (partyCandidates := partyCandidates) (trace := trace) hsolid)

/--
STV quota-capacity arithmetic from the appendix proof: the two parties'
canonical full Droop-quota counts fit within the district's seat count.

Source status: Appendix Proposition 1 quota-capacity proof step.
-/
theorem paper_stv_quota_floors_fit {seats voters : ℕ} {partyShare : ℝ}
    (hshare_nonneg : 0 ≤ partyShare) (hshare_le : partyShare ≤ 1) :
    ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ +
        ⌊(1 - partyShare) *
          ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤ seats :=
  stvTwoPartyQuotaFloors_sum_le_seats hshare_nonneg hshare_le

/--
STV arithmetic bridge: the appendix quota-process witness implies the
proportional lower-bound and seat-conservation boundary.

Source status: Appendix Proposition 1 proof step.
-/
theorem paper_stv_solid_coalition_quota_witness_bounds_lower_bounds
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hstv :
      paper_stv_solid_coalition_quota_witness_bounds seatCount partyShare seats voters) :
    paper_stv_solid_coalition_lower_bounds seatCount partyShare seats := by
  simpa [paper_stv_solid_coalition_quota_witness_bounds,
    paper_stv_solid_coalition_lower_bounds,
    stvSolidCoalitionQuotaWitnessBounds] using
    (stvSolidCoalitionLowerBounds_of_quotaLowerBounds
      (seatCount := seatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare)
      (stvSolidCoalitionQuotaLowerBounds_of_quotaWitnessBounds hstv))

/--
STV arithmetic bridge: the proportional lower-bound and seat-conservation
boundary implies the STV floor/ceiling seat-share consequence.

Source status: Appendix Proposition 1 proof step.
-/
theorem paper_stv_solid_coalition_lower_bounds_seat_share_bounds
    {seatCount seats : ℕ} {partyShare : ℝ}
    (hstv : paper_stv_solid_coalition_lower_bounds seatCount partyShare seats) :
    paper_stv_seat_share_bounds seatCount partyShare seats := by
  simpa [paper_stv_solid_coalition_lower_bounds, paper_stv_seat_share_bounds,
    stvSolidCoalitionLowerBounds] using
    (stvSeatShareBounds_of_solidCoalitionLowerBounds
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hstv)

/--
Proposition 1 reduction from the generated executable fractional STV simulator.
This is the strict source-primitive paper route: the statement itself is over
the generated candidate-level run, rather than an abstract trace plus an
external trace-equality hypothesis.

Source status: named Proposition 1 theorem-ledger endpoint for the theoretical STV/PAV rounded-seat claim.
-/
theorem paper_proposition1_from_generated_filled_seat_run_fractional_stv_trace_global_weight_terminal_and_pav_min_argmax
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
    (hpav : paper_pav_min_argmax pavSeatCount partyShare seats) :
    paper_seat_share_rounded
        (partyFilledSeatCount partyCandidates seats
          (fractionalSTVFilledSeatRunTrace choice allVoters ballots
            (STVQuota seats voters : ℝ) seats initialActive.card 0
            initialActive initialWeight).steps
          (fractionalSTVFilledSeatRunTerminalActive choice allVoters ballots
            (STVQuota seats voters : ℝ) seats initialActive.card 0
            initialActive initialWeight))
        partyShare seats ∧
      paper_seat_share_rounded pavSeatCount partyShare seats := by
  simpa [paper_pav_min_argmax, paper_pav_seat_score,
    paper_seat_share_rounded, pavSeatMinArgmax, pavSeatScore,
    seatShareRounded] using
    (proposition1_seatSharesRounded_of_generatedFilledSeatRunFractionalSTVTrace_globalWeightTerminal_and_pavMinArgmax_of_total
      (Voter := Voter) (Candidate := Candidate) choice
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) initialWeight
      partyInitialWeight otherPartyInitialWeight
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hvoters htotalChoice hchoiceRespect
      hpartyCandidates hotherPartyCandidates hpartySolid hotherSolid
      hinitialWeightNonneg hinitialTotalMass hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherInitialActive
      hinitialActiveSubset hpartyInitialWeightEq hotherInitialWeightEq
      hpartyInitialMass hotherInitialMass hpav)

end GGRS26CombattingGerrymanderingRCV
