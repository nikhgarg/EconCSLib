import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Ranked Ballots

Reusable finite ballot primitives for ranked-choice voting and STV-style
election rules.

The library starts with partial rankings represented as lists. Paper folders can
add source-specific conventions, such as complete rankings, exhausted ballots,
or equal-rank exclusions, as thin wrappers around this API.

## Main declarations

- `Ballot`
- `Ballot.Valid`
- `Ballot.nextActive`
- `Ballot.removeCandidates`
- `Ballot.firstChoiceIn`
- `Ballot.strictSupportVoters`
- `Ballot.strictSupportCount`
- `Ballot.IsSuffixExtension`
- `Ballot.IsPrefixExtension`
- `Ballot.PreservesPrefixThrough`
- `Ballot.RespectsLength`
-/

namespace EconCSLib
namespace SocialChoice
namespace Voting

/-- A ranked ballot is a finite ordered list of candidates. -/
abbrev Ballot (Candidate : Type*) := List Candidate

namespace Ballot

/-- A ballot is valid when it lists each candidate at most once. -/
def Valid {Candidate : Type*} (ballot : Ballot Candidate) : Prop :=
  ballot.Nodup

/-- `extended` is obtained from `base` by suffixing additional preferences. -/
def IsSuffixExtension {Candidate : Type*}
    (base extended : Ballot Candidate) : Prop :=
  ∃ suffix, extended = base ++ suffix

/-- `extended` is obtained from `base` by prefixing additional preferences. -/
def IsPrefixExtension {Candidate : Type*}
    (pref base extended : Ballot Candidate) : Prop :=
  extended = pref ++ base

/--
`before` and `after` have the same prefix through `candidate`.

This captures paper-neutral strategic-voting moves where a candidate can change
later preferences after their own position, but cannot move themselves earlier
or edit earlier-ranked candidates.
-/
def PreservesPrefixThrough {Candidate : Type*}
    (candidate : Candidate) (before after : Ballot Candidate) : Prop :=
  ∃ pref beforeSuffix afterSuffix,
    before = pref ++ candidate :: beforeSuffix ∧
      after = pref ++ candidate :: afterSuffix

/-- A ballot respects a maximum allowed ranking length. -/
def RespectsLength {Candidate : Type*} (maxLength : ℕ) (ballot : Ballot Candidate) :
    Prop :=
  ballot.length ≤ maxLength

/-- A single-choice ballot ranks at most one candidate. -/
def IsSingleChoice {Candidate : Type*} (ballot : Ballot Candidate) : Prop :=
  RespectsLength 1 ballot

/--
The first candidate on a ballot that is still active, if one exists.

This is the core exhaustion operation used by deterministic RCV/STV traces.
-/
def nextActive {Candidate : Type*} [DecidableEq Candidate]
    (ballot : Ballot Candidate) (active : Finset Candidate) : Option Candidate :=
  match ballot with
  | [] => none
  | c :: rest => if c ∈ active then some c else nextActive rest active

/--
Remove every candidate in `removed` from a ballot, preserving the relative
order of all remaining candidates.
-/
def removeCandidates {Candidate : Type*} [DecidableEq Candidate]
    (removed : Finset Candidate) (ballot : Ballot Candidate) : Ballot Candidate :=
  ballot.filter fun candidate => candidate ∉ removed

/-- The ballot's first-ranked candidate belongs to a given candidate set. -/
def firstChoiceIn {Candidate : Type*} [DecidableEq Candidate]
    (ballot : Ballot Candidate) (candidates : Finset Candidate) : Prop :=
  match ballot with
  | [] => False
  | candidate :: _rest => candidate ∈ candidates

@[simp] theorem firstChoiceIn_nil {Candidate : Type*} [DecidableEq Candidate]
    (candidates : Finset Candidate) :
    firstChoiceIn ([] : Ballot Candidate) candidates = False := rfl

@[simp] theorem firstChoiceIn_cons {Candidate : Type*} [DecidableEq Candidate]
    (candidate : Candidate) (rest : Ballot Candidate)
    (candidates : Finset Candidate) :
    firstChoiceIn (candidate :: rest) candidates =
      (candidate ∈ candidates) := rfl

instance decidableFirstChoiceIn {Candidate : Type*} [DecidableEq Candidate]
    (ballot : Ballot Candidate) (candidates : Finset Candidate) :
    Decidable (firstChoiceIn ballot candidates) := by
  cases ballot with
  | nil =>
      exact isFalse (by simp [firstChoiceIn])
  | cons candidate rest =>
      change Decidable (candidate ∈ candidates)
      infer_instance

@[simp] theorem nextActive_nil {Candidate : Type*} [DecidableEq Candidate]
    (active : Finset Candidate) :
    nextActive ([] : Ballot Candidate) active = none := rfl

@[simp] theorem nextActive_cons_of_mem {Candidate : Type*} [DecidableEq Candidate]
    (c : Candidate) (rest : Ballot Candidate) (active : Finset Candidate)
    (h : c ∈ active) :
    nextActive (c :: rest) active = some c := by
  simp [nextActive, h]

@[simp] theorem nextActive_cons_of_not_mem {Candidate : Type*} [DecidableEq Candidate]
    (c : Candidate) (rest : Ballot Candidate) (active : Finset Candidate)
    (h : c ∉ active) :
    nextActive (c :: rest) active = nextActive rest active := by
  simp [nextActive, h]

theorem nextActive_mem {Candidate : Type*} [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active : Finset Candidate} {c : Candidate}
    (h : nextActive ballot active = some c) :
    c ∈ active := by
  induction ballot with
  | nil =>
      simp [nextActive] at h
  | cons head rest ih =>
      by_cases hhead : head ∈ active
      · simp [nextActive, hhead] at h
        simpa [← h] using hhead
      · simp [nextActive, hhead] at h
        exact ih h

/--
Removing candidates from a ballot is equivalent, for first-active lookup, to
running the original ballot with those candidates absent from the active set.
-/
@[simp] theorem nextActive_removeCandidates_sdiff {Candidate : Type*}
    [DecidableEq Candidate]
    (ballot : Ballot Candidate) (active removed : Finset Candidate) :
    nextActive (removeCandidates removed ballot) (active \ removed) =
      nextActive ballot (active \ removed) := by
  induction ballot with
  | nil =>
      simp [removeCandidates]
  | cons head rest ih =>
      by_cases hremoved : head ∈ removed
      · have hinactive : head ∉ active \ removed := by
          intro hhead
          exact (Finset.mem_sdiff.mp hhead).2 hremoved
        simp [removeCandidates, nextActive, hremoved, hinactive]
        simpa [removeCandidates] using ih
      · by_cases hactive : head ∈ active \ removed
        · simp [removeCandidates, nextActive, hremoved, hactive]
        · simp [removeCandidates, nextActive, hremoved, hactive]
          simpa [removeCandidates] using ih

/--
Removing candidates that are not active does not change the first active
candidate.
-/
theorem nextActive_removeCandidates_eq_of_forall_not_mem {Candidate : Type*}
    [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active removed : Finset Candidate}
    (hremoved : ∀ candidate, candidate ∈ active → candidate ∉ removed) :
    nextActive (removeCandidates removed ballot) active =
      nextActive ballot active := by
  have hsdiff : active \ removed = active := by
    ext candidate
    constructor
    · intro hcandidate
      exact (Finset.mem_sdiff.mp hcandidate).1
    · intro hcandidate
      exact Finset.mem_sdiff.mpr
        ⟨hcandidate, hremoved candidate hcandidate⟩
  simpa [hsdiff] using nextActive_removeCandidates_sdiff ballot active removed

/--
Suffixing later preferences does not change the first active candidate when
the original ballot already has one.
-/
theorem nextActive_append_of_some {Candidate : Type*} [DecidableEq Candidate]
    {ballot suffix : Ballot Candidate} {active : Finset Candidate} {c : Candidate}
    (h : nextActive ballot active = some c) :
    nextActive (ballot ++ suffix) active = some c := by
  induction ballot with
  | nil =>
      simp [nextActive] at h
  | cons head rest ih =>
      by_cases hhead : head ∈ active
      · simpa [nextActive, hhead] using h
      · simp [nextActive, hhead] at h ⊢
        exact ih h

/--
If the original ballot is exhausted at an active set, appending later
preferences makes the next active candidate come from the suffix.
-/
theorem nextActive_append_of_none {Candidate : Type*} [DecidableEq Candidate]
    {ballot suffix : Ballot Candidate} {active : Finset Candidate}
    (h : nextActive ballot active = none) :
    nextActive (ballot ++ suffix) active = nextActive suffix active := by
  induction ballot with
  | nil =>
      simp
  | cons head rest ih =>
      by_cases hhead : head ∈ active
      · simp [nextActive, hhead] at h
      · simp [nextActive, hhead] at h ⊢
        exact ih h

/--
Prefixing inactive candidates does not change the first active candidate.
-/
theorem nextActive_append_left_of_forall_not_mem {Candidate : Type*} [DecidableEq Candidate]
    {pref ballot : Ballot Candidate} {active : Finset Candidate}
    (hpref : ∀ c, c ∈ pref → c ∉ active) :
    nextActive (pref ++ ballot) active = nextActive ballot active := by
  induction pref with
  | nil =>
      simp
  | cons head rest ih =>
      have hhead : head ∉ active := hpref head (by simp)
      have hrest : ∀ c, c ∈ rest → c ∉ active := by
        intro c hc
        exact hpref c (by simp [hc])
      simp [List.cons_append, hhead, ih hrest]

/--
If two ballots preserve the prefix through a candidate that is still active,
then they have the same first active candidate.
-/
theorem nextActive_eq_of_preservesPrefixThrough_active {Candidate : Type*}
    [DecidableEq Candidate] {before after : Ballot Candidate}
    {active : Finset Candidate} {gate : Candidate}
    (hpreserve : PreservesPrefixThrough gate before after)
    (hgate : gate ∈ active) :
    nextActive before active = nextActive after active := by
  rcases hpreserve with ⟨pref, beforeSuffix, afterSuffix, hbefore, hafter⟩
  subst before
  subst after
  cases hpref : nextActive pref active with
  | none =>
      rw [nextActive_append_of_none hpref, nextActive_append_of_none hpref]
      simp [nextActive, hgate]
  | some first =>
      have hbeforePrefix :
          nextActive (pref ++ gate :: beforeSuffix) active = some first :=
        nextActive_append_of_some hpref
      have hafterPrefix :
          nextActive (pref ++ gate :: afterSuffix) active = some first :=
        nextActive_append_of_some hpref
      rw [hbeforePrefix, hafterPrefix]

/--
If a pair of ballots preserves the prefix through some active gate candidate,
then the first active candidate is unchanged.
-/
theorem nextActive_eq_of_exists_preservesPrefixThrough_active {Candidate : Type*}
    [DecidableEq Candidate] {before after : Ballot Candidate}
    {active : Finset Candidate}
    (hpreserve : ∃ gate, gate ∈ active ∧ PreservesPrefixThrough gate before after) :
    nextActive before active = nextActive after active := by
  rcases hpreserve with ⟨gate, hgate, hgatePreserve⟩
  exact nextActive_eq_of_preservesPrefixThrough_active hgatePreserve hgate

/--
If a preserved-prefix gate belongs to a set of candidates that are all active,
then it can be used as an active gate.
-/
theorem exists_active_preservesPrefixThrough_of_subset {Candidate : Type*}
    {before after : Ballot Candidate} {gates active : Finset Candidate}
    (hsubset : gates ⊆ active)
    (hpreserve : ∃ gate, gate ∈ gates ∧ PreservesPrefixThrough gate before after) :
    ∃ gate, gate ∈ active ∧ PreservesPrefixThrough gate before after := by
  rcases hpreserve with ⟨gate, hgate, hgatePreserve⟩
  exact ⟨gate, hsubset hgate, hgatePreserve⟩

/--
Pointwise version of
`exists_active_preservesPrefixThrough_of_subset` for a finite voter set.
-/
theorem forall_exists_active_preservesPrefixThrough_of_subset
    {Voter Candidate : Type*} {voters : Finset Voter}
    {before after : Voter → Ballot Candidate}
    {gates active : Finset Candidate}
    (hsubset : gates ⊆ active)
    (hpreserve : ∀ voter ∈ voters,
      ∃ gate, gate ∈ gates ∧
        PreservesPrefixThrough gate (before voter) (after voter)) :
    ∀ voter ∈ voters,
      ∃ gate, gate ∈ active ∧
        PreservesPrefixThrough gate (before voter) (after voter) := by
  intro voter hvoter
  exact exists_active_preservesPrefixThrough_of_subset hsubset
    (hpreserve voter hvoter)

/--
If two ballots preserve the prefix through an active candidate, then the
candidate being first active after the edit implies the candidate was already
first active before the edit.
-/
theorem nextActive_eq_some_of_preservesPrefixThrough {Candidate : Type*}
    [DecidableEq Candidate] {before after : Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hpreserve : PreservesPrefixThrough candidate before after)
    (hcandidate : candidate ∈ active)
    (hafter : nextActive after active = some candidate) :
    nextActive before active = some candidate := by
  rw [nextActive_eq_of_preservesPrefixThrough_active hpreserve hcandidate]
  exact hafter

/-- Voters whose ballots first activate a candidate at a fixed active set. -/
def activeSupport {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (active : Finset Candidate) (candidate : Candidate) : Finset Voter :=
  voters.filter fun voter => nextActive (ballots voter) active = some candidate

/--
Voters contributing to a strict-support count.

A voter contributes for `candidate`, source group `sources`, and blocker set
`blockers` when the ballot starts in `sources` and, after ignoring candidates
other than `candidate` and the blockers, the first active candidate is
`candidate`.
-/
def strictSupportVoters {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) :
    Finset Voter :=
  voters.filter fun voter =>
    firstChoiceIn (ballots voter) sources ∧
      nextActive (ballots voter) (insert candidate blockers) =
        some candidate

/--
Number of voters with strict support for `candidate` from `sources` before
any candidate in `blockers`.
-/
def strictSupportCount {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) : ℕ :=
  (strictSupportVoters voters ballots sources blockers candidate).card

/--
Strict support is active support for `{candidate} ∪ blockers`, restricted to
ballots whose first-ranked candidate belongs to `sources`.
-/
theorem strictSupportVoters_eq_activeSupport_filter_firstChoiceIn
    {Voter Candidate : Type*} [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {sources blockers : Finset Candidate}
    {candidate : Candidate} :
    strictSupportVoters voters ballots sources blockers candidate =
      (activeSupport voters ballots (insert candidate blockers) candidate).filter
        (fun voter => firstChoiceIn (ballots voter) sources) := by
  ext voter
  by_cases hvoter : voter ∈ voters
  · simp [strictSupportVoters, activeSupport, hvoter, and_comm]
  · simp [strictSupportVoters, activeSupport, hvoter]

/--
Strict-support voters are active-support voters for the active set consisting
of the target candidate and the blocker candidates.
-/
theorem strictSupportVoters_subset_activeSupport {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {sources blockers : Finset Candidate}
    {candidate : Candidate} :
    strictSupportVoters voters ballots sources blockers candidate ⊆
      activeSupport voters ballots (insert candidate blockers) candidate := by
  intro voter hvoter
  simp [strictSupportVoters, activeSupport] at hvoter ⊢
  exact ⟨hvoter.1, hvoter.2.2⟩

/--
Strict-support counts are bounded by the corresponding active-support counts.
-/
theorem strictSupportVoters_card_le_activeSupport_card {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {sources blockers : Finset Candidate}
    {candidate : Candidate} :
    (strictSupportVoters voters ballots sources blockers candidate).card ≤
      (activeSupport voters ballots (insert candidate blockers) candidate).card :=
  Finset.card_le_card strictSupportVoters_subset_activeSupport

/--
Reducing every ballot by a candidate set preserves active-support sets when the
active set is reduced by the same candidate set.
-/
theorem activeSupport_removeCandidates_sdiff_eq {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active removed : Finset Candidate}
    {candidate : Candidate} :
    activeSupport voters
        (fun voter => removeCandidates removed (ballots voter))
        (active \ removed) candidate =
      activeSupport voters ballots (active \ removed) candidate := by
  ext voter
  by_cases hvoter : voter ∈ voters
  · simp [activeSupport, hvoter,
      nextActive_removeCandidates_sdiff]
  · simp [activeSupport, hvoter]

/--
Reducing every ballot by a candidate set preserves active-support counts when
the active set is reduced by the same candidate set.
-/
theorem activeSupport_card_removeCandidates_sdiff_eq {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active removed : Finset Candidate}
    {candidate : Candidate} :
    (activeSupport voters
        (fun voter => removeCandidates removed (ballots voter))
        (active \ removed) candidate).card =
      (activeSupport voters ballots (active \ removed) candidate).card := by
  rw [activeSupport_removeCandidates_sdiff_eq]

/--
If each voter's first active candidate is unchanged, the active support set for
any candidate is unchanged.
-/
theorem activeSupport_eq_of_forall_nextActive_eq {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hstable : ∀ voter ∈ voters,
      nextActive (after voter) active = nextActive (before voter) active) :
    activeSupport voters after active candidate =
      activeSupport voters before active candidate := by
  ext voter
  by_cases hvoter : voter ∈ voters
  · have hstableVoter := hstable voter hvoter
    simp [activeSupport, hvoter, hstableVoter]
  · simp [activeSupport, hvoter]

/--
If each voter's first active candidate is unchanged, the active support count
for any candidate is unchanged.
-/
theorem activeSupport_card_eq_of_forall_nextActive_eq {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hstable : ∀ voter ∈ voters,
      nextActive (after voter) active = nextActive (before voter) active) :
    (activeSupport voters after active candidate).card =
      (activeSupport voters before active candidate).card := by
  rw [activeSupport_eq_of_forall_nextActive_eq hstable]

/--
If the old voter set is contained in the new voter set and every old voter's
first active candidate is unchanged, then old active support is contained in
new active support.
-/
theorem activeSupport_subset_of_subset_forall_nextActive_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {beforeVoters afterVoters : Finset Voter}
    {before after : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : beforeVoters ⊆ afterVoters)
    (hstable : ∀ voter ∈ beforeVoters,
      nextActive (after voter) active = nextActive (before voter) active) :
    activeSupport beforeVoters before active candidate ⊆
      activeSupport afterVoters after active candidate := by
  intro voter hvoter
  simp [activeSupport] at hvoter ⊢
  exact ⟨hsubset hvoter.1, by rw [hstable voter hvoter.1, hvoter.2]⟩

/--
Adding a genuinely new voter whose first active candidate is `candidate`
strictly increases `candidate`'s active-support count, provided old voters'
first active choices are unchanged.
-/
theorem activeSupport_card_lt_of_subset_forall_nextActive_eq_exists_new
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {beforeVoters afterVoters : Finset Voter}
    {before after : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : beforeVoters ⊆ afterVoters)
    (hstable : ∀ voter ∈ beforeVoters,
      nextActive (after voter) active = nextActive (before voter) active)
    (hnew : ∃ voter, voter ∈ afterVoters ∧ voter ∉ beforeVoters ∧
      nextActive (after voter) active = some candidate) :
    (activeSupport beforeVoters before active candidate).card <
      (activeSupport afterVoters after active candidate).card := by
  rcases hnew with ⟨voter, hafter, hbefore, hactive⟩
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · exact activeSupport_subset_of_subset_forall_nextActive_eq hsubset hstable
  · intro heq
    have hafterSupport :
        voter ∈ activeSupport afterVoters after active candidate := by
      simp [activeSupport, hafter, hactive]
    have hbeforeSupport :
        voter ∈ activeSupport beforeVoters before active candidate := by
      simpa [heq] using hafterSupport
    have hbeforeVoter : voter ∈ beforeVoters := by
      have hbeforeSupport' := hbeforeSupport
      simp [activeSupport] at hbeforeSupport'
      exact hbeforeSupport'.1
    exact hbefore hbeforeVoter

/--
Prefix-through-candidate strategic edits cannot add voters whose first active
candidate is the edited candidate, as long as that candidate is still active.
-/
theorem activeSupport_subset_of_preservesPrefixThrough {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hcandidate : candidate ∈ active)
    (hpreserve : ∀ voter ∈ voters,
      PreservesPrefixThrough candidate (before voter) (after voter)) :
    activeSupport voters after active candidate ⊆
      activeSupport voters before active candidate := by
  intro voter hvoter
  simp [activeSupport] at hvoter ⊢
  exact ⟨hvoter.1,
    nextActive_eq_some_of_preservesPrefixThrough
      (hpreserve voter hvoter.1) hcandidate hvoter.2⟩

/--
The number of voters whose first active candidate is `candidate` cannot increase
under prefix-through-candidate edits while `candidate` is still active.
-/
theorem activeSupport_card_le_of_preservesPrefixThrough {Voter Candidate : Type*}
    [DecidableEq Candidate] {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hcandidate : candidate ∈ active)
    (hpreserve : ∀ voter ∈ voters,
      PreservesPrefixThrough candidate (before voter) (after voter)) :
    (activeSupport voters after active candidate).card ≤
      (activeSupport voters before active candidate).card :=
  Finset.card_le_card
    (activeSupport_subset_of_preservesPrefixThrough hcandidate hpreserve)

end Ballot

end Voting
end SocialChoice
end EconCSLib
