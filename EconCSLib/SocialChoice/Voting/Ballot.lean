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
- `Ballot.strictSupportCountWithBlockerPrefix`
- `Ballot.strictSupportCountWithAccumulatedBlockers`
- `Ballot.IsSuffixExtension`
- `Ballot.IsPrefixExtension`
- `Ballot.PreservesPrefixThrough`
- `Ballot.RespectsLength`
- `Ballot.activeSupport_card_eq_of_forall_suffixExtension_nextActive_some`
- `Ballot.activeSupport_card_eq_of_forall_prefixExtension_inactive`
- `Ballot.activeSupport_card_eq_of_forall_append_exhausted_prefix`
- `Ballot.activeSupport_card_removeCandidates_eq_of_disjoint_active`
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
Removing candidates disjoint from the active set does not change the first
active candidate.
-/
theorem nextActive_removeCandidates_eq_of_disjoint_active {Candidate : Type*}
    [DecidableEq Candidate]
    {ballot : Ballot Candidate} {active removed : Finset Candidate}
    (hdisjoint : active ∩ removed = ∅) :
    nextActive (removeCandidates removed ballot) active =
      nextActive ballot active := by
  exact nextActive_removeCandidates_eq_of_forall_not_mem (by
    intro candidate hactive hremoved
    have hmem : candidate ∈ active ∩ removed := by
      simp [hactive, hremoved]
    rw [hdisjoint] at hmem
    simpa using hmem)

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
Ordered strict-support sum with an accumulated blocker prefix.

For each candidate in the list, the strict-support count is computed with the
blockers already accumulated from earlier candidates, then the candidate is
added to the blocker set before processing the tail. This is the paper-neutral
loop shape used by STV prediction routines that avoid double-counting voters
across an ordered candidate family.
-/
def strictSupportCountWithBlockerPrefix {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) : List Candidate → ℕ
  | [] => 0
  | candidate :: rest =>
      strictSupportCount voters ballots sources blockers candidate +
        strictSupportCountWithBlockerPrefix voters ballots sources
          (insert candidate blockers) rest

/--
Quota lower-bound invariant for an accumulated-blocker strict-support loop.

At each step, the current strict-support count is at least `quota`, and the
tail is checked after inserting the current candidate into the blocker set.
-/
def StrictSupportAccumulatorQuota {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (quota : ℕ) : List Candidate → Prop
  | [] => True
  | candidate :: rest =>
      quota ≤ strictSupportCount voters ballots sources blockers candidate ∧
        StrictSupportAccumulatorQuota voters ballots sources
          (insert candidate blockers) quota rest

/--
Budgeted quota invariant for an accumulated-blocker strict-support loop.

At each step, the current strict-support count together with the budget units
assigned to the current candidate reaches `quota`.
-/
def StrictSupportAccumulatorBudgetQuota {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) : List Candidate → Prop
  | [] => True
  | candidate :: rest =>
      quota ≤ assignedBudget candidate +
          strictSupportCount voters ballots sources blockers candidate ∧
        StrictSupportAccumulatorBudgetQuota voters ballots sources
          (insert candidate blockers) assignedBudget quota rest

/--
Blockers after processing a candidate prefix in order.

This is a paper-neutral way to state loop invariants: the condition for a
candidate can refer to exactly the blockers accumulated from earlier listed
candidates.
-/
def blockersAfterPrefix {Candidate : Type*} [DecidableEq Candidate]
    (blockers : Finset Candidate) : List Candidate → Finset Candidate
  | [] => blockers
  | candidate :: rest => blockersAfterPrefix (insert candidate blockers) rest

/--
Prefix-form quota condition for an accumulated-blocker strict-support loop.
-/
def StrictSupportAccumulatorQuotaAtPrefixes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (quota : ℕ)
    (candidates : List Candidate) : Prop :=
  ∀ pref candidate suffix,
    candidates = pref ++ candidate :: suffix →
      quota ≤ strictSupportCount voters ballots sources
        (blockersAfterPrefix blockers pref) candidate

/--
Prefix-form budgeted quota condition for an accumulated-blocker
strict-support loop.
-/
def StrictSupportAccumulatorBudgetQuotaAtPrefixes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (candidates : List Candidate) : Prop :=
  ∀ pref candidate suffix,
    candidates = pref ++ candidate :: suffix →
      quota ≤ assignedBudget candidate +
        strictSupportCount voters ballots sources
          (blockersAfterPrefix blockers pref) candidate

/--
Candidates that meet the current accumulated-blocker quota test at a given
processed prefix.
-/
def strictSupportReadyCandidatesAtPrefix {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (quota : ℕ)
    (processed : List Candidate) : Finset Candidate :=
  sources.filter fun candidate =>
    quota ≤ strictSupportCount voters ballots sources
      (blockersAfterPrefix blockers processed) candidate

/--
Candidates that meet the current accumulated-blocker quota test after adding
candidate-specific budget units at a given processed prefix.
-/
def strictSupportBudgetReadyCandidatesAtPrefix {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (processed : List Candidate) : Finset Candidate :=
  sources.filter fun candidate =>
    quota ≤ assignedBudget candidate +
      strictSupportCount voters ballots sources
        (blockersAfterPrefix blockers processed) candidate

/-- Membership in the current-prefix ready set is exactly source membership plus quota support. -/
theorem mem_strictSupportReadyCandidatesAtPrefix_iff {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {quota : ℕ}
    {processed : List Candidate} {candidate : Candidate} :
    candidate ∈
        strictSupportReadyCandidatesAtPrefix voters ballots sources blockers
          quota processed ↔
      candidate ∈ sources ∧
        quota ≤ strictSupportCount voters ballots sources
          (blockersAfterPrefix blockers processed) candidate := by
  simp [strictSupportReadyCandidatesAtPrefix]

/--
Membership in the budgeted current-prefix ready set is exactly source
membership plus the budgeted quota-support inequality.
-/
theorem mem_strictSupportBudgetReadyCandidatesAtPrefix_iff
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {processed : List Candidate} {candidate : Candidate} :
    candidate ∈
        strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
          blockers assignedBudget quota processed ↔
      candidate ∈ sources ∧
        quota ≤ assignedBudget candidate +
          strictSupportCount voters ballots sources
            (blockersAfterPrefix blockers processed) candidate := by
  simp [strictSupportBudgetReadyCandidatesAtPrefix]

/--
If every selected loop item belongs to the ready-candidate set computed from
the earlier selected prefix, then the source-loop selections satisfy the
prefix-form accumulator quota condition.
-/
theorem strictSupportAccumulatorQuotaAtPrefixes_of_mem_readyCandidatesAtPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {quota : ℕ}
    {candidates : List Candidate}
    (hselected :
      ∀ pref candidate suffix,
        candidates = pref ++ candidate :: suffix →
          candidate ∈
            strictSupportReadyCandidatesAtPrefix voters ballots sources
              blockers quota pref) :
    StrictSupportAccumulatorQuotaAtPrefixes voters ballots sources blockers
      quota candidates := by
  intro pref candidate suffix hdecomp
  have hmem := hselected pref candidate suffix hdecomp
  have hready :
      candidate ∈ sources ∧
        quota ≤ strictSupportCount voters ballots sources
          (blockersAfterPrefix blockers pref) candidate := by
    simpa [strictSupportReadyCandidatesAtPrefix] using hmem
  exact hready.2

/--
If every selected loop item belongs to the budgeted ready-candidate set
computed from the earlier selected prefix, then the source-loop selections
satisfy the prefix-form budgeted accumulator quota condition.
-/
theorem strictSupportAccumulatorBudgetQuotaAtPrefixes_of_mem_budgetReadyCandidatesAtPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {candidates : List Candidate}
    (hselected :
      ∀ pref candidate suffix,
        candidates = pref ++ candidate :: suffix →
          candidate ∈
            strictSupportBudgetReadyCandidatesAtPrefix voters ballots sources
              blockers assignedBudget quota pref) :
    StrictSupportAccumulatorBudgetQuotaAtPrefixes voters ballots sources
      blockers assignedBudget quota candidates := by
  intro pref candidate suffix hdecomp
  have hmem := hselected pref candidate suffix hdecomp
  have hready :
      candidate ∈ sources ∧
        quota ≤ assignedBudget candidate +
          strictSupportCount voters ballots sources
            (blockersAfterPrefix blockers pref) candidate := by
    simpa [strictSupportBudgetReadyCandidatesAtPrefix] using hmem
  exact hready.2

/--
Build the recursive accumulator invariant from the source-loop statement that
each candidate reaches quota at its processed prefix.
-/
theorem strictSupportAccumulatorQuota_of_atPrefixes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {quota : ℕ}
    {candidates : List Candidate}
    (hprefix :
      StrictSupportAccumulatorQuotaAtPrefixes voters ballots sources blockers
        quota candidates) :
    StrictSupportAccumulatorQuota voters ballots sources blockers quota
      candidates := by
  induction candidates generalizing blockers with
  | nil =>
      trivial
  | cons candidate rest ih =>
      refine ⟨?_, ?_⟩
      · exact hprefix [] candidate rest rfl
      · refine ih ?_
        intro pref candidate' suffix hdecomp
        exact hprefix (candidate :: pref) candidate' suffix (by
          simp [hdecomp])

/--
Build the recursive budgeted accumulator invariant from the source-loop
statement that each candidate reaches quota at its processed prefix after
adding the candidate-specific budget.
-/
theorem strictSupportAccumulatorBudgetQuota_of_atPrefixes
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {sources blockers : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {candidates : List Candidate}
    (hprefix :
      StrictSupportAccumulatorBudgetQuotaAtPrefixes voters ballots sources
        blockers assignedBudget quota candidates) :
    StrictSupportAccumulatorBudgetQuota voters ballots sources blockers
      assignedBudget quota candidates := by
  induction candidates generalizing blockers with
  | nil =>
      trivial
  | cons candidate rest ih =>
      refine ⟨?_, ?_⟩
      · exact hprefix [] candidate rest rfl
      · refine ih ?_
        intro pref candidate' suffix hdecomp
        exact hprefix (candidate :: pref) candidate' suffix (by
          simp [hdecomp])

@[simp] theorem strictSupportCountWithBlockerPrefix_nil
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) :
    strictSupportCountWithBlockerPrefix voters ballots sources blockers [] = 0 :=
  rfl

@[simp] theorem strictSupportCountWithBlockerPrefix_cons
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate)
    (rest : List Candidate) :
    strictSupportCountWithBlockerPrefix voters ballots sources blockers
        (candidate :: rest) =
      strictSupportCount voters ballots sources blockers candidate +
        strictSupportCountWithBlockerPrefix voters ballots sources
          (insert candidate blockers) rest :=
  rfl

/--
If every counted term in an accumulated-blocker loop is at least `quota`, then
the full accumulator is at least `quota` times the list length.
-/
theorem quota_mul_length_le_strictSupportCountWithBlockerPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (quota : ℕ)
    (candidates : List Candidate)
    (hquota :
      StrictSupportAccumulatorQuota voters ballots sources blockers quota
        candidates) :
    quota * candidates.length ≤
      strictSupportCountWithBlockerPrefix voters ballots sources blockers
        candidates := by
  induction candidates generalizing blockers with
  | nil =>
      simp [strictSupportCountWithBlockerPrefix]
  | cons candidate rest ih =>
      rcases hquota with ⟨hhead, htail⟩
      have htail_le :
          quota * rest.length ≤
            strictSupportCountWithBlockerPrefix voters ballots sources
              (insert candidate blockers) rest :=
        ih (blockers := insert candidate blockers) htail
      calc
        quota * (candidate :: rest).length = quota + quota * rest.length := by
          simp [Nat.mul_succ, Nat.add_comm]
        _ ≤ strictSupportCount voters ballots sources blockers candidate +
            strictSupportCountWithBlockerPrefix voters ballots sources
              (insert candidate blockers) rest :=
          Nat.add_le_add hhead htail_le
        _ =
            strictSupportCountWithBlockerPrefix voters ballots sources blockers
              (candidate :: rest) := rfl

/--
If every counted term in an accumulated-blocker loop reaches `quota` after
including candidate-specific budget units, then the full support accumulator
plus the assigned-budget sum is at least `quota` times the list length.
-/
theorem quota_mul_length_le_budget_sum_add_strictSupportCountWithBlockerPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources blockers : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (candidates : List Candidate)
    (hquota :
      StrictSupportAccumulatorBudgetQuota voters ballots sources blockers
        assignedBudget quota candidates) :
    quota * candidates.length ≤
      (candidates.map assignedBudget).sum +
        strictSupportCountWithBlockerPrefix voters ballots sources blockers
          candidates := by
  induction candidates generalizing blockers with
  | nil =>
      simp [strictSupportCountWithBlockerPrefix]
  | cons candidate rest ih =>
      rcases hquota with ⟨hhead, htail⟩
      have htail_le :
          quota * rest.length ≤
            (rest.map assignedBudget).sum +
              strictSupportCountWithBlockerPrefix voters ballots sources
                (insert candidate blockers) rest :=
        ih (blockers := insert candidate blockers) htail
      calc
        quota * (candidate :: rest).length = quota + quota * rest.length := by
          simp [Nat.mul_succ, Nat.add_comm]
        _ ≤
            (assignedBudget candidate +
                strictSupportCount voters ballots sources blockers candidate) +
              ((rest.map assignedBudget).sum +
                strictSupportCountWithBlockerPrefix voters ballots sources
                  (insert candidate blockers) rest) :=
          Nat.add_le_add hhead htail_le
        _ =
            ((candidate :: rest).map assignedBudget).sum +
              strictSupportCountWithBlockerPrefix voters ballots sources blockers
                (candidate :: rest) := by
          simp [strictSupportCountWithBlockerPrefix, Nat.add_assoc,
            Nat.add_left_comm]

/--
Ordered strict-support sum with no initial blockers.

This is the usual support accumulator for a prediction loop that traverses a
candidate list and treats earlier selected candidates as blockers for later
strict-support counts.
-/
def strictSupportCountWithAccumulatedBlockers {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) (candidates : List Candidate) : ℕ :=
  strictSupportCountWithBlockerPrefix voters ballots sources ∅ candidates

@[simp] theorem strictSupportCountWithAccumulatedBlockers_nil
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) :
    strictSupportCountWithAccumulatedBlockers voters ballots sources [] = 0 :=
  rfl

@[simp] theorem strictSupportCountWithAccumulatedBlockers_cons
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) (candidate : Candidate)
    (rest : List Candidate) :
    strictSupportCountWithAccumulatedBlockers voters ballots sources
        (candidate :: rest) =
      strictSupportCount voters ballots sources ∅ candidate +
        strictSupportCountWithBlockerPrefix voters ballots sources
          (insert candidate ∅) rest :=
  rfl

/-- No-initial-blocker form of
`quota_mul_length_le_strictSupportCountWithBlockerPrefix`. -/
theorem quota_mul_length_le_strictSupportCountWithAccumulatedBlockers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) (quota : ℕ) (candidates : List Candidate)
    (hquota :
      StrictSupportAccumulatorQuota voters ballots sources ∅ quota
        candidates) :
    quota * candidates.length ≤
      strictSupportCountWithAccumulatedBlockers voters ballots sources
        candidates := by
  exact quota_mul_length_le_strictSupportCountWithBlockerPrefix
    voters ballots sources ∅ quota candidates hquota

/-- No-initial-blocker budgeted form of
`quota_mul_length_le_budget_sum_add_strictSupportCountWithBlockerPrefix`. -/
theorem quota_mul_length_le_budget_sum_add_strictSupportCountWithAccumulatedBlockers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (sources : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (candidates : List Candidate)
    (hquota :
      StrictSupportAccumulatorBudgetQuota voters ballots sources ∅
        assignedBudget quota candidates) :
    quota * candidates.length ≤
      (candidates.map assignedBudget).sum +
        strictSupportCountWithAccumulatedBlockers voters ballots sources
          candidates := by
  exact quota_mul_length_le_budget_sum_add_strictSupportCountWithBlockerPrefix
    voters ballots sources ∅ assignedBudget quota candidates hquota

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
If the removed candidates are disjoint from the current active set, deleting
them from every ballot preserves active support at that active set.
-/
theorem activeSupport_removeCandidates_eq_of_disjoint_active
    {Voter Candidate : Type*} [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active removed : Finset Candidate}
    {candidate : Candidate} (hdisjoint : active ∩ removed = ∅) :
    activeSupport voters
        (fun voter => removeCandidates removed (ballots voter))
        active candidate =
      activeSupport voters ballots active candidate := by
  ext voter
  by_cases hvoter : voter ∈ voters
  · simp [activeSupport, hvoter,
      nextActive_removeCandidates_eq_of_disjoint_active hdisjoint]
  · simp [activeSupport, hvoter]

/--
If the removed candidates are disjoint from the current active set, deleting
them from every ballot preserves active-support counts at that active set.
-/
theorem activeSupport_card_removeCandidates_eq_of_disjoint_active
    {Voter Candidate : Type*} [DecidableEq Candidate] {voters : Finset Voter}
    {ballots : Voter → Ballot Candidate} {active removed : Finset Candidate}
    {candidate : Candidate} (hdisjoint : active ∩ removed = ∅) :
    (activeSupport voters
        (fun voter => removeCandidates removed (ballots voter))
        active candidate).card =
      (activeSupport voters ballots active candidate).card := by
  rw [activeSupport_removeCandidates_eq_of_disjoint_active hdisjoint]

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
Suffixing every ballot in a voter profile preserves active-support counts at an
active set, provided each original ballot already reaches some active
candidate at that set.
-/
theorem activeSupport_eq_of_forall_suffixExtension_nextActive_some
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hext : ∀ voter ∈ voters, IsSuffixExtension (before voter) (after voter))
    (hreaches : ∀ voter ∈ voters,
      ∃ first, nextActive (before voter) active = some first) :
    activeSupport voters after active candidate =
      activeSupport voters before active candidate := by
  exact activeSupport_eq_of_forall_nextActive_eq (by
    intro voter hvoter
    rcases hext voter hvoter with ⟨suffix, hsuffix⟩
    rcases hreaches voter hvoter with ⟨first, hfirst⟩
    have hafter : nextActive (after voter) active = some first := by
      rw [hsuffix]
      exact nextActive_append_of_some hfirst
    rw [hafter, hfirst])

/--
Suffixing every ballot in a voter profile preserves active-support counts at an
active set, provided each original ballot already reaches some active
candidate at that set.
-/
theorem activeSupport_card_eq_of_forall_suffixExtension_nextActive_some
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {before after : Voter → Ballot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hext : ∀ voter ∈ voters, IsSuffixExtension (before voter) (after voter))
    (hreaches : ∀ voter ∈ voters,
      ∃ first, nextActive (before voter) active = some first) :
    (activeSupport voters after active candidate).card =
      (activeSupport voters before active candidate).card := by
  rw [activeSupport_eq_of_forall_suffixExtension_nextActive_some hext hreaches]

/--
Prefixing inactive candidates onto every ballot in a voter profile preserves
active-support sets at the current active set.
-/
theorem activeSupport_eq_of_forall_prefixExtension_inactive
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref before after : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hext : ∀ voter ∈ voters,
      IsPrefixExtension (pref voter) (before voter) (after voter))
    (hpref : ∀ voter ∈ voters, ∀ c, c ∈ pref voter → c ∉ active) :
    activeSupport voters after active candidate =
      activeSupport voters before active candidate := by
  exact activeSupport_eq_of_forall_nextActive_eq (by
    intro voter hvoter
    rw [hext voter hvoter]
    exact nextActive_append_left_of_forall_not_mem (hpref voter hvoter))

/--
Prefixing inactive candidates onto every ballot in a voter profile preserves
active-support counts at the current active set.
-/
theorem activeSupport_card_eq_of_forall_prefixExtension_inactive
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref before after : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hext : ∀ voter ∈ voters,
      IsPrefixExtension (pref voter) (before voter) (after voter))
    (hpref : ∀ voter ∈ voters, ∀ c, c ∈ pref voter → c ∉ active) :
    (activeSupport voters after active candidate).card =
      (activeSupport voters before active candidate).card := by
  rw [activeSupport_eq_of_forall_prefixExtension_inactive hext hpref]

/--
Appending a strategy ballot after an exhausted prefix for every voter preserves
the active-support sets of the strategy ballots at the current active set.
-/
theorem activeSupport_eq_of_forall_append_exhausted_prefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref strategy completed : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = pref voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ voters,
      nextActive (pref voter) active = none) :
    activeSupport voters completed active candidate =
      activeSupport voters strategy active candidate := by
  exact activeSupport_eq_of_forall_nextActive_eq (by
    intro voter hvoter
    rw [hcompleted voter hvoter]
    exact nextActive_append_of_none (hexhausted voter hvoter))

/--
Appending a strategy ballot after an exhausted prefix for every voter preserves
the active-support counts of the strategy ballots at the current active set.
-/
theorem activeSupport_card_eq_of_forall_append_exhausted_prefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref strategy completed : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = pref voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ voters,
      nextActive (pref voter) active = none) :
    (activeSupport voters completed active candidate).card =
      (activeSupport voters strategy active candidate).card := by
  rw [activeSupport_eq_of_forall_append_exhausted_prefix
    hcompleted hexhausted]

/--
If every voter in `available` belongs to `voters` and activates `candidate`,
then `candidate`'s active support is at least `available.card`.
-/
theorem card_le_activeSupport_card_of_subset_forall_nextActive_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {available voters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : available ⊆ voters)
    (hactive : ∀ voter ∈ available,
      nextActive (ballots voter) active = some candidate) :
    available.card ≤ (activeSupport voters ballots active candidate).card := by
  apply Finset.card_le_card
  intro voter hvoter
  simp [activeSupport, hsubset hvoter, hactive voter hvoter]

/--
Completing available exhausted ballots with strategy ballots that activate
`candidate` gives at least one active-support voter per available ballot.
-/
theorem card_le_activeSupport_card_of_subset_forall_append_exhausted_prefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {available voters : Finset Voter}
    {pref strategy completed : Voter → Ballot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hsubset : available ⊆ voters)
    (hcompleted : ∀ voter ∈ available,
      completed voter = pref voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ available,
      nextActive (pref voter) active = none)
    (hstrategy : ∀ voter ∈ available,
      nextActive (strategy voter) active = some candidate) :
    available.card ≤ (activeSupport voters completed active candidate).card :=
  card_le_activeSupport_card_of_subset_forall_nextActive_eq hsubset (by
    intro voter hvoter
    rw [hcompleted voter hvoter]
    exact (nextActive_append_of_none (hexhausted voter hvoter)).trans
      (hstrategy voter hvoter))

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

/--
A finite source witness that a prediction routine has identified an initial
loss prefix whose length is large enough for a claimed lower bound.
-/
structure InitialLossPrefixCertificate {Candidate Sequence : Type*}
    (lossCandidates : Finset Candidate)
    (initialLossCount : Sequence → ℕ)
    (lowerInitialLosses : ℕ) (sequence : Sequence) where
  lossPrefix : List Candidate
  prefix_nodup : lossPrefix.Nodup
  prefix_subset_lossCandidates :
    ∀ candidate, candidate ∈ lossPrefix → candidate ∈ lossCandidates
  lower_le_prefix_length : lowerInitialLosses ≤ lossPrefix.length
  prefix_length_le_initialLossCount :
    lossPrefix.length ≤ initialLossCount sequence

/-- Project the lower-initial-loss inequality from a concrete prefix witness. -/
theorem lowerInitialLosses_le_initialLossCount_of_initialLossPrefixCertificate
    {Candidate Sequence : Type*} {lossCandidates : Finset Candidate}
    {initialLossCount : Sequence → ℕ} {lowerInitialLosses : ℕ}
    {sequence : Sequence}
    (cert :
      InitialLossPrefixCertificate lossCandidates initialLossCount
        lowerInitialLosses sequence) :
    lowerInitialLosses ≤ initialLossCount sequence :=
  le_trans cert.lower_le_prefix_length cert.prefix_length_le_initialLossCount

/--
Per-sequence initial-loss prefix witnesses give the loss-floor premise used by
sequence-reduction coverage arguments.
-/
theorem loss_floor_of_initialLossPrefixCertificates
    {Candidate Sequence : Type*} {lossCandidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {initialLossCount : Sequence → ℕ} {lowerInitialLosses : ℕ}
    (cert :
      ∀ sequence, feasibleSequence sequence →
        InitialLossPrefixCertificate lossCandidates initialLossCount
          lowerInitialLosses sequence) :
    ∀ sequence, feasibleSequence sequence →
      lowerInitialLosses ≤ initialLossCount sequence := by
  intro sequence hfeasible
  exact lowerInitialLosses_le_initialLossCount_of_initialLossPrefixCertificate
    (cert sequence hfeasible)

end Voting
end SocialChoice
end EconCSLib
