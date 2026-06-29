import EconCSLib.SocialChoice.Voting.Ballot
import EconCSLib.SocialChoice.Voting.STV
import EconCSLib.SocialChoice.Voting.STV.Quota
import EconCSLib.SocialChoice.Voting.STV.SolidCoalition
import EconCSLib.SocialChoice.Voting.STV.Structures
import EconCSLib.SocialChoice.Voting.Thiele
import EconCSLib.SocialChoice.Voting.Proportionality

/-!
# Voting

Aggregate import for reusable voting-rule primitives.

## Main declarations

- `EconCSLib.SocialChoice.Voting.Ballot`: ranked ballots and next-active
  preference.
- `EconCSLib.SocialChoice.Voting.STV`: deterministic STV/RCV trace vocabulary.
- `EconCSLib.SocialChoice.Voting.STV.Quota`: Droop quota arithmetic.
- `EconCSLib.SocialChoice.Voting.STV.SolidCoalition`: party-level quota-process
  invariants for solid-coalition STV proofs.
- `EconCSLib.SocialChoice.Voting.STV.Structures`: final-order and win/loss
  structure replay predicates.
- `EconCSLib.SocialChoice.Voting.Thiele`: approval ballots and committee
  score primitives.
- `EconCSLib.SocialChoice.Voting.Proportionality`: two-party floor/ceiling
  seat-share arithmetic.
-/
