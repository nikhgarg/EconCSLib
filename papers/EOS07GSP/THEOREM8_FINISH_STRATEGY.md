# Theorem 8 Finish Strategy

This note is a short proof plan for the remaining EOS07GSP Theorem 8 route.

## Current Boundary

The algebraic and terminal-record layers are strong. The remaining paper-level
gap is not another payment identity; it is the source-game bridge from the
generalized-English extensive form to the finite `B*` threshold behavior:

- concrete belief consistency for the source game,
- sequential rationality iff the source-shaped reachable/off-path local
  optimality predicate,
- arbitrary-PBE behavioral characterization,
- generated-history or exact-terminal-record identification for source paths.

Sorted schedules, no-overshoot terminal histories, cold-start schedules, and
exact-drop histories already give reusable source-completion endpoints. Bare
arbitrary histories should not be used directly, because overshoot histories
can record dropout prices after the finite `B*` threshold.

The finite exact-record version is now closed in the state-game setting. The
key proof idea is to use a finite displayed `Fin n` source state whose active
ranks are exactly the scheduled ranks, while every unscheduled natural rank is
initially inactive with its exact finite `B*` record. Complete displayed
schedules then give all displayed ranks active-to-inactive, exact records, VCG
outcome, displayed slot/payment formulas, and the ordered payoff package. The
canonical wrapper
`theorem8_price_sorted_finite_schedule_pbe_displayed_ordered_conclusion`
builds the price-sorted schedule internally; its belief-explicit counterpart is
`theorem8_price_sorted_finite_schedule_belief_pbe_displayed_ordered_conclusion`.
Both still require threshold-event timing evidence for the PBE-generated source
history, so they are finite direct-PBE endpoints rather than the unconstrained
full generalized-English theorem.

## Preferred Route

1. Keep working at the source bridge layer, not in paper-interface aliases.
2. Convert concrete source paths into disciplined traces or exact-drop
   histories as early as possible.
3. Build stable theorem endpoints whose conclusions mention final
   paper-facing objects, so wrappers do not depend on proof-generated
   certificates.
4. For PBE completion, prove the game-level sequential-rationality iff from
   source reachable/off-path local optimality and tie-breaking, then derive
   named-strategy PBE, arbitrary-PBE strategy equality, and VCG outcome
   equality from that one bridge.

## Next Lean Move

Do not add more finite exact-record or price-sorted schedule wrappers unless a
reviewer asks for a different presentation. The next Lean move is the general
source theorem: prove a concrete source-history invariant that supplies
no-overshoot or clock-discipline for realized named-strategy dropouts, then
lift it to histories and feed it into the existing source-extensive or
source-shaped all-terminal endpoints. In parallel, prove the concrete
belief-consistency and source sequential-rationality iff needed by the real
generalized-English source game.
