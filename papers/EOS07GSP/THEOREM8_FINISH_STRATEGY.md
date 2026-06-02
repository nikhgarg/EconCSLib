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

Use the already green non-cold-start disciplined-trace endpoint and the
finite-schedule trace-full source-completion endpoints. Reintroduce cold-start
clock-disciplined source-completion only through a theorem with an explicit,
stable conclusion; avoid wrappers whose inferred result type depends on
internally generated proof witnesses.

Next, continue from the one-stop dynamic clock-sorted finite-schedule trace-full
source-completion bridge. It removes repeated downstream certificate
reconstruction and produces a reusable library-style bridge for future
dynamic-auction proofs.
