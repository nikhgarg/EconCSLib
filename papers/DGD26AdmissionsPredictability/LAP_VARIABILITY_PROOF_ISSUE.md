# Linear Assignment Variability: Resolved Proof Note

## Resolution Status

This note originally isolated the remaining mathematical issue in the
formalization of the linear assignment problem (LAP) variability theorem from
Dong, Garg, and Dean, "Capacity Constraints Make Admissions Processes Less
Predictable."

The issue is now resolved in Lean.  The proof uses a proper-suffix exchange
argument rather than the informal same-slot survivor argument from the paper
proof sketch.  The key checked declarations are:

- `false_of_forward_suffix_exchange_slotBelow`
- `not_slotBelow_old_occupant_lost_of_lap_borderline_loss`
- `same_slot_order_borderline_injective_of_selectsUniqueGlobalOptima_of_slotNoTies`
- `variabilityAtMost_choiceRuleOfAssignment_of_distinct_slot_orders`
- `paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement`

The original handoff text is retained below because it documents the proof
hazard and the counterexample criteria that motivated the suffix-exchange
proof.

## Model

Let:

- `U` be a finite set of applicants.
- `S` be a finite set of slots, with capacity one per slot.
- `w : U x S -> R` be a weight function. In the Lean development `R` is `Z`,
  but rational or real weights are mathematically equivalent for the question.
- For every slot `s`, assume there are no ties:
  `w(a,s) != w(b,s)` whenever `a != b`.

For a finite applicant pool `X subset U`, a feasible assignment matches each
slot to at most one applicant in `X`, and no applicant is assigned to more than
one slot. The selected assignment is a maximum-weight assignment:

```text
maximize   sum_{s in S} w(A(s), s)
subject to each slot has at most one applicant,
           each applicant is used at most once,
           assigned applicants lie in X,
           and the assignment fills all slots whenever |X| >= |S|.
```

The choice set `C(X)` is the set of applicants assigned by the selected
maximum-weight assignment. Assume the chosen set is unique for every pool `X`.
The assignment itself may have ties, but all optimal assignments must choose the
same set of applicants.

Two slots `s,t` have the same induced preference order if, for all applicants
`a,b`,

```text
w(a,s) < w(b,s)   iff   w(a,t) < w(b,t).
```

Equivalently, sorting applicants by `w(.,s)` and `w(.,t)` gives the same strict
ranking. Let `m` be the number of distinct slot order classes.

For a fixed pool `X`, define the borderline or variable set:

```text
V_C(X) = { y in C(X) : exists x notin X such that y notin C(X union {x}) }.
```

The paper claims that LAP variability is bounded by the number of distinct
slot orders:

```text
|V_C(X)| <= m        for every X.
```

## Main Theorem To Prove Or Refute

**Theorem (LAP distinct-order variability bound).**
Under the assumptions above, for every finite pool `X`,

```text
|V_C(X)| <= number of distinct slot-induced applicant orders.
```

A stronger pointwise form sufficient for the theorem is:

**Same-order borderline injectivity.**
Let `y,z in V_C(X)`. Suppose, in the selected assignment for `X`, applicant `y`
is assigned to slot `s_y` and applicant `z` is assigned to slot `s_z`. If
`s_y` and `s_z` have the same induced applicant order, then `y = z`.

Equivalently, each slot-order class contributes at most one applicant to
`V_C(X)`.

## Local Kernel Where The Proof Is Stuck

The current Lean development has reduced the theorem to the following local
claim.

Take a pool `X`, a fresh applicant `x notin X`, and let:

- `A` be the selected maximum-weight assignment for `X`.
- `B` be the selected maximum-weight assignment for `X union {x}`.
- `y` be an old applicant lost after adding `x`:

```text
y in C(X) \ C(X union {x}).
```

The formalization already proves that this is an exact one-for-one exchange:

```text
C(X union {x}) = {x} union (C(X) \ {y}).
```

Let:

- `root` be the slot where `B(root) = x`.
- `lost` be the old slot where `A(lost) = y`.
- `oldSlot` be another old slot where `A(oldSlot) = z`.

Assume:

```text
oldSlot and lost have the same induced applicant order,
z is strictly below y in that order, i.e. w(z, oldSlot) < w(y, oldSlot).
```

The desired local contradiction is:

```text
Such a loss of y is impossible.
```

If this local contradiction holds, then in any same-order class only the worst
old occupant in that class can be borderline, which proves the distinct-order
variability bound.

## What The Paper's Informal Proof Says

The paper argues:

If `y` outranks the current occupant `z` of another same-order slot, then `y`
cannot be variable. If `y` were lost after adding a new applicant, the lower
occupant `z` would still be chosen by 1-instability, and the LAP ordering lemma
would force `y` to be chosen too.

The problem is that in a general linear assignment, `z` may survive by moving
to a different slot. The proof cannot assume that `z` remains in `oldSlot`.

The missing formal step is exactly to handle this reassignment.

## Already-Proved Facts

The current Lean proof has established the following mathematical facts.

### 1. LAP is 1-unstable

Adding one fresh applicant changes the chosen set by at most one old applicant.
In the loss case, adding `x` and losing `y` is an exact one-for-one exchange:

```text
C(X union {x}) = {x} union (C(X) \ {y}).
```

Thus every old chosen applicant other than `y` remains chosen after the
insertion, though possibly in a different slot.

### 2. Directed alternating path

Define a directed edge from an old slot `s` to a new slot `t` when the old
occupant of `s` is assigned to `t` after insertion:

```text
s -> t    iff    exists a, A(s) = a and B(t) = a.
```

The proof establishes:

- `root`, the new slot of `x`, has no incoming edge, since `x` was not assigned
  before.
- `lost`, the old slot of `y`, has no outgoing edge, since `y` is not assigned
  after insertion.
- Directed edges are left-unique and right-unique, using no-duplicate
  assignments.
- The directed path starting at `root` reaches `lost`.
- Every slot in the reachable set from `root` lies on the directed path to
  `lost`.

So, abstractly, the exact exchange has a path form:

```text
s_0 = root, s_1, ..., s_k = lost

B(s_0) = x
A(s_i) = B(s_{i+1})  for i = 0,...,k-1
A(s_k) = y.
```

There may be other disjoint cycles elsewhere, but they are irrelevant to this
fresh-to-lost path.

### 3. Dominated old slots lie on the fresh-to-lost path

If `A(oldSlot) = z` and `w(z, oldSlot) < w(y, oldSlot)`, then `oldSlot` lies on
the directed path from `root` to `lost`.

Proof idea already formalized:

If `oldSlot` were outside the path, splice the path of `B` into `A`. In the
resulting enlarged-pool optimum, `oldSlot` still contains `z` while `y` is
rejected. Replacing `z` by `y` at `oldSlot` would improve the objective,
contradicting local optimality.

### 4. The first move from such an old slot leaves the order class

If `A(oldSlot) = z`, `z` is below `y` in `oldSlot`, and `z` survives after the
insertion, then `z` cannot be assigned after insertion to a slot with the same
order as `oldSlot`.

Proof idea already formalized:

In `B`, applicant `y` is rejected. If `B(newSlot) = z` and `newSlot` has the
same order as `oldSlot`, then local optimality of `B` says `z` must be at least
as high as `y` in `newSlot`, contradicting `z < y` transported from
`oldSlot`.

### 5. Therefore the path leaves and re-enters the order class

Since `oldSlot` and `lost` are assumed to have the same order:

- the first edge out of `oldSlot` goes to a slot outside this order class;
- the path eventually ends at `lost`, inside this order class.

The Lean proof now has a clean re-entry statement:

There exist consecutive slots `u -> v` on the path such that:

```text
u is outside the order class of oldSlot,
v is inside the order class of oldSlot.
```

## Resolved Mathematical Hurdle

The successful proof uses a proper-suffix exchange.  The direct
leave-and-reenter argument is too weak because it only controls ordinal
comparisons inside one order class; the proper suffix argument instead compares
two complementary splices and uses global optimality of both assignments.

Let the path be:

```text
s_0 = root, s_1, ..., s_k = lost,
B(s_0) = x,
A(s_i) = B(s_{i+1}) for i < k,
A(s_k) = y.
```

Suppose `oldSlot = s_i`, with `A(s_i) = z` and `z < y` in the order shared by
`s_i` and `s_k`.

Consider the old-pool assignment `E_i` obtained from `A` by:

```text
put y in s_i,
put A(s_i) in s_{i+1},
put A(s_{i+1}) in s_{i+2},
...
put A(s_{k-1}) in s_k,
leave all other slots as in A.
```

This assignment is feasible for the old pool: it removes duplicate `z` by
replacing `oldSlot` with `y`, and `y` was removed from `lost` by the suffix
shift.

Old optimality of `A` gives:

```text
w(y,s_i) + sum_{j=i}^{k-1} w(A(s_j), s_{j+1})
  <=
sum_{j=i}^{k} w(A(s_j), s_j),

where A(s_k) = y.
```

The direct inequality above is not the proof used in Lean: it still tries to
reason about the whole segment cardinally.  The checked proof instead takes
the suffix beginning after `oldSlot`, splices that suffix of `B` into `A`, and
then replaces the duplicate root occupant `z` by the lost applicant `y` at
`oldSlot`.  The complementary suffix splice is feasible for the enlarged pool,
so optimality of `B` plus the complementary-splice objective identity gives
`objective A <= objective C`.  Replacing `z` by `y` at `oldSlot` strictly
improves `C`, while the resulting assignment is feasible for the old pool;
old-pool optimality then gives the contradiction.

This proves the stronger kernel:

```text
If y is the unique old applicant lost after inserting x, then no old chosen
occupant z can occupy an old slot p with w(z,p) < w(y,p).
```

## Historical Question For Another Agent

This is now answered by the checked suffix-exchange proof.  The original
request was to answer one of the following.

### Option A: Prove the local kernel

Prove that the local kernel is true under the stated assumptions:

```text
If A(oldSlot) = z, A(lost) = y, oldSlot and lost have the same induced order,
and z is below y in that order, then y cannot be the unique old applicant lost
after adding one fresh applicant x.
```

Useful path facts are available as assumptions:

```text
s_0 = root, s_k = lost,
B(s_0) = x,
A(s_i) = B(s_{i+1}) for i < k,
A(s_k) = y,
oldSlot = s_i for some i,
oldSlot and lost have the same induced order,
A(oldSlot) = z,
w(z, oldSlot) < w(y, oldSlot).
```

Also use:

- `A` is maximum weight for the old pool `X`.
- `B` is maximum weight for the enlarged pool `X union {x}`.
- The chosen set is unique for each pool.
- Each slot has no ties.
- Same-order slots induce the same strict ranking, but may have different
  cardinal weight gaps.

### Option B: Prove only the global theorem

Even if the local kernel is false, the global theorem may still be true.
Prove directly that:

```text
|V_C(X)| <= number of slot order classes.
```

In this case, a proof may need a more global injection from borderline
applicants to order classes, rather than the "only the worst old occupant in a
class is variable" argument.

### Option C: Find a counterexample

A counterexample to the global theorem should specify:

- A finite applicant set `U`.
- A finite slot set `S`.
- A weight table `w(a,s)`.
- A partition of slots into induced-order classes, computed from the weight
  table.
- A pool `X`.
- The unique chosen set `C(X)`.
- For more than `m` different applicants in `C(X)`, fresh applicants whose
  addition causes those applicants to be lost.

Equivalently, show:

```text
|V_C(X)| > m.
```

A weaker but still useful counterexample to the paper's proof strategy would
show the local kernel is false:

- `A(oldSlot) = z`, `A(lost) = y`;
- `oldSlot` and `lost` have the same induced order;
- `z` is below `y` in that order;
- after adding a fresh applicant `x`, `y` is lost but `z` remains chosen by
  moving to another slot.

That would not automatically refute the global theorem, but it would confirm
that the paper's proof needs a different argument.

## Counterexample Search Before Resolution

No counterexample was found before the suffix-exchange proof was completed.

Searches already run:

- Small bounded random search over unique-optimum instances: no counterexample.
- Exhaustive strict-weight search over 72,000 small configurations with three
  slots, two same-order slots plus one other slot: no counterexample.
- Additional random searches with four to six slots and repeated order classes
  have also not found a counterexample so far.

These searches are only sanity checks. They are not a proof.

## Lean Implementation Pointers

The relevant Lean file is:

```text
papers/DGD26AdmissionsPredictability/LAP.lean
```

Important definitions/theorems already present:

- `SameSlotOrder`
- `SlotNoTies`
- `choice_insert_eq_insert_erase_choice_of_lap_borderline_loss`
- `lost_slot_mem_forwardSlotReachSet_of_lap_borderline_loss`
- `not_exists_forwardSlotLinked_from_lost_of_lap_borderline_loss`
- `not_exists_forwardSlotLinked_to_fresh_root`
- `forwardSlotLinked_rightUnique_of_noDuplicate`
- `forwardSlotLinked_leftUnique_of_noDuplicate`
- `not_forward_reaches_back_of_reachable_of_root_no_incoming`
- `not_mem_forwardSlotReachSet_successor_of_mem_fresh_root_reachSet`
- `old_slot_mem_forwardSlotReachSet_of_slotBelow_lost_of_lap_borderline_loss`
- `exists_forward_move_not_same_order_of_loss_of_slotBelow`
- `exists_cross_order_successor_reaches_lost_of_slotBelow_lost`
- `exists_forward_reentry_sameSlotOrder_of_path`
- `exists_reentry_edge_sameSlotOrder_of_slotBelow_lost`

The bridge theorem that would finish the paper's LAP variability claim is:

```text
variabilityAtMost_choiceRuleOfAssignment_of_same_slot_order_borderline_injective
```

It needs the same-order borderline injectivity kernel:

```text
For any X and any y,z in borderlineSet(C,X),
if y and z are assigned by A=select X to same-order slots,
then y = z.
```

## Current Best Guess

The theorem may be true, but the proof likely requires a real alternating-path
exchange lemma or a valuated-matroid/gross-substitutes argument. The simple
paper proof is not enough because it ignores reassignment across slots.

The most promising next proof route is:

1. Formalize the suffix assignment `E_i` described above.
2. Prove it is feasible and capacity-filling for the old pool.
3. Use optimality of `A` and `B` to derive path inequalities.
4. Show that a path leaving and later re-entering a same-order class violates
   those inequalities, or discover that arbitrary cardinal weights allow a
   counterexample.
