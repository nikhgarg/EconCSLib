# LAP Variability Bound: Alternating-Path Exchange Proof Handoff

## Status

The local kernel appears to be true. The missing step is not a leave-and-reenter order-class contradiction. Instead, the useful lemma is a stronger pointwise dominance statement along the fresh-to-lost alternating path.

The key fix is to pair the old-pool suffix exchange with a second, reverse-tail exchange in the enlarged pool. The second inequality cancels the uncontrolled cardinal contribution from all slots outside the common order class.

The proof below should be suitable as a Lean formalization target.

---

## 1. Setup and notation

Let:

- `X` be the old applicant pool.
- `x ∉ X` be the fresh applicant.
- `A` be a maximum-weight selected assignment for `X`.
- `B` be a maximum-weight selected assignment for `X ∪ {x}`.
- `y ∈ C(X) \ C(X ∪ {x})` be the old applicant lost after adding `x`.

Assume the already-proved exact one-for-one exchange and path facts. Thus there is a fresh-to-lost directed alternating path

```text
s₀ = root, s₁, ..., sₖ = lost
```

with

```text
B(s₀) = x,
A(sⱼ) = B(sⱼ₊₁)    for 0 ≤ j < k,
A(sₖ) = y.
```

For the proof below, use the abbreviation

```text
aⱼ := A(sⱼ)          for 0 ≤ j < k,
aₖ := y = A(sₖ).
```

Then the path identities are

```text
B(s₀) = x,
B(sⱼ₊₁) = aⱼ        for 0 ≤ j < k,
A(sⱼ) = aⱼ          for 0 ≤ j ≤ k.
```

The path should be represented in Lean by a no-duplicate list/vector of slots. The no-duplicate property is needed for feasibility of the competitor assignments and for cancellation of outside terms. If assignments are `Option`-valued and may be partial, every slot on this path is assigned in the relevant assignment by the displayed path identities; the competitor assignments below preserve the set of assigned slots.

The case `k = 0` means the fresh applicant directly replaces `y` in the same slot. The tail lemma below has no index `i < k` in that case. All local-kernel applications have an old slot different from `lost`, hence correspond to some `i < k`. The case `i = k-1` is allowed: the new-pool tail then consists only of the lost slot, and the middle sums are empty.

---

## 2. Main lemma to formalize

### Lemma: lost applicant is never better than a displaced path occupant at that occupant's old slot

For every `i < k`,

```text
w(y, sᵢ) ≤ w(aᵢ, sᵢ).
```

Equivalently,

```text
w(A(sₖ), sᵢ) ≤ w(A(sᵢ), sᵢ).
```

This is stronger than the local same-order kernel. It uses only optimality of `A` and `B` plus the path identities. It does not use same-order assumptions, slot no-ties, or uniqueness of the chosen set, except insofar as those hypotheses were already used to obtain the one-for-one path setup.

---

## 3. Tail sums

Fix `i < k`. Define

```text
Pᵢ := ∑_{j=i}^{k-1} w(aⱼ, sⱼ₊₁)
```

and

```text
Qᵢ := ∑_{j=i+1}^{k} w(aⱼ, sⱼ).
```

Expanded,

```text
Pᵢ = w(aᵢ, sᵢ₊₁) + w(aᵢ₊₁, sᵢ₊₂) + ... + w(aₖ₋₁, sₖ),
```

while

```text
Qᵢ = w(aᵢ₊₁, sᵢ₊₁) + ... + w(aₖ₋₁, sₖ₋₁) + w(y, sₖ).
```

Interpretation:

- `Pᵢ` is the value, in `B`, of the old occupants shifted one step forward along the tail `sᵢ₊₁, ..., sₖ`.
- `Qᵢ` is the value, in `A`, of the same tail after deleting the first path applicant `aᵢ`; it includes `y` at `sₖ`.

The proof will derive:

```text
w(y, sᵢ) + Pᵢ ≤ w(aᵢ, sᵢ) + Qᵢ       (old-pool optimality)
Qᵢ ≤ Pᵢ                                (new-pool optimality)
```

and therefore

```text
w(y, sᵢ) ≤ w(aᵢ, sᵢ).
```

---

## 4. Old-pool suffix exchange

Construct an assignment `Eᵢ` for the old pool `X` by rotating the suffix

```text
sᵢ, sᵢ₊₁, ..., sₖ
```

one step forward, with `y = aₖ` moved to the first slot:

```text
Eᵢ(sᵢ)     = y,
Eᵢ(sⱼ₊₁)   = aⱼ       for i ≤ j < k,
Eᵢ(t)      = A(t)     for every other slot t.
```

Equivalently,

```text
Eᵢ(sᵢ)   = A(sₖ),
Eᵢ(sⱼ)   = A(sⱼ₋₁)   for i < j ≤ k,
Eᵢ(t)    = A(t)      outside the suffix.
```

### Feasibility of `Eᵢ`

`Eᵢ` is feasible for `X` because:

1. Every applicant used by `Eᵢ` on the suffix is already used by `A` on the same suffix.
2. The suffix applicants are pairwise distinct, since `A` is a feasible assignment and the path slots are distinct.
3. Outside the suffix, `Eᵢ` agrees with `A`.
4. No suffix applicant appears outside the suffix in `A`, again by feasibility of `A`.
5. Hence `Eᵢ` uses exactly the same chosen applicant set as `A`, only permuted among suffix slots.
6. It assigns exactly the same set of slots as `A`, so any capacity-filling side condition is preserved.

Thus `Eᵢ` is a valid competitor for the old-pool optimum `A`.

### Inequality from optimality of `A`

Since `A` is optimal for `X`,

```text
value(Eᵢ) ≤ value(A).
```

The assignments agree outside the suffix, so outside terms cancel. On the suffix,

```text
value(Eᵢ on suffix)
  = w(y, sᵢ) + ∑_{j=i}^{k-1} w(aⱼ, sⱼ₊₁)
  = w(y, sᵢ) + Pᵢ.
```

Also,

```text
value(A on suffix)
  = w(aᵢ, sᵢ) + ∑_{j=i+1}^{k} w(aⱼ, sⱼ)
  = w(aᵢ, sᵢ) + Qᵢ.
```

Therefore

```text
w(y, sᵢ) + Pᵢ ≤ w(aᵢ, sᵢ) + Qᵢ.       (1)
```

---

## 5. Enlarged-pool reverse-tail exchange

Construct an assignment `Fᵢ` for the enlarged pool `X ∪ {x}` by reversing the shifted tail after `sᵢ`:

```text
Fᵢ(sⱼ) = aⱼ       for i < j ≤ k,
Fᵢ(t)  = B(t)     for every other slot t.
```

Equivalently, on the tail `sᵢ₊₁, ..., sₖ`, set `Fᵢ` equal to `A`; outside that tail, leave `B` unchanged.

Thus:

```text
Fᵢ(sᵢ₊₁) = aᵢ₊₁,
Fᵢ(sᵢ₊₂) = aᵢ₊₂,
...
Fᵢ(sₖ₋₁) = aₖ₋₁,
Fᵢ(sₖ)   = y.
```

The slot `sᵢ` is not changed. In particular:

- if `i = 0`, then `Fᵢ(s₀) = B(s₀) = x`;
- if `i > 0`, then `Fᵢ(sᵢ) = B(sᵢ) = aᵢ₋₁`.

### Feasibility of `Fᵢ`

`Fᵢ` is feasible for `X ∪ {x}` because it is obtained from `B` by removing `aᵢ` from the shifted tail and inserting `y` at the lost slot.

More explicitly:

1. In `B`, the tail `sᵢ₊₁, ..., sₖ` contains

   ```text
   aᵢ, aᵢ₊₁, ..., aₖ₋₁,
   ```

   because `B(sⱼ₊₁) = aⱼ` for `i ≤ j < k`.

2. In `Fᵢ`, the same tail contains

   ```text
   aᵢ₊₁, ..., aₖ₋₁, y.
   ```

3. Thus `Fᵢ` drops `aᵢ` and inserts `y`.

4. All inserted applicants lie in `X`, hence in `X ∪ {x}`.

5. `y` is not used anywhere by `B`, since `y ∉ C(X ∪ {x})`.

6. For each `j` with `i < j < k`, applicant `aⱼ` is used by `B` at slot `sⱼ₊₁`, which lies inside the modified tail. Since `B` has no duplicate applicants, `aⱼ` is not used by `B` outside the modified tail.

7. The applicant `aₖ = y` is not used by `B` at all.

8. The inserted applicants are pairwise distinct, since they are distinct applicants used by `A` at distinct path slots.

9. Outside the modified tail, `Fᵢ` agrees with `B`.

10. `Fᵢ` assigns exactly the same set of slots as `B`, so any capacity-filling side condition is preserved.

Therefore `Fᵢ` is a valid competitor for the enlarged-pool optimum `B`.

### Inequality from optimality of `B`

Since `B` is optimal for `X ∪ {x}`,

```text
value(Fᵢ) ≤ value(B).
```

The assignments agree outside the tail `sᵢ₊₁, ..., sₖ`, so outside terms cancel. On that tail,

```text
value(Fᵢ on tail)
  = ∑_{j=i+1}^{k} w(aⱼ, sⱼ)
  = Qᵢ.
```

And

```text
value(B on tail)
  = ∑_{j=i}^{k-1} w(aⱼ, sⱼ₊₁)
  = Pᵢ.
```

Therefore

```text
Qᵢ ≤ Pᵢ.                                (2)
```

---

## 6. Cancellation

Combine (1) and (2):

```text
w(y, sᵢ) + Pᵢ ≤ w(aᵢ, sᵢ) + Qᵢ ≤ w(aᵢ, sᵢ) + Pᵢ.
```

Cancel `Pᵢ` from both sides:

```text
w(y, sᵢ) ≤ w(aᵢ, sᵢ).
```

This proves the main tail-dominance lemma.

No order-class argument is involved. Arbitrary cardinal weights on slots outside the common order class are absorbed into `Pᵢ` and `Qᵢ` and then canceled using the enlarged-pool inequality.

---

## 7. Local same-order kernel

The local kernel from the handoff is now immediate.

Assume:

```text
A(oldSlot) = z,
A(lost) = y,
oldSlot and lost have the same induced order,
w(z, oldSlot) < w(y, oldSlot).
```

Use the already-proved result that any old slot whose occupant is dominated by `y` at that slot lies on the fresh-to-lost path. Hence there is some `i < k` such that

```text
oldSlot = sᵢ,
z = aᵢ.
```

Apply the tail-dominance lemma at this `i`:

```text
w(y, oldSlot) ≤ w(z, oldSlot).
```

This contradicts

```text
w(z, oldSlot) < w(y, oldSlot).
```

Therefore the described loss of `y` is impossible.

Important: in this proof, the same-order assumption is used only to set up the intended local kernel and global injectivity theorem. Once the strict inequality `w(z, oldSlot) < w(y, oldSlot)` and the on-path reduction are available, the contradiction is purely cardinal.

---

## 8. Same-order borderline injectivity

Let `y,z ∈ V_C(X)` and suppose the selected old assignment `A` assigns

```text
A(s_y) = y,
A(s_z) = z,
```

with `s_y` and `s_z` inducing the same strict applicant order.

Assume for contradiction that `y ≠ z`. Since each slot has no ties, at slot `s_z` exactly one of the following holds.

### Case 1: `z` is below `y` at `s_z`

```text
w(z, s_z) < w(y, s_z).
```

Because `y ∈ V_C(X)`, choose a fresh applicant `x_y ∉ X` such that

```text
y ∉ C(X ∪ {x_y}).
```

By one-for-one exchange, `y` is the unique old applicant lost, so `z` remains chosen after inserting `x_y`. Apply the local kernel with:

```text
lost applicant = y,
lost slot      = s_y,
oldSlot        = s_z,
old occupant   = z.
```

The slots `s_y` and `s_z` have the same order, and `z` is below `y` at `s_z`, so the local kernel gives a contradiction.

### Case 2: `y` is below `z` at `s_z`

```text
w(y, s_z) < w(z, s_z).
```

Since `s_y` and `s_z` have the same induced order, transport this strict comparison to `s_y`:

```text
w(y, s_y) < w(z, s_y).
```

Because `z ∈ V_C(X)`, choose a fresh applicant `x_z ∉ X` such that

```text
z ∉ C(X ∪ {x_z}).
```

By one-for-one exchange, `z` is the unique old applicant lost, so `y` remains chosen after inserting `x_z`. Apply the local kernel with:

```text
lost applicant = z,
lost slot      = s_z,
oldSlot        = s_y,
old occupant   = y.
```

The slots `s_y` and `s_z` have the same order, and `y` is below `z` at `s_y`, so the local kernel gives a contradiction.

Both cases contradict `y ≠ z`. Therefore

```text
y = z.
```

So two distinct borderline applicants cannot be assigned to same-order slots in the selected assignment for `X`.

---

## 9. Global variability bound

For a fixed pool `X`, define a map from borderline applicants to slot-order classes:

```text
φ(y) = the order class of the slot assigned to y by A = select(X).
```

This is well-defined because every `y ∈ V_C(X)` is in `C(X)`, hence is assigned by `A`, and feasibility/no-duplicate assignment gives a unique assigned slot.

The same-order borderline injectivity result says exactly that `φ` is injective.

Therefore, for finite sets,

```text
|V_C(X)| ≤ number of slot-order classes.
```

This proves the LAP distinct-order variability bound.

---

## 10. Lean formalization plan

### 10.1. Avoid the re-entry lemma

The already-formalized leave-and-reenter statement is not needed for the final proof. It is enough to use:

1. exact one-for-one loss;
2. existence of the fresh-to-lost path;
3. dominated old slots lie on that path;
4. optimality of `A` and `B`.

The new target lemma should be the tail-dominance lemma:

```text
Along a fresh-to-lost path s₀,...,sₖ,
for every i < k,
  w y sᵢ ≤ w (A(sᵢ)) sᵢ.
```

### 10.2. Suggested theorem skeleton

The exact syntax depends on the existing assignment representation, but the statement should look like this:

```lean
/-- Along the fresh-to-lost alternating path, the lost applicant is not
better at any earlier path slot than that slot's old occupant. -/
theorem lost_weight_le_old_path_occupant
    {X : Finset Applicant} {x y : Applicant}
    {A B : Assignment Applicant Slot}
    {k : Nat} {s : Fin (k+1) → Slot}
    (hAopt : IsMaxWeightAssignment X A)
    (hBopt : IsMaxWeightAssignment (insert x X) B)
    (hNoDupPath : Function.Injective s)
    (hRoot : B (s 0) = some x)
    (hStep : ∀ j : Fin k,
      A (s j.castSucc) = B (s j.succ))
    (hLost : A (s (Fin.last k)) = some y)
    (hyLostNew : y ∉ chosen B)
    (hi : i < k) :
      w y (s ⟨i, Nat.lt_succ_of_lt hi⟩)
        ≤ w (oldOccupant A (s ⟨i, Nat.lt_succ_of_lt hi⟩))
            (s ⟨i, Nat.lt_succ_of_lt hi⟩) := by
  ...
```

This is only schematic. In the actual development, it may be easier to state the lemma for a `List Slot` path with `p.Nodup`, `p.get ⟨i, _⟩`, and `p.get ⟨i+1, _⟩`.

### 10.3. Use list suffixes if indices become painful

For a fixed `i`, let

```text
suffix = [sᵢ, sᵢ₊₁, ..., sₖ].
```

Then the two relevant quantities can be expressed without explicit interval sums:

```text
Pᵢ = sum over adjacent pairs (u,v) in suffix of w(A(u), v),
Qᵢ = sum over slots t in suffix.tail of w(A(t), t).
```

The old exchange inequality becomes:

```text
w(A(last suffix), first suffix) + Pᵢ
  ≤
w(A(first suffix), first suffix) + Qᵢ.
```

The new exchange inequality becomes:

```text
Qᵢ ≤ Pᵢ.
```

This list formulation may avoid many `Finset.Icc` arithmetic obligations.

### 10.4. Competitor assignment definitions

For fixed `i < k`, define the old-pool competitor:

```text
Eᵢ(t) =
  if t = sᵢ then A(sₖ)
  else if t = sⱼ for some i < j ≤ k then A(sⱼ₋₁)
  else A(t).
```

Define the enlarged-pool competitor:

```text
Fᵢ(t) =
  if t = sⱼ for some i < j ≤ k then A(sⱼ)
  else B(t).
```

For Lean, it is useful to package the uniqueness of the index `j` with the path `Nodup`/injectivity fact. Possible helper lemmas:

```lean
exists_unique_index_of_mem_path
exists_unique_index_of_mem_suffix
not_mem_outside_suffix_of_index_ne
```

If there is already an assignment-update operation over finite maps, define `Eᵢ` and `Fᵢ` by applying updates over the suffix in reverse order, then prove the update values by simp lemmas.

### 10.5. Feasibility helper lemmas

Prove two reusable helper lemmas.

#### Old rotation feasibility

```text
Rotating the applicants assigned by a feasible assignment A among a no-duplicate
finite set of assigned slots preserves feasibility and preserves the chosen set.
```

This directly handles `Eᵢ`, since it is just a cyclic rotation of `A` on the suffix.

#### New tail replacement feasibility

For `Fᵢ`, prove a tailored lemma:

```text
If B(sⱼ₊₁) = A(sⱼ) for i ≤ j < k,
A(sₖ) = y,
y is not assigned by B,
A has no duplicate applicants on the path,
B has no duplicate applicants,
and the path slots are no-duplicate,
then replacing B on sᵢ₊₁,...,sₖ by A on sᵢ₊₁,...,sₖ is feasible.
```

The key no-duplicate argument is:

- each inserted `A(sⱼ)` for `i < j < k` was previously used by `B` at `sⱼ₊₁`, inside the modified tail;
- `A(sₖ)=y` was not used by `B` at all;
- hence none of the inserted applicants appears outside the modified tail in `B`.

### 10.6. Value-cancellation helper lemma

It will likely help to prove a general lemma of the form:

```text
If assignments M and N agree outside a finite slot set T, then
value(M) - value(N)
equals the difference of their values restricted to T.
```

Over `Int`, this can be stated as an equality after moving terms:

```text
value(M) = valueOutside + valueOn(M,T)
value(N) = valueOutside + valueOn(N,T)
```

Then `linarith` can derive the desired inequalities.

For the old competitor use `T = {sᵢ, ..., sₖ}`.

For the new competitor use `T = {sᵢ₊₁, ..., sₖ}`.

### 10.7. Inequality lemmas to extract

Once feasibility is available, the two formal inequalities should be separated as named lemmas.

```lean
theorem old_suffix_exchange_ineq
  ... :
  w y sᵢ + Pᵢ ≤ w aᵢ sᵢ + Qᵢ := by
  -- define Eᵢ
  -- prove feasible Eᵢ for X
  -- apply optimality of A
  -- cancel outside suffix terms
```

```lean
theorem new_reverse_tail_exchange_ineq
  ... :
  Qᵢ ≤ Pᵢ := by
  -- define Fᵢ
  -- prove feasible Fᵢ for X ∪ {x}
  -- apply optimality of B
  -- cancel outside tail terms
```

Then the main lemma is a short arithmetic proof:

```lean
theorem lost_weight_le_old_path_occupant ... :
  w y sᵢ ≤ w aᵢ sᵢ := by
  have hOld := old_suffix_exchange_ineq ...
  have hNew := new_reverse_tail_exchange_ineq ...
  -- hOld : w y sᵢ + Pᵢ ≤ w aᵢ sᵢ + Qᵢ
  -- hNew : Qᵢ ≤ Pᵢ
  linarith
```

### 10.8. Local kernel theorem

After the tail lemma, the local kernel should be very small:

```lean
theorem not_lost_of_same_order_slotBelow
  (hOldSlotAssigned : A oldSlot = some z)
  (hLostAssigned : A lost = some y)
  (hSame : SameSlotOrder oldSlot lost)
  (hBelow : w z oldSlot < w y oldSlot)
  ... : False := by
  obtain ⟨i, hi, hsi⟩ := old_slot_mem_path_of_slotBelow ... hBelow
  have hdom := lost_weight_le_old_path_occupant ... hi
  -- rewrite hsi and hOldSlotAssigned into hdom
  linarith
```

The same-order hypothesis may not be used in the final arithmetic part, but it belongs in this theorem because this is the kernel needed by the global same-order injectivity proof.

### 10.9. Same-order borderline injectivity theorem

Use the local kernel twice, depending on the common order comparison.

```lean
theorem same_slot_order_borderline_injective
  (hy : y ∈ borderlineSet C X)
  (hz : z ∈ borderlineSet C X)
  (hAy : A sy = some y)
  (hAz : A sz = some z)
  (hSame : SameSlotOrder sy sz) :
  y = z := by
  by_contra hneq
  have hcomp : w z sz < w y sz ∨ w y sz < w z sz := by
    -- slot no-ties at sz, linear order
  cases hcomp with
  | inl hzBelowY =>
      obtain ⟨xy, hxyFresh, hyLost⟩ := hy
      exact local_kernel_for_loss_y xy ... sz sy hzBelowY
  | inr hyBelowZ_at_sz =>
      have hyBelowZ_at_sy : w y sy < w z sy := by
        -- If hSame : ∀ a b, w a sy < w b sy ↔ w a sz < w b sz,
        -- this is the right direction. Use `.mp` instead if the
        -- stored orientation is reversed.
        exact (hSame y z).mpr hyBelowZ_at_sz
      obtain ⟨xz, hxzFresh, hzLost⟩ := hz
      exact local_kernel_for_loss_z xz ... sy sz hyBelowZ_at_sy
```

Be careful with the direction of `SameSlotOrder`. If it is stated as

```lean
w a s < w b s ↔ w a t < w b t
```

then transport is just applying the iff in the appropriate direction.

### 10.10. Global theorem

Map each borderline applicant to the order class of its assigned slot under `A = select X`.

```text
φ(y) = orderClass(slotOfAssignedApplicant A y).
```

Then use `same_slot_order_borderline_injective` to prove `φ` injective.

If the existing bridge theorem

```lean
variabilityAtMost_choiceRuleOfAssignment_of_same_slot_order_borderline_injective
```

already packages this cardinal step, use it directly after proving the injectivity kernel.

---

## 11. Why this resolves the original hurdle

The original attempted proof used only the old-pool suffix exchange. That gave

```text
w(y, sᵢ) + Pᵢ ≤ w(aᵢ, sᵢ) + Qᵢ.
```

Alone, this does not imply `w(y,sᵢ) ≤ w(aᵢ,sᵢ)`, because the uncontrolled difference `Qᵢ - Pᵢ` may contain arbitrary cardinal weights from slots outside the common order class.

The missing observation is that optimality of the enlarged assignment `B` gives exactly

```text
Qᵢ ≤ Pᵢ.
```

So the uncontrolled terms have the right sign and cancel:

```text
w(y, sᵢ) + Pᵢ
  ≤ w(aᵢ, sᵢ) + Qᵢ
  ≤ w(aᵢ, sᵢ) + Pᵢ.
```

This is why arbitrary cardinal gaps outside the order class cannot create a counterexample to the local kernel.

---

## 12. Minimal final proof chain

The recommended formalization chain is:

```text
fresh-to-lost path facts
    ↓
old suffix competitor Eᵢ feasible for X
    ↓
old_suffix_exchange_ineq:
    w(y,sᵢ) + Pᵢ ≤ w(aᵢ,sᵢ) + Qᵢ
    ↓
new reverse-tail competitor Fᵢ feasible for X ∪ {x}
    ↓
new_reverse_tail_exchange_ineq:
    Qᵢ ≤ Pᵢ
    ↓
lost_weight_le_old_path_occupant:
    w(y,sᵢ) ≤ w(aᵢ,sᵢ)
    ↓
local same-order kernel
    ↓
same-order borderline injectivity
    ↓
|V_C(X)| ≤ number of slot-induced order classes
```

The most important lemma is `lost_weight_le_old_path_occupant`. Once that is formalized, the rest should be comparatively short.
