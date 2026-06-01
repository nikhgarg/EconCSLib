# Singleton Allowed-Sample Fiber Sketch

Goal: remove the last certificate in
`im05_integerMultisetPermutation_conditional_finite_law_one_of_allowedSample_constant_fiber`
by proving that, for fixed `excluded`, every residual word outside
`{excluded}` has the same number of preimages under
`im05_integerMultisetPermutationAllowedSample {excluded}`.

Status: completed in Lean.  The final named declarations are:

- `im05_integerMultisetPermutationAllowedSampleSingletonFiberEquiv`
- `im05_integerMultisetPermutationAllowedSample_singleton_fiber_card`
- `im05_integerMultisetPermutationAllowedSample_singleton_fiber_card_pos`
- `im05_integerMultisetPermutation_conditional_finite_law_one`

For a count vector `count`, write:

- `m = count excluded`
- `r = ∑ name, im05_countOutside count {excluded} name`
- `T = ∑ name, count name = r + m`

For any residual sample `ρ : im05_integerMultisetPermutationSample Name
(im05_countOutside count {excluded})`, a preimage is determined exactly by the
set `S : Finset (Fin T)` of the `m` slots occupied by `excluded`.  The inverse
word fills every slot in `S` with `excluded` and fills the complement slots,
in increasing order, with the entries of `ρ`.

Implemented Lean route:

1. Added small total-count lemmas for singleton deletion:
   `sum_countOutside_singleton_add_count` and its cast/cast-symmetry variants.
2. Defined an order-preserving embedding from `Fin r` into the complement of
   `S` using `Finset.orderEmbOfFin` on `(Finset.univ.erase? or filter not-in S)`.
   Prefer `((Finset.univ : Finset (Fin T)).filter fun slot => slot ∉ S)`.
3. Defined the inverse reconstruction word from `(S, S.card = m)` and residual
   `ρ`.
4. Proved its counts:
   - `excluded` count is `S.card = m`;
   - every non-excluded name count is the residual count, because the
     complement positions are exactly enumerated by `orderEmbOfFin`.
5. Proved filtering the reconstructed word outside `{excluded}` returns `ρ`;
   this is the hard order-preservation lemma.
6. Proved the forward map from a fiber sample to its excluded-slot set and show
   the two maps are inverse.  The fiber cardinality is
   `((Finset.univ : Finset (Fin T)).powersetCard m).card`, independent of `ρ`.

The fallback bijection-between-fibers route was not needed.  The implemented
equivalence computes the common fiber cardinality directly as the number of
slot sets of size `count excluded`.
