# Source-Transformation Strategy Notes

These are scratch notes for the Theorem 1(iii) source-route seam.

The paper's informal step says the balancing partition exists because the
feature distribution is continuous and an expanding set changes the two
integrals continuously.  In Lean, this needs a concrete expanding family.

The accepted formal route avoids an arbitrary abstract nonatomic-set splitting
theorem.  On a real feature coordinate, the right construction is:

1. Work inside a bounded interval `[lo, hi]` and a measurable source set `S`.
2. Use the ordered sweep `S ∩ (lo, cut]` versus `S ∩ (cut, hi]`.
3. Apply the existing interval intermediate-value lemma to the indicator
   weights `1_S * leftWeight` and `1_S * rightWeight`.
4. For `S_b`, use `leftWeight = q_z - u` and `rightWeight = 1 - q_z`.
5. For `S_d`, use `leftWeight = q_z` and `rightWeight = u - q_z`.

This closes the paper's "expanding set" argument for arbitrary measurable
subsets of a real interval, not only for the whole interval.  It does not yet
give an abstract standard-Borel nonatomic transport theorem, but it is the
natural faithful version of the proof after the paper's "add a continuous
feature dimension" reduction.

Lean progress so far:

- The subset sweep cut now exists for arbitrary measurable `S` inside
  `[lo, hi]`.
- The cut has been pushed through feature-marginal focal score-mass
  preservation.
- The corresponding product-measure balance equations are formalized.
- Classical and measurable finite-label nonfocal selectors are available on
  the swept subregions.
- The aggregate two-coordinate MAE-delta endpoints are formalized for subset
  sweeps, including measurable-selector versions that discharge finite-law
  integrability obligations.
- The same subset sweep now reaches the supplied-`qNext` two-region endpoints:
  if a transformed posterior has the claimed shape on the swept pieces and is
  unchanged outside them, the integrated MAE delta is nonpositive.
- For supplied shaped `qNext`, the subset sweep also preserves focal
  score-mass and hence preserves the continuous aggregate posterior for the
  focal label, assuming outside equality and posterior-simplex bounds.
- Fully constructive subset-sweep `S_b` and `S_d` MAE endpoints now choose the
  cut, a measurable feature-level nonfocal selector, and the piecewise
  transformed posterior `qNext`.
- The non-collapse constructive subset `S_b` and `S_d` endpoints have been
  strengthened to measurable simplex-valued `qNext` certificates under the
  same feasibility/threshold conditions as the whole-interval route.
- The multiclass-safe collapse variants have now been lifted to arbitrary
  measurable subset sweeps for both `S_b` and `S_d`.  These endpoints construct
  measurable simplex-valued `qNext`, preserve focal aggregate posterior mass,
  and prove nonpositive integrated MAE delta without the non-collapse
  feasibility or threshold hypotheses.
- The reduced uniform-middle shape layer now has subset-sweep collapse
  combiners and terminal point-shape facts, plus shape congruence lemmas for
  transferring reduced-shape certificates across coordinatewise posterior
  equalities.
- The accepted formal version of the paper's continuous expansion is now the
  real-coordinate subset sweep.  For general feature spaces, Lean has reusable
  coordinate bridges: integrals over coordinate preimages transfer to the
  pushed-forward coordinate law, finite product laws have finite coordinate
  interval mass, and measurable embeddings preserve nonatomicity of the feature
  marginal after pushforward.
- The coordinate-sweep `S_b` and `S_d` score-mass preservation statements are
  formalized for a measurable real coordinate `r : X -> R` whenever the focal
  score factors through that coordinate.  This is weaker than a fully abstract
  arbitrary nonatomic transport theorem, but it is a precise implementation of
  the paper's vague "expand a set continuously" step.
- The coordinate route has now been lifted from score-mass preservation to
  constructive `S_b` and `S_d` source transformations: push the joint law
  through `(x, y) -> (r x, y)`, apply the real-line collapse endpoint, and
  pull the constructed `qNext` back to the original feature space.  These
  coordinate-pullback endpoints construct measurable simplex-valued posteriors,
  preserve the focal aggregate posterior, and prove nonpositive integrated
  MAE delta on the original joint law.

Future improvement: replace the coordinate hypothesis by a fully abstract
nonatomic transport/sweep wrapper.  The final report should record that the
current source-route formalization intentionally uses the easier real-coordinate
version, now with full coordinate-pullback `qNext` endpoints; the direct
Theorem 1(iii) calibration proof is not affected by this auxiliary-route
limitation.
