# Final Validation Report: A No Free Lunch Theorem for Human-AI Collaboration

## 1. Human Verdict
- Lean formalization status: formalized
- Human dashboard review status: 0 reviewed, 0 stale, 0 mismatches
- Paper correctness verdict: main theorem proof checked; one minor source display uses loss notation while the surrounding text and proof use accuracy
- Qualitative proof verdict: source proof reproduced with finite calibrated settings and explicit mixtures
- Lean footprint: `PaperInterface.lean` has 71 lines and 6 paper-facing rows

## 2. Source and Scope
- Paper: *A No Free Lunch Theorem for Human-AI Collaboration*
- Authors: Kenny Peng, Nikhil Garg, Jon Kleinberg
- Source version: Proceedings of the AAAI Conference on Artificial Intelligence, 39(13), 14369-14376 (AAAI 2025)
- Lean folder: `papers/PKG25NoFreeLunch`
- Human-facing theorem file: `papers/PKG25NoFreeLunch/PaperInterface.lean`
- DAG artifacts: `papers/PKG25NoFreeLunch/DependencyDAG.tex`, `papers/PKG25NoFreeLunch/DependencyDAG.pdf`

## 3. What Has Been Proven
- The finite collaboration-setting model, calibration condition, deterministic strategies, source reliability, and non-collaboration definitions are formalized.
- The source linear-combination proposition is formalized as a disjoint-union mixture of finite calibrated settings.
- Proposition 1 is proved from the explicit counterexample setting for each failed deferral coordinate, then mixed across agents.
- Proposition 2 is proved from the source's two auxiliary finite settings. The "lambda close to 1" step is replaced by an explicit `7/8` and `1/8` mixture.
- The main theorem `theorem_main_no_free_lunch` proves that every reliable deterministic collaboration strategy is non-collaborative.

## 4. Paper Definitions Checked
- `definition_rounding_convention`: source rounding convention `round(1/2) = 1`.
- `definition_collaboration_strategy`: deterministic collaboration strategy from prediction profiles to labels.
- `definition_interior_prediction_profile`: source domain `(0,1)^n`.
- `definition_non_collaborative`: fixed agent off ties and fixed tie label on the half slice.
- `definition_reliable`: source reliability over all collaboration-setting accuracy surfaces.

## 5. Named Theorem Statements Checked
### Theorem 1
**Paper statement.** Every reliable collaboration strategy is non-collaborative.

**Lean interface statement.**
- `theorem_main_no_free_lunch`: for a nonempty finite agent set, `Reliable C -> NonCollaborative C`.

**Status.** formalized.

## 6. Paper-Facing Statement Validator Ledger
This table is one row per dashboard/PaperInterface row. Regenerate it with:

`python3 scripts/review_dashboard.py --paper PKG25NoFreeLunch --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Rounding convention | `definition_rounding_convention` | gpt-5-codex-subagent (model; matches; 2026-06-14T04:17:03Z) | Matches the paper's rounding convention `round(1/2)=1`. |
| Collaboration strategy | `definition_collaboration_strategy` | gpt-5-codex-subagent (model; matches; 2026-06-14T04:17:03Z) | Matches the paper's deterministic map `C : [0,1]^n -> {0,1}`. |
| Interior prediction profile | `definition_interior_prediction_profile` | gpt-5-codex-subagent (model; matches; 2026-06-14T04:17:03Z) | Matches the `(0,1)^n` source domain. |
| Non-collaboration | `definition_non_collaborative` | gpt-5-codex-subagent (model; matches; 2026-06-14T04:17:03Z) | Matches the fixed-agent and fixed-tie-label source definition. |
| Reliability | `definition_reliable` | gpt-5-codex-subagent (model; matches; 2026-06-14T04:17:03Z) | Matches source reliability over every collaboration setting. |
| Main theorem | `theorem_main_no_free_lunch` | gpt-5-codex-subagent (model; matches; 2026-06-14T04:17:03Z) | Matches the direction from reliable to non-collaborative; the nonempty-agent condition is source-implicit. |

Human dashboard reviews and model/agent statement checks may both appear here.
This table is provenance for the statement targets; it does not change the
human-only `human_review.reviewed_rows` counter.

## 7. Additional Assumptions Beyond Paper
- None beyond the source-implicit nonempty agent set and deterministic strategies.
- The exposed theorem uses source reliability over all collaboration-setting accuracy surfaces. The proof restricts that premise to the finite calibrated witness settings constructed in the source proof.

## 8. Proof-Strategy Deviations
- The source's "lambda sufficiently close to 1" phrase in Proposition 2 is replaced by an explicit `7/8` mixture weight. This is a proof-detail strengthening, not a caveat.
- The early source display `E |Yhat(X) - Y|` is treated as loss notation; the formalization follows the surrounding text and proof, which use accuracy as expected correctness.

## 9. Proof Tricks Worth Reusing
- Use a finite setting structure with explicit masses, label probabilities, and calibrated predictions.
- Prove zero-mass calibration cells by finite nonnegative sums, so calibration can be used unconditionally.
- Model mixtures as sigma/disjoint-union finite settings and prove strategy/agent accuracy linearity once.
- For no-free-lunch counterexamples, prove pointwise dominance plus one strict positive-mass point, then lift with `Finset.sum_lt_sum`.

## 10. Library Lift Pass
- Candidate reusable components: finite calibrated setting mixtures, finite event-mass scaling lemmas, and finite accuracy range lemmas.
- These currently live paper-locally because the API may need another paper before stabilizing.

## 11. DAG Audit
- Rendered artifact: `DependencyDAG.pdf` regenerated from `DependencyDAG.tex`
- Topology: source proof dependencies are reflected in `DependencyDAG.tex`
- Layout: visually inspected after regeneration; nodes and labels are readable without text collisions

## 12. Conditional Results and Remaining Gaps
- No Lean proof gaps remain for the source theorem.
- LLM statement validation is current for all six paper-facing rows. Human dashboard review remains 0/6.

## 13. Suspected Paper Errors or Inconsistencies
- Minor notation issue: the initial displayed formula for "accuracy" is written as absolute error/loss, while the later proof uses expected correctness. Lean follows expected correctness, which is the theorem's operative notion in the proof.

## 14. Validation Checks
- `lake build PKG25NoFreeLunch` passes.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex` passes.
- Lean axiom checks for `reliableFinite_exists_defers_away`, `reliableFinite_constant_on_half`, `main_no_free_lunch_finite`, `reliableFinite_of_reliable`, `main_no_free_lunch`, and `theorem_main_no_free_lunch` report only the ordinary Lean/Classical base axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `python3 scripts/review_dashboard.py --paper PKG25NoFreeLunch --statement-check` reports six current Lean-to-TeX drafts, six statement-judge rows, and no missing/stale/flagged items.

## 15. Final Verdict
- Completion status: formalized
- Summary: The main no-free-lunch theorem is proved from explicit finite calibrated collaboration settings, including the linear-combination construction, Proposition 1, Proposition 2, and the final non-collaboration conclusion.
