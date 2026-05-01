# Paper README Status Vocabulary

Paper-local theorem ledgers use a controlled status vocabulary. Keep nuance in
the `Remaining assumptions / notes` cell, not in the `Status` cell.

Allowed paper-row statuses:

- `formalized`: The listed Lean declaration(s) close the intended paper item.
  The remaining-assumptions cell must be `None` or start with `None;` followed
  only by notes about paper assumptions already encoded in the declarations.
  DAG style: use `dag_result` for theorem/proposition/corollary nodes,
  `dag_lemma` for lemma/support nodes, and `dag_model` for definition/model
  nodes.
- `formalized with caveat`: Lean closes a precise variant of the paper item,
  but the row needs a documented caveat such as a corrected statement, finite
  model restriction, proof-strategy deviation, or source mismatch. DAG style:
  `dag_caveat`.
- `partially formalized`: Substantial definitions, helper lemmas, or finite
  analogues are formalized, but the full source item is not closed. DAG style:
  `dag_partial`.
- `conditional`: A paper-facing statement or reduction is proved only under an
  explicit extra certificate, bridge theorem, or hypothesis not yet discharged.
  DAG style: `dag_conditional`.
- `scaffold`: Names, interfaces, or theorem shells exist, but no substantive
  source proof has been closed. DAG style: `dag_scaffold`.
- `not started`: No meaningful Lean artifact exists yet for the paper item.
  DAG style: `dag_unformalized`.
- `not formalized`: The item is intentionally not represented one-for-one, is
  out of scope, or is superseded by another formalized route. DAG style:
  `dag_unformalized`.

For every status other than `formalized`, the final column should state the
exact caveat, closed sub-result, remaining certificate, or reason for deferral.

The dependency DAG legend should expose this same vocabulary. For a formalized
node, the color additionally records the paper-object type: green for
theorems/results, yellow for lemmas/support, and blue for definitions/models.
For non-fully-closed statuses, the style records the status directly.
