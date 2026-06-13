import TEMPLATE.MainTheorems

/-!
# Paper Assumptions: [Paper Title]

This file is the only paper-local place for assumptions that are not derived in
Lean. Keep it small. Each declaration must be explicitly stated by the paper,
listed in `status.json` `review_surface.assumption_names`, and judged in
`assumption_match_llm.json` as a true source/model assumption rather than a
proof convenience.

Use `-- audit-premise: <exact Lean binder>` comments to route hidden theorem
premises to an approved assumption declaration when the audit reports an exact
binder string.

## Paper Assumptions

- `assumption_source_model_conditions`: placeholder for a paper-stated model
  assumption. Delete this row if no assumption is needed.
-/

namespace TEMPLATE

/--
Paper model assumption / first source assumption.

Replace this placeholder with an assumption that is explicitly stated in the
paper. Do not use this file for proof conveniences or certificates derived in
the appendix.
-/
-- audit-premise: _h_source : assumption_source_model_conditions
abbrev assumption_source_model_conditions : Prop := True

end TEMPLATE
