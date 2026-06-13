#!/usr/bin/env python3
"""Create the standard EconCSLib paper-formalization scaffold.

The script performs the deterministic intake step for a new source paper:
create the citation-specific folder, cache the source PDF when possible,
extract a text cache with `pdftotext` when available, and write the required
README/DAG/MainTheorems/PaperInterface/status/formalization-plan/.gitignore files.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import urllib.parse
import urllib.request
from datetime import date
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
FOLDER_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\d{2}[A-Z][A-Za-z0-9]*$")


def title_case_slug(text: str) -> str:
    parts = [part for part in re.split(r"[^A-Za-z0-9]+", text) if part]
    if not parts:
        return "Paper"
    return "".join(part[:1].upper() + part[1:] for part in parts)


def derive_folder(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    stem = Path(parsed.path).stem or parsed.netloc or "paper"
    stem = re.sub(r"^abs$", "", stem)
    slug = title_case_slug(stem)
    return f"Draft{date.today().year % 100:02d}{slug}"


def lean_namespace(folder: str) -> str:
    namespace = re.sub(r"[^A-Za-z0-9_]", "", folder)
    if not namespace or namespace[0].isdigit():
        namespace = f"Paper{namespace}"
    return namespace


def normalize_pdf_url(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    if parsed.netloc.endswith("arxiv.org"):
        if parsed.path.startswith("/abs/"):
            arxiv_id = parsed.path.removeprefix("/abs/")
            return urllib.parse.urlunparse(parsed._replace(path=f"/pdf/{arxiv_id}.pdf", query=""))
        if parsed.path.startswith("/pdf/") and not parsed.path.endswith(".pdf"):
            return urllib.parse.urlunparse(parsed._replace(path=f"{parsed.path}.pdf", query=""))
    return url


def write_file(path: Path, contents: str, force: bool) -> None:
    if path.exists() and not force:
        print(f"skip existing {path.relative_to(ROOT)}")
        return
    path.write_text(contents, encoding="utf-8")
    print(f"wrote {path.relative_to(ROOT)}")


def refresh_review_cache(folder: str) -> None:
    """Run the review metadata bootstrap for a fresh paper scaffold."""

    cmd = [
        "python3",
        str(ROOT / "scripts" / "review_dashboard.py"),
        "--paper",
        folder,
        "--refresh-cache",
    ]
    try:
        proc = subprocess.run(cmd, cwd=str(ROOT), check=False, capture_output=True, text=True)
    except OSError as exc:
        print(f"warning: could not refresh review cache for {folder}: {exc}")
        return
    if proc.returncode != 0:
        if proc.stdout:
            print(proc.stdout.strip())
        if proc.stderr:
            print(proc.stderr.strip())
        print(f"warning: review cache refresh failed for {folder}")


def download_pdf(url: str, target: Path, force: bool) -> bool:
    if target.exists() and not force:
        print(f"skip existing {target.relative_to(ROOT)}")
        return True
    try:
        request = urllib.request.Request(
            normalize_pdf_url(url),
            headers={"User-Agent": "EconCSLib paper intake"},
        )
        with urllib.request.urlopen(request, timeout=60) as response:
            data = response.read()
        target.write_bytes(data)
        print(f"downloaded {target.relative_to(ROOT)}")
        return True
    except Exception as exc:  # noqa: BLE001 - intake should report and continue
        print(f"warning: could not download PDF from {url}: {exc}", file=sys.stderr)
        return False


def extract_text(pdf: Path, txt: Path, force: bool) -> None:
    if txt.exists() and not force:
        print(f"skip existing {txt.relative_to(ROOT)}")
        return
    if not pdf.exists():
        print(f"warning: no PDF at {pdf.relative_to(ROOT)}; skipping text extraction", file=sys.stderr)
        return
    if shutil.which("pdftotext") is None:
        print("warning: `pdftotext` not found; skipping text extraction", file=sys.stderr)
        return
    subprocess.run(["pdftotext", str(pdf), str(txt)], cwd=ROOT, check=True)
    print(f"extracted {txt.relative_to(ROOT)}")


def readme_text(args: argparse.Namespace, folder: str) -> str:
    title = args.title or "[Paper Title]"
    authors = args.authors or "[Authors]"
    version = args.version or "[Conference/Journal/arXiv version]"
    official_url = args.official_url or args.url
    pdf_url = normalize_pdf_url(args.pdf_url or args.url)
    return f"""# {title}

## Source Version

- Paper: *{title}*
- Authors: {authors}
- Version formalized: {version}
- Official URL: {official_url}
- Public PDF: {pdf_url}

The PDF is cached locally as `source.pdf` and ignored by Git. The extracted text
cache is `source.txt` when `pdftotext` succeeds, and is also ignored by Git in
public workspaces unless redistribution rights have been checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `{folder}/MainTheorems.lean`
- Human-facing theorem file: `{folder}/PaperInterface.lean`
- Machine-readable status source: `{folder}/status.json`
- Outside-Lean proof plan: `{folder}/FORMALIZATION_PLAN.md`
- Final validation report: `{folder}/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `{folder}/DependencyDAG.tex`
- Rendered DAG: `{folder}/DependencyDAG.pdf`

`PaperInterface.lean` should be readable on its own: expose source formulas and
direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.
Keep the dashboard surface small: one row per paper-facing definition or named
result, not every helper theorem, certificate, or proof-route alias.

Use the controlled status vocabulary from `../../docs/STATUS.md`:
`formalized`, `formalized with caveat`, `partially formalized`, `conditional`,
`scaffold`, `not started`, and `not formalized`. Keep detailed caveats,
remaining certificates, or proof-route notes in the final column rather than in
the status cell.
Keep theorem/table content synchronized with `DependencyDAG.tex` node styles and
`MainTheorems.lean` declarations before marking a row `formalized`. Keep
`status.json` as the source of truth for review rows, artifact paths, and the
paper's top-level public status.

At the start of the paper, fill in the `FORMALIZATION_PLAN.md`
`Initial Outside-Lean Paper Audit` section before deep proof work. Read the
source, sanity-check every named result and formula-bearing displayed claim for
signs, constants, normalizations, quantifiers, domains, and dependencies, and
record suspected bugs, missing assumptions, formula ambiguities, and proof
strategy consequences. Alert the user early about any major issue. After that
source inventory and the first compact `PaperInterface.lean` skeleton exist,
run the smaller statement target-setting pass: populate `lean_to_tex_llm.json`,
populate `statement_match_llm.json`, and run
`python3 scripts/review_dashboard.py --paper {folder} --statement-precheck`.
Then run `python3 scripts/review_dashboard.py --paper {folder}
--assumption-precheck`: the statement judge is row-local and does not certify
that theorem premises are source assumptions or derived facts. Use this pass
only to correct theorem targets and premise provenance; do not update the DAG,
final validation report, human-review log, or review-surface audit just because
this early check ran.

At review boundaries, populate `lean_to_tex_llm.json` with context-free
Lean-to-TeX/prose translations generated from `PaperInterface.lean` alone. New
tracked entries should use `{{ "tex_statement": "...", "lean_statement_sha256":
"..." }}`. Then populate `statement_match_llm.json` with an independent
no-context judgment of whether each translation matches the original paper
statement, including Lean, paper, and TeX statement digests plus the judge
model/agent name, validator type, validation timestamp, and any validator
comment. If the judge flags a mismatch or uncertainty, iterate on the Lean
statement before treating it as the paper theorem target. Run
`python3 scripts/review_dashboard.py --paper {folder} --precheck` before
handoff so missing/stale statement-audit rows are explicit.
If any paper-facing theorem takes a hypothesis that is not proved from prior
Lean declarations, declare that hypothesis in `Assumptions.lean`, list it in
`status.json` `review_surface.assumption_names`, and populate
`assumption_match_llm.json` with an independent judgment that it is a true
paper/source model assumption rather than a proof shortcut.
The repository audit follows paper-local helper chains recursively: a theorem
is not closed if any helper it depends on still consumes an unvalidated
certificate, source-row equation, hidden hypothesis, or proof-boundary premise.
Do not use `axiom`, `constant`, `opaque`, or unsafe declarations to bypass that
provenance boundary.
If the dashboard has more than 30 rows, also populate `review_surface_llm.json`
with a no-paper-context LLM audit that checks whether every dashboard row is a
paper-facing definition, formula, or named statement. At 50 or more rows, treat
the dashboard as oversized and curate `PaperInterface.lean` or
`status.json.review_surface.include_names` before broad human review.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Main theorem(s) | `none` | not started | `none` | Extract named results from the local source text cache |

## Intake Checklist

- [ ] Confirm the official PDF URL, version, and bibliographic fields.
- [ ] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [ ] Fill in `FORMALIZATION_PLAN.md` with the initial outside-Lean paper audit,
      formula/result sanity check, proof strategy, and likely hard seams before
      deep Lean work.
- [ ] Run the lightweight statement target-setting pass and fix mismatched
      theorem targets before serious proof work.
- [ ] Run the assumption/hidden-premise precheck after the statement pass; do
      not treat row-local statement matches as globally certified targets until
      premise provenance also clears.
- [ ] Confirm `python3 scripts/audit_repository.py` reports no recursive
      paper-local hidden-premise dependency or axiom-like declaration for this
      paper.
- [ ] Populate `DependencyDAG.tex` with the same named-result inventory.
- [ ] Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`
      before updating any status row.
- [ ] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [ ] Route every non-derived paper-facing theorem premise through
      `Assumptions.lean`, then run the assumption-provenance LLM judge.
- [ ] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 50 or more rows, curate the interface before broad review.
- [ ] Run the context-free Lean-to-TeX translation and third-LLM match judgment
      workflow before asking for human dashboard review.
- [ ] Update `status.json`, then run `python3 scripts/sync_paper_status.py`.
- [ ] Rebuild `DependencyDAG.pdf` and verify visually after each significant edit.
"""


def status_text(args: argparse.Namespace, folder: str) -> str:
    title = args.title or "[Paper Title]"
    authors = args.authors or "[Authors]"
    version = args.version or "[Conference/Journal/arXiv version]"
    return json.dumps(
        {
            "schema": 1,
            "id": folder,
            "title": title,
            "authors": authors,
            "source_version": version,
            "build_target": f"lake build {folder}",
            "status": "not started",
            "main_caveat": "Replace with the public caveat or state that no caveat is known.",
            "human_summary": "Replace with a concise public-facing note; leave empty for formalized papers unless a source-version or proof-route note matters.",
            "human_summary_review": {
                "status": "draft",
                "note": (
                    "Set to human_approved only after a human has written or explicitly approved this "
                    "summary; do not rewrite a human_approved summary without explicit human instruction."
                ),
            },
            "review_entrypoint": f"papers/{folder}/FINAL_VALIDATION_REPORT.md",
            "human_review": {
                "reviewed_rows": 0,
                "total_rows": 0,
                "stale_rows": 0,
                "mismatch_rows": 0,
                "source": "paper-local status.json review_surface; human entries come from dashboard logs",
            },
            "paper_interface": {
                "path": f"papers/{folder}/PaperInterface.lean",
                "line_count": 0,
                "declaration_rows": 0,
                "review_rows": 0,
                "oversized": False,
                "maintainability_issue": None,
            },
            "artifacts": {
                "readme": f"papers/{folder}/README.md",
                "paper_interface": f"papers/{folder}/PaperInterface.lean",
                "assumptions": f"papers/{folder}/Assumptions.lean",
                "final_validation_report": f"papers/{folder}/FINAL_VALIDATION_REPORT.md",
                "dependency_dag_tex": f"papers/{folder}/DependencyDAG.tex",
                "dependency_dag_pdf": f"papers/{folder}/DependencyDAG.pdf",
            },
            "review_surface": {
                "source_file": f"papers/{folder}/PaperInterface.lean",
                "assumption_source_file": f"papers/{folder}/Assumptions.lean",
                "llm_statement_review": {
                    "lean_to_tex_file": f"papers/{folder}/lean_to_tex_llm.json",
                    "match_judgment_file": f"papers/{folder}/statement_match_llm.json",
                    "review_surface_audit_file": f"papers/{folder}/review_surface_llm.json",
                    "assumption_judgment_file": f"papers/{folder}/assumption_match_llm.json",
                    "surface_audit_threshold": 30,
                    "surface_warning_threshold": 50,
                    "policy": (
                        "Translate each Lean statement with an LLM that has no paper context; "
                        "have a third LLM compare that TeX/prose translation with the original "
                        "paper statement, record the model/agent validator metadata, and iterate "
                        "on PaperInterface.lean until they match. "
                        "If the dashboard has more than 30 rows, run a no-paper-context LLM "
                        "audit that checks whether every row is paper-facing; at 50 or more "
                        "rows, curate the surface before broad human review."
                    ),
                },
                "llm_assumption_review": {
                    "assumption_judgment_file": f"papers/{folder}/assumption_match_llm.json",
                    "policy": (
                        "Every paper-facing theorem premise not derived from prior Lean declarations "
                        "must be declared in Assumptions.lean, listed in assumption_names, "
                        "and judged by an independent LLM as a true paper/source model assumption rather "
                        "than a proof assumption."
                    ),
                },
                "assumption_policy": "strict",
                "assumption_names": [],
                "include_names": [],
                "slices": [
                    {
                        "id": "all",
                        "title": "All source-facing review rows",
                        "names": [],
                    }
                ],
            },
        },
        indent=2,
        ensure_ascii=False,
    ) + "\n"


def lean_to_tex_llm_text(folder: str) -> str:
    return json.dumps(
        {
            "schema": 1,
            "paper": folder,
            "items": {},
        },
        indent=2,
    ) + "\n"


def statement_match_llm_text(folder: str) -> str:
    return json.dumps(
        {
            "schema": 1,
            "paper": folder,
            "validator": "",
            "validator_type": "",
            "validated_at": "",
            "comment": "",
            "items": {
                "assumption_source_model_conditions": {
                    "judgment": "",
                    "reason": "",
                    "source_location": "",
                    "premise_judgments": {},
                }
            },
        },
        indent=2,
    ) + "\n"


def review_surface_llm_text(folder: str) -> str:
    return json.dumps(
        {
            "schema": 1,
            "paper": folder,
            "validator": "",
            "validator_type": "",
            "validated_at": "",
            "comment": "",
            "judgment": "",
            "reason": "",
            "review_rows": 0,
            "review_surface_sha256": "",
            "items": {},
        },
        indent=2,
    ) + "\n"


def assumption_match_llm_text(folder: str) -> str:
    return json.dumps(
        {
            "schema": 1,
            "paper": folder,
            "validator": "",
            "validator_type": "",
            "validated_at": "",
            "comment": "",
            "items": {},
        },
        indent=2,
    ) + "\n"


def dag_text() -> str:
    return r"""\documentclass[tikz,border=10pt]{standalone}
\input{../../docs/tikz/dag_preamble.tex}

\begin{document}

% Agent visual validation loop:
% 1. Compile this file to PDF after every substantive DAG edit.
% 2. Inspect the PDF or a rendered PNG, not just the TeX source.
% 3. Increase spacing or reroute arrows until no box, legend, note, edge, or label overlaps.
%
% Intended lifecycle:
% - During paper intake, replace the scaffold below with every named result in the
%   paper and the dependency arrows between them.
% - After intake, treat this as a stable topology: update node styles/status/text
%   as proofs close, but avoid adding boxes or arrows unless the original named
%   result inventory or dependency map was actually incomplete.
%
% Arrow direction rule:
% Draw edges from prerequisite/source node to dependent/target node.  The
% `dag_arrow` and `dag_dashed_arrow` styles use an explicit end-arrow (`->`),
% so the arrowhead should always land on the node that consumes the dependency.
% Do not reverse the coordinate order just to make routing easier; use anchors
% or an orthogonal route through empty space instead.

\begin{tikzpicture}[
  x=1cm,
  y=1cm,
  every node/.append style={outer sep=4pt}
]

\dagPaperMetadata{[Paper Title]}{[Authors]}{[Publication Venue]}{[Year]}{[Formalized PDF link]}

% --- Legend: README status vocabulary plus formalized node-type styles. ---
\dagPaperLegendRightOfMetadata{
\node[dag_result, dag_template_legend] (legRes) at (0,0) {formalized\\result};
\node[dag_lemma, dag_template_legend] (legLem) at (4.2,0) {formalized\\lemma};
\node[dag_model, dag_template_legend] (legDef) at (8.4,0) {formalized\\definition};
\node[dag_caveat_legend] (legCav) at (12.6,0) {formalized\\with caveat};
\node[dag_partial, dag_template_legend] (legPart) at (0,-2.6) {partially\\formalized};
\node[dag_conditional, dag_template_legend] (legCond) at (4.2,-2.6) {conditional};
\node[dag_scaffold, dag_template_legend] (legScaf) at (8.4,-2.6) {scaffold};
\node[dag_unformalized, dag_template_legend] (legNot) at (12.6,-2.6) {not started /\\not formalized};
}
\daglegend{(legRes)(legLem)(legDef)(legCav)(legPart)(legCond)(legScaf)(legNot)}{Legend}

\begin{dagPaperBody}

% --- Layout guidance for future agents. ---
\node[dag_template_note] (Guide) at (6.4,0) {
  Replace these scaffold nodes with the paper's named definitions, lemmas,
  propositions, theorems, and corollaries. Keep nodes on the grid below:
  columns are spaced by 6.4cm and rows by 3.2cm, which is wide enough for the
  default 5cm node text widths. Prefer straight or orthogonal arrows (`--`,
  `|-`, `-|`) and route through empty grid cells when a dependency skips a row.
  Draw from prerequisite to dependent result so the arrowhead points at the
  consumer.  For short horizontal gaps, use explicit anchors like `(A.east) --
  (B.west)` and increase spacing if the arrowhead visually merges with a node.
  After every layout change, render and inspect the PDF; if anything overlaps,
  increase row or column spacing before adding complicated curves. Once the
  initial named-result map is complete, prefer README-status style updates over
  adding new boxes or arrows.
};

% --- Non-overlapping proof graph scaffold. ---
% Status update pattern:
% - Change the leading style only, e.g. dag_unformalized -> dag_conditional ->
%   dag_lemma/dag_result, and update the short text if the remaining assumption changed.
% - Keep node names and arrows stable after the initial intake map is complete.
\node[dag_model] (Model) at (0,-4.2) {
  \textbf{Definitions / Model} \\
  Source primitives
};
\node[dag_lemma] (LemmaA) at (6.4,-4.2) {
  \textbf{Lemma A} \\
  First reusable step
};
\node[dag_lemma] (LemmaB) at (12.8,-4.2) {
  \textbf{Lemma B} \\
  Second reusable step
};

\node[dag_conditional] (Bridge) at (6.4,-7.4) {
  \textbf{Bridge Theorem} \\
  Conditional paper-facing reduction
};
\node[dag_unformalized] (Open) at (12.8,-7.4) {
  \textbf{Open Source Result} \\
  Name exact remaining gap
};

\node[dag_result] (Main) at (6.4,-10.6) {
  \textbf{Main Theorem} \\
  Closed paper-facing endpoint
};

\draw[dag_arrow] (Model) -- (LemmaA);
\draw[dag_arrow] (LemmaA) -- (LemmaB);
\draw[dag_arrow] (LemmaA) -- (Bridge);
\draw[dag_dashed_arrow] (LemmaB) -- (Open);
\draw[dag_arrow] (Bridge) -- (Main);
\draw[dag_dashed_arrow] (Open) |- (Main);
\end{dagPaperBody}
\end{tikzpicture}
\end{document}
"""


def main_theorems_text(title: str, namespace: str) -> str:
    display_title = title or "[Paper Title]"
    return f"""/-!
# Paper-Facing Theorems: {display_title}

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

## Main declarations

- `paperDefinition1`: placeholder for the first exact source definition.
- `paper_theorem_1`: placeholder for the first exact source theorem.
-/

namespace {namespace}

/-- Placeholder for the first exact source definition. Replace before claiming progress. -/
abbrev paperDefinition1 : Prop := True

/--
Replace before claiming progress: exact source formula row.

This row is complete only if the formula is derived from source primitives or
from separately validated paper assumptions; do not use it to assert an
unproved source-row equation.
-/
theorem paperTheoremPlaceholder : paperDefinition1 := by
  trivial

/-- Placeholder for the first exact source theorem. Replace before claiming progress. -/
theorem paper_theorem_1 : paperDefinition1 := by
  trivial

end {namespace}
"""


def assumption_source_text(title: str, folder: str, namespace: str) -> str:
    display_title = title or "[Paper Title]"
    return f"""import {folder}.MainTheorems

/-!
# Paper Assumptions: {display_title}

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

namespace {namespace}

/--
Paper model assumption / first source assumption.

Replace this placeholder with an assumption that is explicitly stated in the
paper. Do not use this file for proof conveniences or certificates derived in
the appendix.
-/
-- audit-premise: _h_source : assumption_source_model_conditions
abbrev assumption_source_model_conditions : Prop := True

end {namespace}
"""


def paper_interface_text(title: str, folder: str, namespace: str) -> str:
    display_title = title or "[Paper Title]"
    return f"""import {folder}.MainTheorems
import {folder}.Assumptions

/-!
# Human-Facing Paper Interface: {display_title}

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- Use short proofs that call into `MainTheorems.lean` or lower proof files.
- If implementation endpoints become broad or helper-heavy, move them to
  `ProofInterface.lean`; keep this filename as the single review surface.
- Keep exhaustive endpoint aliases and proof-seam checks in `PostPaperAudit.lean`,
  not here.

## Paper Definitions

- `paperDefinition1_formula`: placeholder for the first exact source formula.

## Named Results

- `paper_theorem_1_statement`: placeholder for the first exact source theorem.
-/

namespace {namespace}

/--
Definition 1 / first source object.

Replace this placeholder with the raw formula from the paper. A reviewer should
not need to open imported files to know what this object means.
-/
abbrev paperDefinition1_formula : Prop := True

/--
Theorem 1 / first named result.

Replace this placeholder with the exact source theorem statement, using the
visible paper-facing definitions and named paper assumptions imported from
`Assumptions.lean`.
-/
theorem paper_theorem_1_statement
    (_h_source : assumption_source_model_conditions) :
    paperDefinition1_formula := by
  simpa [paperDefinition1_formula] using paper_theorem_1

end {namespace}
"""


def gitignore_text() -> str:
    return """*.pdf
!DependencyDAG.pdf
*.aux
*.log
*.fls
*.fdb_latexmk
*.synctex.gz
"""


def review_launcher_text() -> str:
    return """#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)"
ROOT_DIR="$(cd \"${SCRIPT_DIR}/../..\" && pwd)"
PAPER_DIR=\"$(basename \"$SCRIPT_DIR\")\"

exec \"${ROOT_DIR}/scripts/launch_review_dashboard.sh\" --paper \"$PAPER_DIR\" \"$@\"
"""


def root_import_text(folder: str) -> str:
    return f"""import {folder}.PaperInterface
"""


def notes_text(title: str, namespace: str, args: argparse.Namespace) -> str:
    official_url = args.official_url or args.url
    title_text = title or "[Paper Title]"
    return f"""# {title_text} Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `{namespace}`
- Official URL: {official_url}
- Source PDF: `source.pdf`
- Local source text cache, if generated: `source.txt` (ignored by Git in public workspaces)

## Formalization checklist

- [ ] Full named-result inventory copied to the README theorem table.
- [ ] DAG graph includes all required paper-stage nodes and dependencies.
- [ ] README status and remaining-assumption notes match proof artifacts.
- [ ] Post-formalization library elevation pass completed: reusable proof
      results, techniques, and primitives were moved into `EconCSLib` when
      local/low-risk, or recorded with destination modules in the final report.
- [ ] Final status review completed before publishing.

## Notes

- Date reviewed:
- Last theorem row formalized:
- Outstanding assumptions / caveats:
- Reusable library elevation candidates:

"""


def formalization_plan_text(title: str, namespace: str) -> str:
    title_text = title or "[Paper Title]"
    return f"""# Formalization Plan: {title_text}

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report.

- Namespace: `{namespace}`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected:
- Formula sanity check:
  - Signs, constants, normalizations, quantifiers, domains:
  - Formula-bearing displayed claims that need derivation, not source-row assumptions:
- Named result sanity check:
  - Results that look correct as stated:
  - Suspected bugs, missing assumptions, or ambiguous wording:
- Proof strategy consequences:
  - Source proof route to follow:
  - Cleaner Lean route or reusable library route:
  - Major issues already reported to the user:

## Source Inventory

- Definitions / formatted paper objects:
- Named lemmas / propositions / theorems / corollaries:
- Theorem-like displayed claims that are used later:

## Initial Proof Strategy

- Main theorem chain:
- Likely reusable `EconCSLib` seams:
- Paper steps that look underspecified or analytically hard:
- Planned fallback route if the source proof is too informal:

## Active Scratchpad

- Current Lean endpoint:
- Exact current mathematical gap:
- Next bridge lemmas to try:
- Informal proof sketch / recurrence / construction:

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
- Genuine paper assumptions to declare in `Assumptions.lean`:
- Temporary certificate fields to discharge:
"""


def final_validation_report_text(title: str, folder: str) -> str:
    title_text = title or "[Paper Short Name]"
    return f"""# Final Validation Report: {title_text}

## 1. Human Verdict
- Lean formalization status: not started
- Human dashboard review status: 0 reviewed, 0 stale, 0 mismatches
- Paper correctness verdict: not assessed
- Qualitative proof verdict: not assessed
- Lean footprint: not measured

## 2. Source and Scope
- Paper: <title>
- Source version: <arXiv/publisher URL + version/date>
- Lean folder: `papers/{folder}`
- Human-facing theorem file: `papers/{folder}/PaperInterface.lean`
- Paper assumption file: `papers/{folder}/Assumptions.lean`
- DAG artifacts: `papers/{folder}/DependencyDAG.tex`, `papers/{folder}/DependencyDAG.pdf`

## 3. What Has Been Proven
None yet.

## 4. Paper Assumption Provenance
Every paper-facing theorem premise that is not derived in Lean should appear as
a named assumption declaration in `Assumptions.lean`, be listed in `status.json`
`review_surface.assumption_names`, and be checked in `assumption_match_llm.json`
as a true paper/source model assumption.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper assumptions recorded yet. |

## 5. Additional Assumptions Beyond Paper
- None

## 6. Proof-Strategy Deviations
- None

## 7. Proof Tricks Worth Reusing
- None

## 8. Library Lift Pass
- Reusable library extraction candidates: None
- Library certificate/source-boundary audit: not run. Before a completion
  claim, run `python3 scripts/audit_repository.py --library-only --library-premise-audit` and
  confirm any certificate-taking library APIs used by paper wrappers are
  constructed internally, validated as paper assumptions, or listed as partial
  boundaries. This audit follows transitive helper chains, not only direct
  aliases.
- Paper-local hidden-premise audit: not run. The default repository audit should
  report no reviewed row that recursively depends on a local helper with an
  unvalidated certificate, source-row equation, hidden hypothesis, or other
  proof-boundary premise.

## 9. DAG Audit
- Rendered artifact: not checked
- Topology: not checked
- Layout: not checked

## 10. Conditional Results and Remaining Gaps
- All named results remain open.

## 11. Suspected Paper Errors or Inconsistencies
- None

## 12. Validation Checks
- Not run.
- Required closeout checks include targeted Lean build, statement precheck,
  assumption/hidden-premise precheck, repository audit, and library premise
  audit when reusable certificate APIs are used or when preparing a public PR.
  The repository audit must also be clean of axiom-like declarations.

## 13. Final Verdict
- Completion status: not formalized
- Summary: Scaffold only.

## 14. Paper Definitions Checked
- None yet.

## 15. Named Theorem Statements Checked
### Theorem <n>
**Paper statement.** <one theorem-box-level statement matching the source>

**Lean interface statement.**
- `<PaperInterface.theoremN_part>`: <which paper clause it states>

**Status.** not formalized.

## 16. Paper-Facing Statement Validator Ledger
This table is one row per dashboard/PaperInterface row. Regenerate it with:

`python3 scripts/review_dashboard.py --paper {folder} --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| <paper item label> | `<PaperInterface.declaration>` | <human/model/agent validators, judgments, dates, stale flags> | <validator comments or `None`> |

Human dashboard reviews and model/agent statement checks may both appear here.
This table is provenance for the statement targets; it does not change the
human-only `human_review.reviewed_rows` counter.
"""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("url", help="paper URL; arXiv abs URLs are converted to PDF URLs")
    parser.add_argument("--folder", help="citation-style folder name, e.g. DSWG24DiscretizationBias")
    parser.add_argument("--title", help="paper title for README and theorem ledger")
    parser.add_argument("--authors", help="paper authors for README")
    parser.add_argument("--version", help="source version, conference, journal, or arXiv version")
    parser.add_argument("--official-url", help="canonical paper URL if different from input URL")
    parser.add_argument("--pdf-url", help="direct PDF URL if different from input URL")
    parser.add_argument("--namespace", help="Lean namespace; defaults to sanitized folder name")
    parser.add_argument("--no-download", action="store_true", help="scaffold files without downloading the PDF")
    parser.add_argument("--force", action="store_true", help="overwrite existing scaffold files")
    parser.add_argument("--with-notes", action="store_true", help="generate PAPER_NOTES.md handoff checklist")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    folder = args.folder or derive_folder(args.url)
    namespace = args.namespace or lean_namespace(folder)

    if not FOLDER_RE.fullmatch(folder):
        print(
            f"warning: `{folder}` does not match [AuthorInitials][2DigitYear][Descriptor]; "
            "rename after citation intake",
            file=sys.stderr,
        )

    paper_dir = PAPERS / folder
    paper_dir.mkdir(parents=True, exist_ok=True)

    pdf = paper_dir / "source.pdf"
    txt = paper_dir / "source.txt"

    write_file(paper_dir / ".gitignore", gitignore_text(), args.force)
    write_file(paper_dir / "README.md", readme_text(args, folder), args.force)
    write_file(paper_dir / "status.json", status_text(args, folder), args.force)
    write_file(paper_dir / "lean_to_tex_llm.json", lean_to_tex_llm_text(folder), args.force)
    write_file(paper_dir / "statement_match_llm.json", statement_match_llm_text(folder), args.force)
    write_file(paper_dir / "review_surface_llm.json", review_surface_llm_text(folder), args.force)
    write_file(paper_dir / "assumption_match_llm.json", assumption_match_llm_text(folder), args.force)
    launch_script = paper_dir / "review-dashboard.sh"
    write_file(
        launch_script,
        review_launcher_text(),
        args.force,
    )
    launch_script.chmod(0o755)
    write_file(
        paper_dir / "FORMALIZATION_PLAN.md",
        formalization_plan_text(args.title or "", namespace),
        args.force,
    )
    write_file(
        paper_dir / "FINAL_VALIDATION_REPORT.md",
        final_validation_report_text(args.title or "", folder),
        args.force,
    )
    write_file(paper_dir / "DependencyDAG.tex", dag_text(), args.force)
    write_file(paper_dir / "MainTheorems.lean", main_theorems_text(args.title or "", namespace), args.force)
    write_file(
        paper_dir / "Assumptions.lean",
        assumption_source_text(args.title or "", folder, namespace),
        args.force,
    )
    write_file(
        paper_dir / "PaperInterface.lean",
        paper_interface_text(args.title or "", folder, namespace),
        args.force,
    )
    write_file(PAPERS / f"{folder}.lean", root_import_text(folder), args.force)
    if args.with_notes:
        write_file(
            paper_dir / "PAPER_NOTES.md",
            notes_text(args.title or "", namespace, args),
            args.force,
        )

    if not args.no_download:
        downloaded = download_pdf(args.pdf_url or args.url, pdf, args.force)
        if downloaded:
            extract_text(pdf, txt, args.force)
    else:
        print("skipped PDF download")

    refresh_review_cache(folder)

    print(f"paper scaffold ready: {paper_dir.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
