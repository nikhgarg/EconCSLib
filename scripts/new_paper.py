#!/usr/bin/env python3
"""Create the standard EconCSLib paper-formalization scaffold.

The script performs the deterministic intake step for a new source paper:
create the citation-specific folder, cache the source PDF when possible,
extract a text cache with `pdftotext` when available, and write the required
README/DAG/MainTheorems/PaperInterface/formalization-plan/.gitignore files.
"""

from __future__ import annotations

import argparse
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
cache is `source.txt` when `pdftotext` succeeds and licensing permits tracking
the text.

## Paper-Facing Ledger

- Implementation theorem file: `{folder}/MainTheorems.lean`
- Human-facing theorem file: `{folder}/PaperInterface.lean`
- Outside-Lean proof plan: `{folder}/FORMALIZATION_PLAN.md`
- Dependency DAG: `{folder}/DependencyDAG.tex`
- Rendered DAG: `{folder}/DependencyDAG.pdf` when generated locally

`PaperInterface.lean` should be readable on its own: expose source formulas and
direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.

Use the controlled status vocabulary from `../../docs/STATUS.md`:
`formalized`, `formalized with caveat`, `partially formalized`, `conditional`,
`scaffold`, `not started`, and `not formalized`. Keep detailed caveats,
remaining certificates, or proof-route notes in the final column rather than in
the status cell.
Keep theorem/table content synchronized with `DependencyDAG.tex` node styles and
`MainTheorems.lean` declarations before marking a row `formalized`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Main theorem(s) | `none` | not started | `none` | Extract named results from `source.txt` |

## Intake Checklist

- [ ] Confirm the official PDF URL, version, and bibliographic fields.
- [ ] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [ ] Fill in `FORMALIZATION_PLAN.md` with the initial proof strategy and
      likely hard seams before deep Lean work.
- [ ] Populate `DependencyDAG.tex` with the same named-result inventory.
- [ ] Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`
      before updating any status row.
- [ ] Rebuild `DependencyDAG.pdf` and verify visually after each significant edit.
"""


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

This file is the human-facing Lean ledger for the source paper. Keep
source-faithful definitions and theorem wrappers here, in paper order.

## Main declarations

- `paperDefinition1`: placeholder for the first exact source definition.
- `paper_theorem_1`: placeholder for the first exact source theorem.
-/

namespace {namespace}

/-- Placeholder for the first exact source definition. Replace before claiming progress. -/
abbrev paperDefinition1 : Prop := True

/-- Replace before claiming progress: explicit source formula wrapper. -/
theorem paperTheoremPlaceholder : paperDefinition1 := by
  trivial

/-- Placeholder for the first exact source theorem. Replace before claiming progress. -/
theorem paper_theorem_1 : paperDefinition1 := by
  trivial

end {namespace}
"""


def paper_interface_text(title: str, folder: str, namespace: str) -> str:
    display_title = title or "[Paper Title]"
    return f"""import {folder}.MainTheorems

/-!
# Human-Facing Paper Interface: {display_title}

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- Then state the named results directly, with assumptions visible in each
  theorem signature.
- Use short proofs that call into `MainTheorems.lean` or lower proof files.
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
visible paper-facing definitions above.
-/
theorem paper_theorem_1_statement : paperDefinition1_formula := by
  simpa [paperDefinition1_formula] using paper_theorem_1

end {namespace}
"""


def gitignore_text() -> str:
    return """*.pdf
*.aux
*.log
*.fls
*.fdb_latexmk
*.synctex.gz
"""


def root_import_text(folder: str) -> str:
    return f"""import {folder}.PaperInterface
"""


def notes_text(title: str, namespace: str, args: argparse.Namespace) -> str:
    official_url = args.official_url or args.url
    title_text = title or "[Paper Title]"
    return f"""# {title_text} Verification Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `{namespace}`
- Official URL: {official_url}
- Source PDF: `source.pdf`
- Source text cache: `source.txt`

## Verification checklist

- [ ] Full named-result inventory copied to the README theorem table.
- [ ] DAG graph includes all required paper-stage nodes and dependencies.
- [ ] README status and remaining-assumption notes match proof artifacts.
- [ ] Final status review completed before publishing.

## Notes

- Date reviewed:
- Last theorem row verified:
- Outstanding assumptions / caveats:

"""


def formalization_plan_text(title: str, namespace: str) -> str:
    title_text = title or "[Paper Title]"
    return f"""# Formalization Plan: {title_text}

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report.

- Namespace: `{namespace}`

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
- Genuine paper assumptions:
- Temporary certificate fields to discharge:
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
    write_file(
        paper_dir / "FORMALIZATION_PLAN.md",
        formalization_plan_text(args.title or "", namespace),
        args.force,
    )
    write_file(paper_dir / "DependencyDAG.tex", dag_text(), args.force)
    write_file(paper_dir / "MainTheorems.lean", main_theorems_text(args.title or "", namespace), args.force)
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

    print(f"paper scaffold ready: {paper_dir.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
