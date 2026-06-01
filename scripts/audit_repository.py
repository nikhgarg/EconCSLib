#!/usr/bin/env python3
"""Repository hygiene audit for EconCSLib.

The checks here are intentionally mechanical. They are meant to catch stale
paper-folder structure, hidden Lean proof placeholders, noisy `#check` ledgers,
and obvious README status-table overclaims. Semantic theorem fidelity still
requires the paper-by-paper PDF/DAG audit.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
PUBLIC_RELEASE = (ROOT / "docs" / "PAPER_STATUS.md").exists()
ACTIVE_PAPERS: set[str] = set()
REQUIRED_PAPER_FILES = {
    ".gitignore",
    "DependencyDAG.tex",
    "FORMALIZATION_PLAN.md",
    "MainTheorems.lean",
    "PaperInterface.lean",
    "README.md",
}
REQUIRED_GITIGNORE_PATTERNS = {
    "*.pdf",
    "*.aux",
    "*.log",
    "*.fls",
    "*.fdb_latexmk",
    "*.synctex.gz",
}
REVIEW_LAUNCHER_NAME = "review-dashboard.sh"
REVIEW_LAUNCHER_TARGET = "scripts/launch_review_dashboard.sh"
REVIEW_TRACE_CACHE = ".review_traces/paper_interface_cache.json"
REVIEW_SLICES_NAME = "review_slices.json"
REVIEW_ROW_WARN_THRESHOLD = 80
ROOT_STATUS_VALUES = {
    "Formalized",
    "Formalized with caveat",
    "Formalized with documented caveat",
    "Main endpoints formalized",
    "Main endpoints formalized with documented deviations",
    "Partially formalized",
    "Not formalized",
    "Active validation",
}
ROOT_INTERFACE_REQUIRED_STATUSES = {
    "Formalized",
    "Formalized with caveat",
    "Formalized with documented caveat",
    "Main endpoints formalized",
    "Main endpoints formalized with documented deviations",
}
FORBIDDEN_STATUS_LABEL_RE = re.compile(
    r"\bverified in Lean(?: with source OCR caveat)?\b|"
    r"\bVerified in Lean(?: with source OCR caveat)?\b|"
    r"\bVerified with OCR caveat\b|"
    r"\bVerified with caveat\b|"
    r"\b[Cc]urrent verification status\b|"
    r"\b[Vv]erification status\b|"
    r"<td>\s*Verified\s*</td>|"
    r"\|\s*Verified\s*\|"
)
PAPER_STATUS_VALUES = {
    "formalized",
    "formalized with caveat",
    "partially formalized",
    "conditional",
    "scaffold",
    "not started",
    "not formalized",
}
DAG_REQUIRED_PREAMBLE = "docs/tikz/dag_preamble.tex"
DAG_STATUS_STYLES = {
    "dag_result",
    "dag_lemma",
    "dag_model",
    "dag_caveat",
    "dag_partial",
    "dag_conditional",
    "dag_scaffold",
    "dag_unformalized",
}
PAPER_FOLDER_NAME_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\d{2}[A-Z][A-Za-z0-9]*$")
LEAN_DECL_RE = re.compile(r"^\s*(?:theorem|lemma|def|abbrev|structure|class|inductive|export)\s+", re.M)
REVIEW_DECL_RE = re.compile(
    r"^\s*(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
    re.M,
)
LEDGER_PLACEHOLDER_RE = re.compile(
    r"\[Paper Title\]|\bnamespace TEMPLATE\b|\bpaperDefinition1\b|\bpaper_theorem_1\b|Replace before claiming progress",
)
PROOF_FACING_AUDIT_FORMULA_RE = re.compile(
    r"/--(?:(?!-/).)*\bformula\b(?:(?!-/).)*-/\s*noncomputable\s+abbrev\s+audit[A-Za-z0-9_]*",
    re.I | re.S,
)
INTERFACE_WITNESS_RE = re.compile(
    r"^\s*(?:theorem|lemma|def|abbrev)\s+[A-Za-z0-9_]*(?:tuple|prod|pprod)[A-Za-z0-9_]*witness[A-Za-z0-9_]*\b|"
    r"^\s*(?:theorem|lemma|def|abbrev)\s+[A-Za-z0-9_]*witness[A-Za-z0-9_]*(?:tuple|prod|pprod)[A-Za-z0-9_]*\b",
    re.I | re.M,
)
README_AGENT_DETAIL_RE = re.compile(
    r"Get context on this repo|source inventory first|FORMALIZATION_PLAN\.md|"
    r"PostPaperAudit\.lean|pdftotext|econcs-formalizer/SKILL\.md|"
    r"DependencyDAG\.tex|MainTheorems\.lean",
    re.I,
)
README_OLD_STATUS_TABLE_RE = re.compile(
    r"^\|\s*Paper folder\s*\|\s*Paper\s*\|\s*Overall status\s*\|",
    re.M,
)
README_STATUS_DETAIL_RE = re.compile(
    r"Current Lean surface|Lean declaration|PostPaperAudit\.lean|"
    r"DependencyDAG\.tex|MainTheorems\.lean",
    re.I,
)
README_STATUS_HEADER = ["Paper", "Status", "Human summary"]
README_MAX_STATUS_ROWS = 20
README_MAX_STATUS_SUMMARY_CHARS = 180
README_MAX_LINES = 140


@dataclass(frozen=True)
class Finding:
    severity: str
    path: Path
    message: str

    def format(self) -> str:
        rel = self.path.relative_to(ROOT) if self.path.is_absolute() else self.path
        return f"[{self.severity}] {rel}: {self.message}"


def lean_files(include_active: bool) -> list[Path]:
    roots = [ROOT / "EconCSLib", PAPERS]
    files: list[Path] = []
    for root in roots:
        if not root.exists():
            continue
        for path in root.rglob("*.lean"):
            if not include_active and any(part in ACTIVE_PAPERS for part in path.parts):
                continue
            files.append(path)
    return sorted(files)


def strip_line_comment(line: str) -> str:
    """Drop Lean line comments.

    This is deliberately conservative and does not attempt to parse nested block
    comments. It is enough for the placeholder and `#check` ledger checks.
    """

    return line.split("--", 1)[0]


def lean_code_lines(path: Path) -> list[tuple[int, str]]:
    """Return Lean code lines with line and block comments removed."""

    code_lines: list[tuple[int, str]] = []
    depth = 0
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        out: list[str] = []
        i = 0
        while i < len(line):
            if depth == 0 and line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth > 0 and line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth > 0 and line.startswith("-/", i):
                depth -= 1
                i += 2
            elif depth == 0:
                out.append(line[i])
                i += 1
            else:
                i += 1
        code_lines.append((line_no, strip_line_comment("".join(out))))
    return code_lines


def check_sorries(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    sorry_re = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")
    for path in lean_files(include_active):
        for line_no, code in lean_code_lines(path):
            if sorry_re.search(code):
                findings.append(Finding("ERROR", path, f"Lean `sorry` at line {line_no}"))
    return findings


def check_guarded_checks(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    for path in lean_files(include_active):
        previous_significant = ""
        for line_no, line in lean_code_lines(path):
            code = line.strip()
            if "#check" in code:
                if previous_significant != "#guard_msgs(drop info) in":
                    findings.append(
                        Finding(
                            "ERROR",
                            path,
                            f"unguarded `#check` at line {line_no}; wrap with `#guard_msgs(drop info) in`",
                        )
                    )
            if code:
                previous_significant = code
    return findings


def paper_dirs(include_template: bool = False) -> list[Path]:
    dirs = [p for p in PAPERS.iterdir() if p.is_dir()]
    if not include_template:
        dirs = [p for p in dirs if p.name != "TEMPLATE"]
    return sorted(dirs)


def has_source_pdf(folder: Path) -> bool:
    return any(path.name != "DependencyDAG.pdf" for path in folder.rglob("*.pdf"))


def has_text_cache(folder: Path) -> bool:
    return any(path.suffix == ".txt" for path in folder.rglob("*.txt"))


def check_paper_contract(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    for folder in paper_dirs():
        active = folder.name in ACTIVE_PAPERS
        if active and not include_active:
            continue

        if not PAPER_FOLDER_NAME_RE.fullmatch(folder.name):
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    "paper folder name should match `[AuthorInitials][2DigitYear][Descriptor]`",
                )
            )

        aggregator = PAPERS / f"{folder.name}.lean"
        if not aggregator.exists():
            findings.append(Finding("ERROR", folder, f"missing paper import file `{aggregator.name}`"))

        for filename in sorted(REQUIRED_PAPER_FILES):
            if not (folder / filename).exists():
                findings.append(Finding("ERROR", folder, f"missing required file `{filename}`"))

        dag_pdf = folder / "DependencyDAG.pdf"
        if not dag_pdf.exists():
            findings.append(Finding("WARN", folder, "rendered `DependencyDAG.pdf` is absent locally"))
        dag_tex = folder / "DependencyDAG.tex"
        if dag_tex.exists():
            dag_text = dag_tex.read_text(encoding="utf-8")
            if DAG_REQUIRED_PREAMBLE not in dag_text:
                findings.append(
                    Finding(
                        "ERROR",
                        dag_tex,
                        f"DAG should input shared preamble `{DAG_REQUIRED_PREAMBLE}`",
                    )
                )

        if not has_source_pdf(folder):
            severity = "WARN" if PUBLIC_RELEASE else "ERROR"
            message = (
                "no cached source PDF found; public-release checkouts may omit source PDFs for licensing"
                if PUBLIC_RELEASE
                else "no cached source PDF found"
            )
            findings.append(Finding(severity, folder, message))
        if not has_text_cache(folder):
            findings.append(Finding("ERROR", folder, "no cached `pdftotext` source text found"))

        gitignore = folder / ".gitignore"
        if gitignore.exists():
            contents = gitignore.read_text(encoding="utf-8")
            for pattern in sorted(REQUIRED_GITIGNORE_PATTERNS):
                if pattern not in contents:
                    findings.append(Finding("ERROR", gitignore, f"missing ignore pattern `{pattern}`"))

    aggregate_names = re.compile(r"(aggregate|test[-_ ]?of[-_ ]?time)", re.IGNORECASE)
    for folder in paper_dirs(include_template=True):
        if aggregate_names.search(folder.name):
            findings.append(Finding("ERROR", folder, "top-level aggregate paper folder should not exist"))
    return findings


def _safe_slice_id(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "-", value.strip()).strip("-") or "all"


def review_slice_counts(interface_text: str, slice_file: Path) -> tuple[list[str], dict[str, int]]:
    """Count human-review declaration rows by optional review-slice metadata."""

    decls: list[tuple[int, str]] = []
    for line_number, line in enumerate(interface_text.splitlines(), start=1):
        match = REVIEW_DECL_RE.match(line)
        if match:
            decls.append((line_number, match.group(1)))
    if not slice_file.exists():
        return [], {"all": len(decls)}

    try:
        payload = json.loads(slice_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ["review_slices.json is not valid JSON"], {"all": len(decls)}
    if not isinstance(payload, dict):
        return ["review_slices.json should contain a JSON object"], {"all": len(decls)}
    raw_slices = payload.get("slices")
    if not isinstance(raw_slices, list) or not raw_slices:
        return ["review_slices.json should define a nonempty `slices` list"], {"all": len(decls)}

    problems: list[str] = []
    slices: list[dict[str, object]] = []
    for index, raw_slice in enumerate(raw_slices, start=1):
        if not isinstance(raw_slice, dict):
            problems.append(f"slice {index} is not a JSON object")
            continue
        title = str(raw_slice.get("title") or raw_slice.get("id") or f"Slice {index}")
        slices.append({**raw_slice, "id": _safe_slice_id(str(raw_slice.get("id") or title))})

    counts: dict[str, int] = {str(rule["id"]): 0 for rule in slices}
    counts["other"] = 0
    for line_number, name in decls:
        assigned = False
        for rule in slices:
            names = rule.get("names")
            prefixes = rule.get("prefixes")
            pattern = rule.get("name_regex")
            line_start = rule.get("line_start")
            line_end = rule.get("line_end")
            try:
                matches_name = isinstance(names, list) and name in {str(item) for item in names}
                matches_prefix = isinstance(prefixes, list) and any(
                    name.startswith(str(prefix)) for prefix in prefixes
                )
                matches_regex = isinstance(pattern, str) and bool(re.search(pattern, name))
            except re.error:
                problems.append(f"slice `{rule['id']}` has invalid `name_regex`")
                matches_regex = False
            matches_line = False
            if isinstance(line_start, int) or isinstance(line_end, int):
                start_ok = not isinstance(line_start, int) or line_number >= line_start
                end_ok = not isinstance(line_end, int) or line_number <= line_end
                matches_line = start_ok and end_ok
            if matches_name or matches_prefix or matches_regex or matches_line:
                counts[str(rule["id"])] = counts.get(str(rule["id"]), 0) + 1
                assigned = True
                break
        if not assigned:
            counts["other"] += 1
    if counts.get("other") == 0:
        counts.pop("other", None)
    return problems, counts


def check_review_launcher_readiness(include_active: bool) -> list[Finding]:
    """Check the paper-local human-review launcher contract from the skill."""

    findings: list[Finding] = []
    launcher_text = f"{REVIEW_LAUNCHER_TARGET}"
    for folder in paper_dirs():
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue

        interface = folder / "PaperInterface.lean"
        launcher = folder / REVIEW_LAUNCHER_NAME
        cache = folder / REVIEW_TRACE_CACHE

        if not interface.exists():
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    f"review launcher cannot be enabled until `PaperInterface.lean` exists",
                )
            )
            if launcher.exists():
                findings.append(
                    Finding(
                        "WARN",
                        launcher,
                        "review launcher exists but there is no `PaperInterface.lean` to review",
                    )
                )
            continue

        if not launcher.exists():
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    f"missing `{REVIEW_LAUNCHER_NAME}`; run `python3 scripts/bootstrap_review_launchers.py --write`",
                )
            )
        else:
            text = launcher.read_text(encoding="utf-8")
            if launcher_text not in text:
                findings.append(
                    Finding(
                        "ERROR",
                        launcher,
                        f"launcher should delegate to `{REVIEW_LAUNCHER_TARGET}`",
                    )
                )
            if not (launcher.stat().st_mode & 0o111):
                findings.append(Finding("ERROR", launcher, "launcher is not executable"))

        if not cache.exists():
            findings.append(
                Finding(
                    "WARN",
                    folder,
                    "review dashboard cache is absent; run `python3 scripts/review_dashboard.py --paper "
                    f"{folder.name} --refresh-cache` before a review session",
                )
            )

        interface_text = interface.read_text(encoding="utf-8")
        item_count = len(REVIEW_DECL_RE.findall(interface_text))
        if item_count == 0:
            findings.append(Finding("ERROR", interface, "review dashboard finds no review rows"))
        elif item_count > REVIEW_ROW_WARN_THRESHOLD:
            slice_file = folder / REVIEW_SLICES_NAME
            problems, counts = review_slice_counts(interface_text, slice_file)
            for problem in sorted(set(problems)):
                findings.append(Finding("ERROR", slice_file, problem))
            max_slice = max(counts.values()) if counts else item_count
            if not slice_file.exists():
                findings.append(
                    Finding(
                        "WARN",
                        interface,
                        f"review dashboard exposes {item_count} rows; add `{REVIEW_SLICES_NAME}` slices of at most "
                        f"{REVIEW_ROW_WARN_THRESHOLD} rows",
                    )
                )
            elif max_slice > REVIEW_ROW_WARN_THRESHOLD:
                findings.append(
                    Finding(
                        "WARN",
                        slice_file,
                        f"largest review slice has {max_slice} rows; keep slices at or below "
                        f"{REVIEW_ROW_WARN_THRESHOLD} rows",
                    )
                )
            else:
                findings.append(
                    Finding(
                        "INFO",
                        slice_file,
                        f"review dashboard exposes {item_count} rows across {len(counts)} review slices",
                    )
                )

    return findings


def check_dag_status_styles() -> list[Finding]:
    findings: list[Finding] = []
    preamble = ROOT / "docs" / "tikz" / "dag_preamble.tex"
    template = PAPERS / "TEMPLATE" / "DependencyDAG.tex"
    if preamble.exists():
        text = preamble.read_text(encoding="utf-8")
        for style in sorted(DAG_STATUS_STYLES):
            if f"{style}/.style" not in text:
                findings.append(Finding("ERROR", preamble, f"missing DAG status style `{style}`"))
    if template.exists():
        text = template.read_text(encoding="utf-8")
        normalized_text = re.sub(r"\\+", " ", text)
        normalized_text = re.sub(r"\s+", " ", normalized_text)
        for status in sorted(PAPER_STATUS_VALUES):
            if status not in normalized_text:
                findings.append(Finding("ERROR", template, f"template legend should mention status `{status}`"))
    return findings


def check_paper_facing_ledgers(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    for folder in paper_dirs():
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue

        ledger_candidates = [folder / "MainTheorems.lean", folder / "PaperInterface.lean"]
        existing = [path for path in ledger_candidates if path.exists()]
        if not existing:
            continue

        for ledger in existing:
            text = ledger.read_text(encoding="utf-8")
            if LEDGER_PLACEHOLDER_RE.search(text):
                findings.append(
                    Finding("ERROR", ledger, "paper-facing ledger still contains template placeholders")
                )
            if not LEAN_DECL_RE.search(text):
                findings.append(
                    Finding("WARN", ledger, "paper-facing ledger has no theorem/lemma/def/abbrev declarations")
                )
            if "#check" in text and "#guard_msgs(drop info) in" not in text:
                findings.append(
                    Finding("ERROR", ledger, "paper-facing ledger contains unguarded `#check`")
                )
    return findings


def check_post_paper_audit_interfaces(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    readme = ROOT / "README.md"
    interface_required = root_status_interface_required_papers(readme) if readme.exists() else set()

    for folder in paper_dirs():
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue

        interface = folder / "PaperInterface.lean"
        audit = folder / "PostPaperAudit.lean"
        report = folder / "FINAL_VALIDATION_REPORT.md"
        aggregator = PAPERS / f"{folder.name}.lean"

        if folder.name in interface_required and not interface.exists():
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    "completed/formalized paper is missing `PaperInterface.lean`",
                )
            )

        if interface.exists():
            text = interface.read_text(encoding="utf-8")
            if folder.name in interface_required and aggregator.exists():
                import_line = f"import {folder.name}.PaperInterface"
                if import_line not in aggregator.read_text(encoding="utf-8"):
                    findings.append(
                        Finding(
                            "ERROR",
                            aggregator,
                            "completed/formalized paper root should import `PaperInterface.lean`",
                        )
                    )
            if "PProd" in text:
                findings.append(
                    Finding("ERROR", interface, "human-facing interface should not use tuple witnesses")
                )
            if INTERFACE_WITNESS_RE.search(text):
                findings.append(
                    Finding(
                        "ERROR",
                        interface,
                        "human-facing interface should not expose tuple/prod witness declarations",
                    )
                )
            if not re.search(r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+", text, re.M):
                findings.append(
                    Finding(
                        "WARN",
                        interface,
                        "human-facing interface has no visible definition/abbrev declarations",
                    )
                )
            has_theorem_or_theorem_alias = re.search(r"^\s*theorem\s+", text, re.M) or re.search(
                r"^\s*(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev)\s+"
                r"(?:theorem|lemma|proposition|corollary)[A-Za-z0-9_']*\b",
                text,
                re.M,
            )
            if not has_theorem_or_theorem_alias:
                findings.append(
                    Finding("WARN", interface, "human-facing interface has no visible theorem statements")
                )

        if audit.exists():
            text = audit.read_text(encoding="utf-8")
            if aggregator.exists():
                import_line = f"import {folder.name}.PostPaperAudit"
                if import_line not in aggregator.read_text(encoding="utf-8"):
                    findings.append(
                        Finding(
                            "WARN",
                            aggregator,
                            "paper root should import existing `PostPaperAudit.lean`",
                        )
                    )
            if interface.exists() and "PaperInterface.lean" not in text:
                findings.append(
                    Finding("WARN", audit, "post-paper audit should point to `PaperInterface.lean`")
                )
            for match in PROOF_FACING_AUDIT_FORMULA_RE.finditer(text):
                line_no = text.count("\n", 0, match.start()) + 1
                findings.append(
                    Finding(
                        "ERROR",
                        audit,
                        f"proof-facing formula alias at line {line_no}; put paper formulas in `PaperInterface.lean`",
                    )
                )

        if report.exists():
            text = report.read_text(encoding="utf-8")
            if "Lean witness" in text:
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        "final report should prefer `Lean interface statement(s)` over `Lean witness`",
                    )
                )

    return findings


def markdown_cells(line: str) -> list[str]:
    return [cell.strip() for cell in line.strip().strip("|").split("|")]


def iter_markdown_tables(path: Path) -> list[tuple[list[str], list[list[str]]]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    tables: list[tuple[list[str], list[list[str]]]] = []
    i = 0
    while i + 1 < len(lines):
        if "|" not in lines[i] or "|" not in lines[i + 1]:
            i += 1
            continue
        header = markdown_cells(lines[i])
        separator = markdown_cells(lines[i + 1])
        if not separator or not all(re.fullmatch(r":?-{3,}:?", cell) for cell in separator):
            i += 1
            continue
        rows: list[list[str]] = []
        i += 2
        while i < len(lines) and "|" in lines[i]:
            rows.append(markdown_cells(lines[i]))
            i += 1
        tables.append((header, rows))
    return tables


def paper_folder_from_link(cell: str) -> str | None:
    markdown_link = re.search(r"\]\((papers/[^)#]+)", cell)
    if markdown_link:
        return Path(markdown_link.group(1)).name
    backtick_path = re.fullmatch(r"`?papers/([^`]+)`?", cell.strip())
    if backtick_path:
        return Path(backtick_path.group(1)).name
    return None


def root_status_interface_required_papers(readme: Path) -> set[str]:
    required: set[str] = set()
    for header, rows in iter_markdown_tables(readme):
        if header != README_STATUS_HEADER:
            continue
        paper_idx = header.index("Paper")
        status_idx = header.index("Status")
        for row in rows:
            if len(row) <= max(paper_idx, status_idx):
                continue
            if row[status_idx].strip() not in ROOT_INTERFACE_REQUIRED_STATUSES:
                continue
            folder = paper_folder_from_link(row[paper_idx])
            if folder is not None:
                required.add(folder)
    return required


def check_root_human_status_table(readme: Path) -> list[Finding]:
    findings: list[Finding] = []
    matching_tables = [(header, rows) for header, rows in iter_markdown_tables(readme) if header == README_STATUS_HEADER]

    if not matching_tables:
        findings.append(
            Finding(
                "ERROR",
                readme,
                "top-level README should include a concise human status table: `Paper | Status | Human summary`",
            )
        )
        return findings

    if len(matching_tables) > 1:
        findings.append(Finding("WARN", readme, "top-level README has multiple human status tables"))

    header, rows = matching_tables[0]
    paper_idx = header.index("Paper")
    status_idx = header.index("Status")
    summary_idx = header.index("Human summary")
    seen: set[str] = set()

    if len(rows) > README_MAX_STATUS_ROWS:
        findings.append(
            Finding(
                "WARN",
                readme,
                f"human status table has {len(rows)} rows; keep it concise",
            )
        )

    for row_number, row in enumerate(rows, start=1):
        if len(row) <= max(paper_idx, status_idx, summary_idx):
            findings.append(Finding("ERROR", readme, f"malformed human status row {row_number}"))
            continue

        paper = row[paper_idx].strip()
        status = row[status_idx].strip()
        summary = row[summary_idx].strip()

        folder = paper_folder_from_link(paper)
        if folder is None:
            findings.append(
                Finding("ERROR", readme, f"human status row {row_number} should link to `papers/<PaperName>`")
            )
        else:
            seen.add(folder)

        if status not in ROOT_STATUS_VALUES:
            findings.append(Finding("ERROR", readme, f"unexpected human README status `{status}` for `{paper}`"))
        if not summary:
            findings.append(Finding("ERROR", readme, f"missing human summary for `{paper}`"))
        elif len(summary) > README_MAX_STATUS_SUMMARY_CHARS:
            findings.append(Finding("WARN", readme, f"human summary is too long for `{paper}`"))

        for cell in row:
            detail = README_STATUS_DETAIL_RE.search(cell)
            if detail:
                findings.append(
                    Finding(
                        "ERROR",
                        readme,
                        f"implementation-facing detail `{detail.group(0)}` in human status row `{paper}`",
                    )
                )

    known = {folder.name for folder in paper_dirs()}
    missing = known - seen
    extra = seen - known
    if missing:
        findings.append(Finding("ERROR", readme, f"missing human status rows: {', '.join(sorted(missing))}"))
    if extra:
        findings.append(Finding("ERROR", readme, f"unknown human status rows: {', '.join(sorted(extra))}"))

    return findings


def check_root_status_table() -> list[Finding]:
    findings: list[Finding] = []
    readme = ROOT / "README.md"
    for header, rows in iter_markdown_tables(readme):
        if "Paper folder" not in header or "Overall status" not in header:
            continue
        status_idx = header.index("Overall status")
        folder_idx = header.index("Paper folder")
        seen = set()
        for row in rows:
            if len(row) <= max(status_idx, folder_idx):
                continue
            folder = row[folder_idx].strip("`")
            seen.add(Path(folder).name)
            status = row[status_idx]
            if status not in ROOT_STATUS_VALUES:
                findings.append(Finding("ERROR", readme, f"unexpected root status `{status}` for `{folder}`"))
        missing = {p.name for p in paper_dirs()} - seen
        if missing:
            findings.append(Finding("ERROR", readme, f"missing root status rows: {', '.join(sorted(missing))}"))
    return findings


def check_status_label_vocabulary() -> list[Finding]:
    findings: list[Finding] = []
    paths = [
        ROOT / "README.md",
        ROOT / "docs" / "PAPER_STATUS.md",
        ROOT / "docs" / "ECONCSLEAN_CURRENT_STATUS.md",
        ROOT / "docs" / "GARG_AUTHOR_FORMALIZATION_REPORT.md",
        ROOT / "site" / "index.html",
    ]
    paths.extend(sorted(PAPERS.glob("*/FINAL_VALIDATION_REPORT.md")))
    for path in paths:
        if not path.exists():
            continue
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if FORBIDDEN_STATUS_LABEL_RE.search(line):
                findings.append(
                    Finding(
                        "ERROR",
                        path,
                        f"legacy `Verified` status label at line {line_no}; use `Formalized` or `Formalized with caveat`",
                    )
                )
    return findings


def check_readme_status_tables(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    suspicious_caveat = re.compile(
        r"\b(open|conditional|caveat|mismatch|bug|not formalized|not covered)\b",
        re.I,
    )
    for folder in paper_dirs():
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        readme = folder / "README.md"
        if not readme.exists():
            continue
        found_status_table = False
        for header, rows in iter_markdown_tables(readme):
            normalized = [h.lower() for h in header]
            if "status" not in normalized:
                continue
            found_status_table = True
            status_idx = normalized.index("status")
            decl_idx = normalized.index("lean declaration") if "lean declaration" in normalized else None
            file_idx = normalized.index("file") if "file" in normalized else None
            rem_idx = next(
                (idx for idx, h in enumerate(normalized) if "remaining" in h or "mismatch" in h),
                None,
            )
            for row in rows:
                if len(row) <= status_idx:
                    continue
                status_raw = row[status_idx].strip()
                status = status_raw.lower()
                decl = row[decl_idx].lower() if decl_idx is not None and len(row) > decl_idx else ""
                file_cell = row[file_idx].lower() if file_idx is not None and len(row) > file_idx else ""
                remaining = row[rem_idx] if rem_idx is not None and len(row) > rem_idx else ""

                if status not in PAPER_STATUS_VALUES:
                    findings.append(
                        Finding(
                            "ERROR",
                            readme,
                            f"unexpected paper status `{status_raw}` for `{row[0]}`; see docs/STATUS.md",
                        )
                    )

                has_none_decl = decl in {"none", "`none`"} or "none matching" in decl
                has_none_file = file_cell in {"none", "`none`"}
                if has_none_decl and not any(marker in status for marker in ("not", "open", "started")):
                    findings.append(
                        Finding("ERROR", readme, f"row has declaration `none` but status `{row[status_idx]}`")
                    )
                exact_formalized = status.strip() == "formalized"
                if exact_formalized and has_none_file:
                    findings.append(
                        Finding("ERROR", readme, f"formalized row points to file `none`: `{row[0]}`")
                    )
                remaining_normalized = remaining.strip().strip("`").lower()
                if exact_formalized and not remaining_normalized.startswith("none"):
                    findings.append(
                        Finding(
                            "WARN",
                            readme,
                            f"`formalized` row should use remaining assumptions `None`: `{row[0]}`",
                        )
                    )
                if exact_formalized and suspicious_caveat.search(remaining):
                    findings.append(
                        Finding("WARN", readme, f"`formalized` row has caveat-like text: `{row[0]}`")
                    )
        if not found_status_table:
            findings.append(Finding("ERROR", readme, "no theorem/status markdown table found"))
    findings.extend(check_root_status_table())
    return findings


def git_ls_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.stdout.splitlines()


def check_tracked_artifacts(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    artifact_re = re.compile(r"DependencyDAG\.(aux|fdb_latexmk|fls|log)$")
    for rel in git_ls_files():
        path = Path(rel)
        if len(path.parts) < 3 or path.parts[0] != "papers":
            continue
        paper = path.parts[1]
        if paper in ACTIVE_PAPERS and not include_active:
            continue
        if artifact_re.search(path.name):
            findings.append(Finding("ERROR", ROOT / path, "tracked LaTeX build artifact"))
        if path.suffix == ".pdf" and path.name != "DependencyDAG.pdf":
            findings.append(Finding("ERROR", ROOT / path, "tracked PDF artifact; source PDFs should stay ignored"))
    return findings


def check_stale_architecture_terms() -> list[Finding]:
    findings: list[Finding] = []
    stale_re = re.compile(r"\bDecisionCore\b")
    paths = [
        ROOT / "README.md",
        ROOT / "docs" / "ARCHITECTURE.md",
        ROOT / "docs" / "ECONCSLEAN_CURRENT_STATUS.md",
        ROOT / "skills" / "econcs-formalizer" / "SKILL.md",
    ]
    paths.extend(sorted((ROOT / "skills" / "econcs-formalizer" / "references").glob("*.md")))
    for path in paths:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(text.splitlines(), start=1):
            if stale_re.search(line):
                findings.append(
                    Finding(
                        "WARN",
                        path,
                        f"stale architecture term `DecisionCore` at line {line_no}; use current `EconCSLib` layering",
                    )
                )
    return findings


def check_human_facing_readme() -> list[Finding]:
    findings: list[Finding] = []
    readme = ROOT / "README.md"
    docs_index = ROOT / "docs" / "README.md"
    workflow = ROOT / "docs" / "AGENT_FORMALIZATION_WORKFLOW.md"

    if not readme.exists():
        findings.append(Finding("ERROR", readme, "top-level human-facing README is missing"))
        return findings

    text = readme.read_text(encoding="utf-8")
    lines = text.splitlines()

    if len(lines) > README_MAX_LINES:
        findings.append(
            Finding(
                "WARN",
                readme,
                f"top-level README has {len(lines)} lines; keep it short and human-facing",
            )
        )

    if README_OLD_STATUS_TABLE_RE.search(text):
        findings.append(
            Finding(
                "ERROR",
                readme,
                "top-level README should use the concise `Paper | Status | Human summary` table, not the full paper ledger",
            )
        )
    findings.extend(check_root_human_status_table(readme))

    for match in README_AGENT_DETAIL_RE.finditer(text):
        line_no = text.count("\n", 0, match.start()) + 1
        findings.append(
            Finding(
                "ERROR",
                readme,
                f"agent-facing detail `{match.group(0)}` at line {line_no}; move it to docs/AGENT_FORMALIZATION_WORKFLOW.md",
            )
        )

    if "docs/AGENT_FORMALIZATION_WORKFLOW.md" not in text:
        findings.append(
            Finding(
                "ERROR",
                readme,
                "top-level README should link to docs/AGENT_FORMALIZATION_WORKFLOW.md for agent instructions",
            )
        )

    if "docs/README.md" not in text:
        findings.append(
            Finding(
                "WARN",
                readme,
                "top-level README should link to docs/README.md for the documentation audience split",
            )
        )

    if not docs_index.exists():
        findings.append(Finding("ERROR", docs_index, "docs index is missing"))
    else:
        docs_text = docs_index.read_text(encoding="utf-8")
        if "Human-Facing" not in docs_text or "Agent And Maintainer-Facing" not in docs_text:
            findings.append(
                Finding(
                    "ERROR",
                    docs_index,
                    "docs index should split human-facing docs from agent/maintainer-facing docs",
                )
            )

    if not workflow.exists():
        findings.append(Finding("ERROR", workflow, "agent formalization workflow doc is missing"))

    return findings


def has_module_docstring_with_main_declarations(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    match = re.search(r"/-!.*?-/", text, re.S)
    return bool(match and "## Main declarations" in match.group(0))


def check_strict_lean_style() -> list[Finding]:
    findings: list[Finding] = []
    for path in sorted((ROOT / "EconCSLib").rglob("*.lean")):
        if not has_module_docstring_with_main_declarations(path):
            findings.append(
                Finding(
                    "WARN",
                    path,
                    "new reusable modules should have a module docstring with `## Main declarations`",
                )
            )
    return findings


def run(include_active: bool, strict_style: bool) -> list[Finding]:
    findings: list[Finding] = []
    findings.extend(check_sorries(include_active))
    findings.extend(check_guarded_checks(include_active))
    findings.extend(check_paper_contract(include_active))
    findings.extend(check_review_launcher_readiness(include_active))
    findings.extend(check_dag_status_styles())
    findings.extend(check_paper_facing_ledgers(include_active))
    findings.extend(check_post_paper_audit_interfaces(include_active))
    findings.extend(check_status_label_vocabulary())
    findings.extend(check_readme_status_tables(include_active))
    findings.extend(check_tracked_artifacts(include_active))
    findings.extend(check_stale_architecture_terms())
    findings.extend(check_human_facing_readme())
    if strict_style:
        findings.extend(check_strict_lean_style())
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--include-active",
        action="store_true",
        help="also audit active fairness/monoculture folders that may be dirty under other agents",
    )
    parser.add_argument(
        "--strict-style",
        action="store_true",
        help="also report Mathlib-style module-docstring guidance for reusable EconCSLib modules",
    )
    args = parser.parse_args()

    findings = run(include_active=args.include_active, strict_style=args.strict_style)
    for finding in findings:
        print(finding.format())

    errors = [finding for finding in findings if finding.severity == "ERROR"]
    warnings = [finding for finding in findings if finding.severity == "WARN"]
    print(
        f"Audit complete: {len(errors)} error(s), {len(warnings)} warning(s)"
        + ("; active paper folders included" if args.include_active else "; active paper folders skipped")
        + ("; strict style included" if args.strict_style else "")
    )
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
