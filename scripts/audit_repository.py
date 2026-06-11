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
    "!DependencyDAG.pdf",
    "*.aux",
    "*.log",
    "*.fls",
    "*.fdb_latexmk",
    "*.synctex.gz",
}
REVIEW_LAUNCHER_NAME = "review-dashboard.sh"
REVIEW_LAUNCHER_TARGET = "scripts/launch_review_dashboard.sh"
REVIEW_TRACE_CACHE = ".review_traces/paper_interface_cache.json"
REVIEW_ROW_WARN_THRESHOLD = 80
PAPER_STATUS_FILE = PAPERS / "status.json"
PAPER_INTERFACE_OVERSIZED_LINE_THRESHOLD = 3000
ROOT_STATUS_VALUES = {
    "Formalized",
    "Formalized with caveat",
    "Formalized with documented caveat",
    "Main endpoints formalized",
    "Main endpoints formalized with documented deviations",
    "Partially formalized",
    "Scaffold",
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
HUMAN_SUMMARY_REVIEW_VALUES = {
    "draft",
    "agent_draft",
    "human_written",
    "human_approved",
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
REVIEW_DECL_KIND_RE = re.compile(
    r"^\s*(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
    re.M,
)
REVIEW_EXPORT_OPEN_RE = re.compile(
    r"^\s*export\s+[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\s+\((.*)$"
)
REVIEW_EXPORT_NAME_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")
SOURCE_EQUATION_WRAPPER_MARKERS = (
    "_formula",
    "_iff",
    "_fields",
    "_rule",
    "_content",
    "_matches",
    "_allocation_payment",
    "_uniform",
    "_pmf",
    "_choice_feasible",
    "_query_choice",
    "_has_",
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
README_STATUS_HEADER = ["Paper", "Status", "Human review", "PaperInterface size", "Public note"]
README_REVIEW_COUNT_RE = re.compile(r"^\d+/\d+$")
README_MAX_STATUS_ROWS = 20
MARKDOWN_LINK_RE = re.compile(r"\[([^\]]+)\]\([^)]+\)")
README_MAX_LINES = 140
REPORT_LEAN_LABEL_RE = re.compile(
    r"\bLean\s+(?:interface\s+statement(?:\(s\))?|declaration(?:s)?|witness(?:es)?)\s*[:.]",
    re.I,
)
REPORT_DECL_TABLE_HEADER_RE = re.compile(
    r"\bLean\s+(?:interface\s+statement(?:\(s\))?|declaration(?:s)?|witness(?:es)?)\b",
    re.I,
)
REPORT_CODE_SPAN_RE = re.compile(r"`([^`]+)`")
REPORT_DECL_NAME_RE = re.compile(
    r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*"
)
REPORT_NON_DECL_CODE_SUFFIXES = (
    ".lean",
    ".md",
    ".json",
    ".tex",
    ".pdf",
    ".py",
)


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
    return any(path.suffix == ".txt" and path.name != "citation_source.txt" for path in folder.rglob("*.txt"))


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
        if not PUBLIC_RELEASE and not has_text_cache(folder):
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


def review_rows_from_interface_text(interface_text: str) -> list[tuple[int, str]]:
    """Return declaration/export rows exposed by a human review interface."""

    lines = interface_text.splitlines()
    decls: list[tuple[int, str]] = []
    line_number = 1
    block_depth = 0
    while line_number <= len(lines):
        line = lines[line_number - 1]
        stripped = line.strip()
        if block_depth > 0:
            block_depth += line.count("/-")
            block_depth -= line.count("-/")
            block_depth = max(block_depth, 0)
            line_number += 1
            continue
        if stripped.startswith("/-"):
            block_depth += line.count("/-")
            block_depth -= line.count("-/")
            block_depth = max(block_depth, 0)
            line_number += 1
            continue
        if stripped.startswith("--"):
            line_number += 1
            continue
        match = REVIEW_DECL_RE.match(line)
        if match:
            decls.append((line_number, match.group(1)))
            line_number += 1
            continue
        export_match = REVIEW_EXPORT_OPEN_RE.match(line)
        if export_match:
            chunks = [export_match.group(1)]
            end_line_number = line_number
            while ")" not in chunks[-1] and end_line_number < len(lines):
                end_line_number += 1
                chunks.append(lines[end_line_number - 1])
            names_text = "\n".join(chunks).split(")", 1)[0]
            for name in REVIEW_EXPORT_NAME_RE.findall(names_text):
                decls.append((line_number, name))
            line_number = end_line_number + 1
            continue
        line_number += 1
    return decls


def review_declaration_blocks(interface_text: str) -> dict[str, tuple[int, str, str]]:
    """Return paper-interface declarations keyed by name.

    Values are `(line_number, kind, declaration_source)`.  The parser mirrors
    the lightweight dashboard row parser; it is intentionally syntactic and
    only needs enough structure for review-surface hygiene checks.
    """

    lines = interface_text.splitlines()
    starts: list[tuple[int, str, str]] = []
    block_depth = 0
    for line_number, line in enumerate(lines, start=1):
        stripped = line.strip()
        if block_depth > 0:
            block_depth += line.count("/-")
            block_depth -= line.count("-/")
            block_depth = max(block_depth, 0)
            continue
        if stripped.startswith("/-"):
            block_depth += line.count("/-")
            block_depth -= line.count("-/")
            block_depth = max(block_depth, 0)
            continue
        if stripped.startswith("--"):
            continue
        match = REVIEW_DECL_KIND_RE.match(line)
        if match:
            starts.append((line_number, match.group(1), match.group(2)))

    out: dict[str, tuple[int, str, str]] = {}
    for index, (line_number, kind, name) in enumerate(starts):
        next_line = starts[index + 1][0] if index + 1 < len(starts) else len(lines) + 1
        source = "\n".join(lines[line_number - 1 : next_line - 1]).strip()
        out[name] = (line_number, kind, source)
    return out


def _lower_initial(name: str) -> str:
    return name[:1].lower() + name[1:] if name else name


def source_equation_wrapper_candidates(name: str, decl_names: set[str]) -> list[str]:
    """Find likely source-equation wrappers that should replace an opaque alias row."""

    prefixes = {f"{name}_", f"{_lower_initial(name)}_"}
    candidates = []
    for candidate in decl_names:
        if candidate == name or not any(candidate.startswith(prefix) for prefix in prefixes):
            continue
        if any(marker in candidate for marker in SOURCE_EQUATION_WRAPPER_MARKERS):
            candidates.append(candidate)
    return sorted(candidates)


def is_signature_only_review_alias(kind: str, source: str) -> bool:
    """Heuristic for review rows that expose only an imported function/type alias."""

    if kind not in {"abbrev", "def"} or ":=" not in source:
        return False
    body = re.sub(r"\s+", " ", source.split(":=", 1)[1].strip())
    if not body:
        return False
    if body.startswith("@"):
        return True
    if re.match(r"(?:[A-Z][A-Za-z0-9_']*|[A-Za-z_][A-Za-z0-9_']*\.)", body):
        return True
    if re.match(r"paper_[A-Za-z0-9_']+\b", body):
        return True
    return False


def review_surface_slice_counts(interface_text: str, status_file: Path) -> tuple[list[str], dict[str, int]]:
    """Count human-review declaration rows by paper-local status review slices."""

    decls = review_rows_from_interface_text(interface_text)
    if not status_file.exists():
        return [], {"all": len(decls)}

    try:
        payload = json.loads(status_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ["status.json is not valid JSON"], {"all": len(decls)}
    if not isinstance(payload, dict):
        return ["status.json should contain a JSON object"], {"all": len(decls)}
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return ["status.json should define a `review_surface` object"], {"all": len(decls)}
    raw_slices = review_surface.get("slices")
    if not isinstance(raw_slices, list) or not raw_slices:
        return ["status.json review_surface should define a nonempty `slices` list"], {"all": len(decls)}

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
        item_count = len(review_rows_from_interface_text(interface_text))
        if item_count == 0:
            findings.append(Finding("ERROR", interface, "review dashboard finds no review rows"))
        elif item_count > REVIEW_ROW_WARN_THRESHOLD:
            status_file = folder / "status.json"
            problems, counts = review_surface_slice_counts(interface_text, status_file)
            for problem in sorted(set(problems)):
                findings.append(Finding("ERROR", status_file, problem))
            max_slice = max(counts.values()) if counts else item_count
            if not status_file.exists():
                findings.append(
                    Finding(
                        "WARN",
                        interface,
                        f"review dashboard exposes {item_count} rows; add `status.json` "
                        f"`review_surface.slices` of at most {REVIEW_ROW_WARN_THRESHOLD} rows",
                    )
                )
            elif max_slice > REVIEW_ROW_WARN_THRESHOLD:
                findings.append(
                    Finding(
                        "WARN",
                        status_file,
                        f"largest review slice has {max_slice} rows; keep slices at or below "
                        f"{REVIEW_ROW_WARN_THRESHOLD} rows",
                    )
                )
            else:
                findings.append(
                    Finding(
                        "INFO",
                        status_file,
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

        for markdown_report in (report, folder / "POST_FORMALIZATION_AUDIT.md"):
            if markdown_report.exists():
                findings.extend(check_report_declaration_inventory(markdown_report))

    return findings


def report_decl_code_spans(text: str) -> list[str]:
    spans: list[str] = []
    for span in REPORT_CODE_SPAN_RE.findall(text):
        if span.endswith(REPORT_NON_DECL_CODE_SUFFIXES):
            continue
        if "/" in span or " " in span or "-" in span:
            continue
        if REPORT_DECL_NAME_RE.fullmatch(span):
            spans.append(span)
    return spans


def check_report_declaration_inventory(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    text = path.read_text(encoding="utf-8")
    if re.search(r"\bmain Lean declarations\b", text, re.I):
        findings.append(
            Finding(
                "WARN",
                path,
                "final/post report should name one main interface declaration per paper-facing result, not a declaration inventory",
            )
        )

    for line_no, line in enumerate(text.splitlines(), start=1):
        if REPORT_LEAN_LABEL_RE.search(line):
            spans = report_decl_code_spans(line)
            if len(spans) > 1:
                findings.append(
                    Finding(
                        "WARN",
                        path,
                        f"line {line_no} lists {len(spans)} Lean declarations; keep only the single main interface declaration",
                    )
                )

    for header, rows in iter_markdown_tables(path):
        for idx, cell in enumerate(header):
            if not REPORT_DECL_TABLE_HEADER_RE.search(cell):
                continue
            for row in rows:
                if idx >= len(row):
                    continue
                spans = report_decl_code_spans(row[idx])
                if len(spans) > 1:
                    findings.append(
                        Finding(
                            "WARN",
                            path,
                            f"table column `{cell}` lists {len(spans)} Lean declarations in one row; keep one main interface declaration per paper-facing result",
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


def markdown_display_text(text: str) -> str:
    return MARKDOWN_LINK_RE.sub(r"\1", text)


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


def check_machine_paper_status() -> list[Finding]:
    findings: list[Finding] = []
    if not PAPER_STATUS_FILE.exists():
        findings.append(Finding("ERROR", PAPER_STATUS_FILE, "missing machine-readable paper status file"))
        return findings

    try:
        data = json.loads(PAPER_STATUS_FILE.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"invalid JSON: {exc.msg}"))
        return findings

    if data.get("schema") != 1:
        findings.append(Finding("ERROR", PAPER_STATUS_FILE, "expected `schema: 1`"))

    papers = data.get("papers")
    if not isinstance(papers, list):
        findings.append(Finding("ERROR", PAPER_STATUS_FILE, "`papers` should be a list"))
        return findings

    known = {folder.name for folder in paper_dirs()}
    entries: dict[str, dict] = {}
    for idx, entry in enumerate(papers, start=1):
        if not isinstance(entry, dict):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"paper entry {idx} should be an object"))
            continue
        paper_id = entry.get("id")
        if not isinstance(paper_id, str) or not paper_id:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"paper entry {idx} has missing `id`"))
            continue
        if paper_id in entries:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"duplicate paper status entry `{paper_id}`"))
        entries[paper_id] = entry

        paper_status_file = PAPERS / paper_id / "status.json"
        if not paper_status_file.exists():
            findings.append(Finding("ERROR", paper_status_file, "missing paper-local status source"))
        else:
            try:
                paper_status_payload = json.loads(paper_status_file.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                findings.append(Finding("ERROR", paper_status_file, f"invalid JSON: {exc.msg}"))
                paper_status_payload = None
            if isinstance(paper_status_payload, dict) and paper_status_payload != entry:
                findings.append(
                    Finding(
                        "ERROR",
                        PAPER_STATUS_FILE,
                        f"`{paper_id}` aggregate entry is out of sync with `{paper_status_file.relative_to(ROOT)}`",
                    )
                )

        for field in ("title", "source_version", "build_target", "status", "review_entrypoint"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has missing `{field}`"))

        status = entry.get("status")
        if isinstance(status, str) and status not in PAPER_STATUS_VALUES:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has unexpected status `{status}`"))

        summary_review = entry.get("human_summary_review")
        if summary_review is not None:
            if not isinstance(summary_review, dict):
                findings.append(
                    Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.human_summary_review` should be an object")
                )
            else:
                review_status = summary_review.get("status")
                if review_status not in HUMAN_SUMMARY_REVIEW_VALUES:
                    findings.append(
                        Finding(
                            "ERROR",
                            PAPER_STATUS_FILE,
                            f"`{paper_id}.human_summary_review.status` should be one of "
                            + ", ".join(sorted(HUMAN_SUMMARY_REVIEW_VALUES)),
                        )
                    )
                if review_status == "human_approved" and not isinstance(entry.get("human_summary"), str):
                    findings.append(
                        Finding(
                            "ERROR",
                            PAPER_STATUS_FILE,
                            f"`{paper_id}` has human-approved summary metadata but no `human_summary` string",
                        )
                    )

        review = entry.get("human_review")
        if not isinstance(review, dict):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has missing `human_review` object"))
        else:
            reviewed = review.get("reviewed_rows")
            total = review.get("total_rows")
            for field in ("reviewed_rows", "total_rows", "stale_rows", "mismatch_rows"):
                if not isinstance(review.get(field), int) or review[field] < 0:
                    findings.append(
                        Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.human_review.{field}` should be a nonnegative integer")
                    )
            if isinstance(reviewed, int) and isinstance(total, int) and reviewed > total:
                findings.append(
                    Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has reviewed_rows greater than total_rows")
                )

        interface = entry.get("paper_interface")
        if not isinstance(interface, dict):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has missing `paper_interface` object"))
            continue

        review_surface = entry.get("review_surface")
        if not isinstance(review_surface, dict):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has missing `review_surface` object"))
            review_surface = {}
        include_names = review_surface.get("include_names")
        if not isinstance(include_names, list) or not all(isinstance(name, str) and name for name in include_names):
            findings.append(
                Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.review_surface.include_names` should be a nonempty string list")
            )
            include_names = []

        path_value = interface.get("path")
        if not isinstance(path_value, str) or not path_value:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.paper_interface.path` is missing"))
            continue

        interface_path = ROOT / path_value
        if not interface_path.exists():
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` interface path does not exist: `{path_value}`"))
            continue

        actual_line_count = len(interface_path.read_text(encoding="utf-8").splitlines())
        interface_text = interface_path.read_text(encoding="utf-8")
        actual_review_names = [name for _line, name in review_rows_from_interface_text(interface_text)]
        declaration_blocks = review_declaration_blocks(interface_text)
        recorded_line_count = interface.get("line_count")
        if recorded_line_count != actual_line_count:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` line_count is {recorded_line_count}, expected {actual_line_count}",
                )
            )
        for name in include_names:
            declaration = declaration_blocks.get(name)
            if not declaration:
                continue
            line_no, kind, source = declaration
            if not is_signature_only_review_alias(kind, source):
                continue
            candidates = source_equation_wrapper_candidates(name, set(declaration_blocks))
            if candidates:
                findings.append(
                    Finding(
                        "ERROR",
                        interface_path,
                        f"`{paper_id}` review row `{name}` at line {line_no} is an opaque signature/alias; "
                        f"use source-equation wrapper `{candidates[0]}` in `status.json` `review_surface.include_names`",
                    )
                )

        total_rows = review.get("total_rows") if isinstance(review, dict) else None
        review_rows = interface.get("review_rows")
        if isinstance(total_rows, int) and review_rows != total_rows:
            findings.append(
                Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` review_rows should match human_review.total_rows")
            )
        if isinstance(total_rows, int) and include_names and len(include_names) != total_rows:
            findings.append(
                Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` include_names length should match human_review.total_rows")
            )
        missing_review_names = set(include_names) - set(actual_review_names)
        if missing_review_names:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` status names are not exported by PaperInterface.lean: "
                    + ", ".join(sorted(missing_review_names)),
                )
            )

        oversized = interface.get("oversized")
        if not isinstance(oversized, bool):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.paper_interface.oversized` should be boolean"))
        elif actual_line_count > PAPER_INTERFACE_OVERSIZED_LINE_THRESHOLD and not oversized:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` PaperInterface.lean has {actual_line_count} lines but is not marked oversized",
                )
            )
        elif oversized and not interface.get("maintainability_issue"):
            findings.append(
                Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` oversized interface should include maintainability_issue")
            )

    missing = known - set(entries)
    extra = set(entries) - known
    if missing:
        findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"missing paper status entries: {', '.join(sorted(missing))}"))
    if extra:
        findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"unknown paper status entries: {', '.join(sorted(extra))}"))

    return findings


def check_root_human_status_table(readme: Path) -> list[Finding]:
    findings: list[Finding] = []
    matching_tables = [(header, rows) for header, rows in iter_markdown_tables(readme) if header == README_STATUS_HEADER]

    if not matching_tables:
        findings.append(
            Finding(
                "ERROR",
                readme,
                "top-level README should include a concise human status table: `Paper | Status | Human review | PaperInterface size | Public note`",
            )
        )
        return findings

    if len(matching_tables) > 1:
        findings.append(Finding("WARN", readme, "top-level README has multiple human status tables"))

    header, rows = matching_tables[0]
    paper_idx = header.index("Paper")
    status_idx = header.index("Status")
    review_idx = header.index("Human review")
    interface_idx = header.index("PaperInterface size")
    summary_idx = header.index("Public note")
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
        if len(row) <= max(paper_idx, status_idx, review_idx, interface_idx, summary_idx):
            findings.append(Finding("ERROR", readme, f"malformed human status row {row_number}"))
            continue

        paper = row[paper_idx].strip()
        status = row[status_idx].strip()
        review = row[review_idx].strip()
        interface = row[interface_idx].strip()
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
        if not README_REVIEW_COUNT_RE.fullmatch(review):
            findings.append(Finding("ERROR", readme, f"human review cell should be `reviewed/total` for `{paper}`"))
        if not interface:
            findings.append(Finding("ERROR", readme, f"missing interface health for `{paper}`"))
        if not summary and status != "Formalized":
            findings.append(Finding("ERROR", readme, f"missing human summary for `{paper}`"))

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
                "top-level README should use the concise `Paper | Status | Human review | PaperInterface size | Public note` table, not the full paper ledger",
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
    findings.extend(check_machine_paper_status())
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
