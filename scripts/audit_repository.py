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
DEFAULT_LLM_ASSUMPTION_JUDGE_FILE = "assumption_match_llm.json"
DEFAULT_ASSUMPTION_SOURCE_FILE = "Assumptions.lean"
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
ALLOWED_TRACKED_PAPER_PDFS = {
    "DependencyDAG.pdf",
    "CAVEAT_ISSUES_SUMMARY.pdf",
}
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
LIBRARY_DECL_KIND_RE = re.compile(
    r"^\s*(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
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
FORMULA_SPECIFIC_NAME_RE = re.compile(
    r"(?:^|_)(?:"
    r"formula|identity|equation|eq|iff|if_and_only_if|ineq|inequality|"
    r"bound|rule|condition|criterion|definition|fields|cdf|density|pmf|"
    r"probability|expectation|variance|normalization|normalizer|integral|"
    r"derivative|limit|ratio|share|mass|threshold|cutoff|tail"
    r")(?:_|$)",
    re.I,
)
BROAD_REVIEW_ROW_NAME_RE = re.compile(
    r"(?:^|_)(?:"
    r"metrics?|surface|source_surface|core|bundle|package|summary|aggregate|"
    r"model|conditions?|certificate|rows?|fixed_policy|main_result"
    r")(?:_|$)",
    re.I,
)
NUMBERED_SOURCE_RESULT_RE = re.compile(
    r"\b(?:Definition|Lemma|Proposition|Theorem|Corollary|Claim)\s+"
    r"[A-Z]?\d+(?:\s*\([^)]+\))?",
    re.I,
)
NUMBERED_SOURCE_NAME_RE = re.compile(
    r"(?:^|_)(?:def(?:inition)?|lem(?:ma)?|prop(?:osition)?|thm|theorem|cor(?:ollary)?|claim)"
    r"[A-Z]?\d+(?:_|$)",
    re.I,
)
SOURCE_FORMULA_TEXT_RE = re.compile(
    r"\\(?:frac|sum|sqrt|Phi|int|prod|Pr|mathbb|operatorname)|"
    r"[=<>≤≥↔]|"
    r"\b(?:formula|identity|equation|if and only if|iff|criterion|"
    r"definition|probability|expectation|variance|density|cdf|integral|"
    r"normalization|ratio|mass|threshold|cutoff|tail)\b",
    re.I,
)
SOURCE_STATUS_LINE_RE = re.compile(r"\bSource status\s*:", re.I)
ASSUMPTION_POLICY_STRICT_VALUES = {
    "strict",
    "source_assumptions_only",
}
ASSUMPTION_DECL_NAME_RE = re.compile(
    r"^(?:paper_)?assumption(?:_|$)|^source_assumption(?:_|$)|_assumption(?:_|$)"
)
ASSUMPTION_AUDIT_PREMISE_RE = re.compile(r"^\s*--\s*audit-premise:\s*(.+?)\s*$")
APPROVED_ASSUMPTION_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "documented_caveat",
    "partial_boundary",
}
APPROVED_ASSUMPTION_PREMISE_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "source_text",
    "source_text_model_primitive",
    "derived_from_source_primitives",
    "documented_caveat",
    "partial_boundary",
}
LEAN_BINDER_RE = re.compile(r"[\(\{]([^()\{\}\[\]]+?)\s*:\s*([^()\{\}\[\]]+?)[\)\}]")
HYPOTHESIS_NAME_RE = re.compile(
    r"^(?:h[A-Za-z0-9_']*|.*(?:assumption|certificate|hypothesis|premise|regularity|bridge|row|threshold|capacity).*)$",
    re.I,
)
PROOF_BOUNDARY_TYPE_RE = re.compile(
    r"\b(?:Prop|[A-Za-z0-9_']*(?:Certificate|Assumption|Hypothesis|Witness|Boundary|"
    r"Bridge|Rows?|Table|SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|"
    r"Window|Windows|Package|Regularity|Invariant))\b",
    re.I,
)
VARIABLE_BOUNDARY_TYPE_RE = re.compile(
    r"\b[A-Za-z0-9_']*(?:Certificate|Assumption|Hypothesis|Witness|Boundary|Bridge|"
    r"Rows?|Table|SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|Window|"
    r"Windows|Package|Regularity|Invariant)\b",
    re.I,
)
LIBRARY_CERTIFICATE_BOUNDARY_RE = re.compile(
    r"(?:^|[_A-Za-z0-9'])("
    r"cert(?:ificate)?|source[-_ ]?rows?|source[-_ ]?table|row[-_ ]?package|"
    r"external|oracle|boundary|witness|bridge|assumption|hypothesis"
    r")",
    re.I,
)
LIBRARY_BOUNDARY_TYPE_RE = re.compile(
    r"\b[A-Za-z0-9_']*(?:"
    r"Certificate|Assumption|Hypothesis|Witness|Boundary|Bridge|Rows?|"
    r"SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|Window|Windows|Package|"
    r"Regularity|Invariant"
    r")\b",
    re.I,
)
LIBRARY_EXTERNAL_BOUNDARY_RE = re.compile(r"\b(?:external|oracle|npEqZPP|NP|ZPP|hardness)\b", re.I)
REVIEW_EXPLICIT_BOUNDARY_RE = re.compile(
    r"\b(?:[A-Za-z0-9_']*(?:Certificate|Oracle|External|Boundary|Bridge|"
    r"SourceFamilyRows|SourceRows?|SourceTable|Rows?|Table|Package|Window|Windows)|"
    r"source[-_ ]?rows?|source[-_ ]?table|row[-_ ]?package)\b",
    re.I,
)
PREDICATE_TYPE_WORD_RE = re.compile(
    r"\b(?:Positive|Nonnegative|NonnegativeBids|Nodup|Feasible|Optimal|Measurable|"
    r"Monotone|Strict|Domain|Truthful|Calibrated|Simplex|Support|Straddles|"
    r"Bound|Bounded|MarginalBound|Invariant|Dominant|Stable|Regular|Window|Windows|"
    r"Package|"
    r"fullSupport|truthful|calibrated|measurable|optimal|feasible)\b"
)
DATA_PARAMETER_TYPE_RE = re.compile(
    r"^(?:ℝ|ℕ|ℤ|Bool|String|Type(?:\\*)?|Sort|List\b|Fin\b|Candidate\b|Seller\b|"
    r"Signal\b|Rule\b|Rating\b|Query\b|Agent\b|Pair\b|Bundle\b|Policy\b|Measure\b)"
)
ALIAS_TARGET_RE = re.compile(
    r":=\s*@?\s*((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)"
)
PAPER_FACING_DECL_NAME_RE = re.compile(
    r"^(?:"
    r"paper_interface_|"
    r"source_(?:theorem|lemma|proposition|corollary|definition)"
    r")",
    re.I,
)
PROPOSITION_TYPE_MARKERS = (
    " = ",
    " < ",
    " > ",
    " ≤ ",
    " ≥ ",
    " ≠ ",
    " ↔ ",
    " → ",
    "∀",
    "∃",
    "∈",
    "∉",
)
NON_ARROW_PROPOSITION_TYPE_MARKERS = tuple(
    marker for marker in PROPOSITION_TYPE_MARKERS if marker != " → "
)
LEDGER_PLACEHOLDER_RE = re.compile(
    r"\[Paper Title\]|\bnamespace TEMPLATE\b|\bpaperDefinition1\b|\bpaper_theorem_1\b|Replace before claiming progress",
)
PROOF_FACING_AUDIT_FORMULA_RE = re.compile(
    r"/--(?:(?!-/).)*\bformula\b(?:(?!-/).)*-/\s*noncomputable\s+abbrev\s+audit[A-Za-z0-9_]*",
    re.I | re.S,
)
AXIOM_LIKE_DECL_RE = re.compile(r"^\s*(?:axiom|opaque|constant|unsafe\s+(?:axiom|def|theorem|lemma))\b")
SOURCE_SHAPED_LIBRARY_NAME_RE = re.compile(
    r"(?:^|_)(?:paper|displayed|appendix)(?:_|$)|"
    r"(?:^|_)source(?:[A-Z_]|$).*(?:formula|rate|threshold|row|table|surface|equation|branch|window|paper)|"
    r"^source[A-Z].*(?:Formula|Rate|Threshold|Row|Table|Surface|Equation|Branch|Window|Paper)|"
    r"(?:^|[A-Za-z0-9_'])Source(?:Formula|Rate|Threshold|Row|Rows|Table|Surface|Equation|"
    r"Branch|Window|Paper|Sorted|Critical|Objective|Score|Event)",
    re.I,
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
README_STATUS_HEADER = ["Paper", "Status", "Review", "Interface", "Human summary"]
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


@dataclass(frozen=True)
class LeanDeclaration:
    path: Path
    line: int
    kind: str
    name: str
    source: str


@dataclass(frozen=True)
class BoundaryDependency:
    """A certificate/source-boundary dependency found through declaration closure."""

    category: str
    premise: str
    declaration: LeanDeclaration
    via: str


DECLARATION_REFERENCE_RE = re.compile(
    r"\b(?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*\b"
)
REFERENCE_NAME_STOPLIST = {
    "by",
    "fun",
    "let",
    "have",
    "show",
    "exact",
    "simp",
    "simpa",
    "rw",
    "rfl",
    "from",
    "where",
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "Prop",
    "Type",
    "Sort",
    "True",
    "False",
    "And",
    "Or",
    "Not",
    "Iff",
    "Eq",
    "HEq",
    "Nat",
    "Int",
    "Real",
    "Fin",
    "List",
    "Set",
    "Finset",
    "Option",
    "none",
    "some",
    "map",
    "id",
}


def declaration_key(declaration: LeanDeclaration) -> tuple[Path, int, str]:
    return (declaration.path, declaration.line, declaration.name)


def reference_name_is_specific(name: str) -> bool:
    """Return whether a declaration name is specific enough for lexical closure.

    The closure is intentionally conservative: it should catch long paper/library
    helper names and avoid short common names such as `map`, `apply`, or `left`
    that would make static dependency propagation too noisy.
    """

    if not name or name in REFERENCE_NAME_STOPLIST:
        return False
    unqualified = name.rsplit(".", 1)[-1]
    if unqualified in REFERENCE_NAME_STOPLIST:
        return False
    if "." in name:
        return len(unqualified) >= 3
    # Avoid resolving paper-local variables or short prose-shaped identifiers
    # such as `bias`, `objective`, `model`, or `stable` against unrelated
    # reusable-library declarations.  Most cross-declaration proof/API calls in
    # this repo use underscore-heavy descriptive names; direct certificate
    # binders are still caught from declaration signatures separately.
    return "_" in unqualified or "'" in unqualified or len(unqualified) >= 16


def declaration_body(source: str) -> str:
    """Return the proof/body part of a Lean declaration for dependency scans."""

    if ":=" not in source:
        return ""
    return source.split(":=", 1)[1]


def declaration_reference_names(source: str, *, body_only: bool = True) -> set[str]:
    """Return qualified and unqualified declaration-like names in a Lean block."""

    haystack = declaration_body(source) if body_only else source
    names: set[str] = set()
    for match in DECLARATION_REFERENCE_RE.finditer(haystack):
        token = match.group(0)
        if not reference_name_is_specific(token):
            continue
        names.add(token)
        if "." in token:
            unqualified = token.rsplit(".", 1)[-1]
            if reference_name_is_specific(unqualified):
                names.add(unqualified)
    return names


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


def lean_files(include_active: bool) -> list[Path]:
    files: list[Path] = []
    try:
        tracked = git_ls_files()
    except subprocess.CalledProcessError:
        tracked = []
    if tracked:
        for rel in tracked:
            path = ROOT / rel
            if path.suffix != ".lean" or not path.exists():
                continue
            if not path.parts:
                continue
            if path.relative_to(ROOT).parts[0] not in {"EconCSLib", "papers"}:
                continue
            if not include_active and any(part in ACTIVE_PAPERS for part in path.parts):
                continue
            files.append(path)
        return sorted(files)

    for root in [ROOT / "EconCSLib", PAPERS]:
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


def check_sorries_in_files(files: list[Path]) -> list[Finding]:
    findings: list[Finding] = []
    sorry_re = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")
    for path in files:
        for line_no, code in lean_code_lines(path):
            if sorry_re.search(code):
                findings.append(Finding("ERROR", path, f"Lean `sorry` at line {line_no}"))
    return findings


def check_sorries(include_active: bool) -> list[Finding]:
    return check_sorries_in_files(lean_files(include_active))


def check_axiom_like_declarations_in_files(files: list[Path]) -> list[Finding]:
    """Reject declarations that can hide unproved premises from paper audits."""

    findings: list[Finding] = []
    for path in files:
        for line_no, code in lean_code_lines(path):
            stripped = code.strip()
            if AXIOM_LIKE_DECL_RE.match(stripped):
                findings.append(
                    Finding(
                        "ERROR",
                        path,
                        f"axiom-like Lean declaration at line {line_no}; route premises through "
                        "Assumptions.lean or prove the declaration",
                    )
                )
    return findings


def check_axiom_like_declarations(include_active: bool) -> list[Finding]:
    return check_axiom_like_declarations_in_files(lean_files(include_active))


def hidden_variable_premise_binders(source: str) -> list[str]:
    """Return proof-boundary binders hidden in a Lean `variable` declaration."""

    if not source.strip().startswith("variable"):
        return []
    hidden: list[str] = []
    for match in LEAN_BINDER_RE.finditer(source):
        names = _binder_names(match.group(1))
        type_text = match.group(2).strip()
        if not names:
            continue
        has_boundary_name = any(HYPOTHESIS_NAME_RE.match(name) for name in names)
        has_boundary_type = (
            VARIABLE_BOUNDARY_TYPE_RE.search(type_text) is not None
            or LIBRARY_BOUNDARY_TYPE_RE.search(type_text) is not None
        )
        if not has_boundary_name and not has_boundary_type:
            continue
        if _is_hypothesis_binder(names, type_text):
            hidden.append(normalize_premise_text(f"{' '.join(names)} : {type_text}"))
    return hidden


def check_hidden_variable_premises_in_files(files: list[Path]) -> list[Finding]:
    """Reject section-level proof premises that Lean inserts implicitly."""

    findings: list[Finding] = []
    for path in files:
        for line_no, code in lean_code_lines(path):
            hidden = hidden_variable_premise_binders(code)
            if not hidden:
                continue
            findings.append(
                Finding(
                    "ERROR",
                    path,
                    f"proof-boundary `variable` premise at line {line_no}; make it an explicit "
                    "theorem/definition parameter: "
                    + "; ".join(hidden[:4])
                    + ("; ..." if len(hidden) > 4 else ""),
                )
            )
    return findings


def check_hidden_variable_premises(include_active: bool) -> list[Finding]:
    return check_hidden_variable_premises_in_files(lean_files(include_active))


def check_guarded_checks_in_files(files: list[Path]) -> list[Finding]:
    findings: list[Finding] = []
    for path in files:
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


def check_guarded_checks(include_active: bool) -> list[Finding]:
    return check_guarded_checks_in_files(lean_files(include_active))


def paper_dirs(include_template: bool = False) -> list[Path]:
    dirs: list[Path] = []
    try:
        tracked = subprocess.run(
            ["git", "ls-files", "--", "papers/*/status.json"],
            cwd=ROOT,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ).stdout.splitlines()
    except subprocess.CalledProcessError:
        tracked = []

    if tracked:
        for rel in tracked:
            path = ROOT / rel
            if path.name == "status.json" and path.exists() and path.parent.parent == PAPERS:
                dirs.append(path.parent)
    else:
        dirs = [p for p in PAPERS.iterdir() if p.is_dir()]
    if not include_template:
        dirs = [p for p in dirs if p.name != "TEMPLATE"]
    return sorted(set(dirs))


def is_source_pdf(path: Path) -> bool:
    return path.suffix == ".pdf" and path.name not in ALLOWED_TRACKED_PAPER_PDFS


def has_source_pdf(folder: Path) -> bool:
    return any(is_source_pdf(path) for path in folder.rglob("*.pdf"))


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


def lean_declaration_blocks(
    interface_text: str,
    declaration_re: re.Pattern[str],
) -> dict[str, tuple[int, str, str]]:
    """Return syntactic Lean declaration blocks keyed by name.

    Values are `(line_number, kind, declaration_source)`.  The parser is
    intentionally syntactic and only needs enough structure for provenance and
    review-surface hygiene checks.
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
        match = declaration_re.match(line)
        if match:
            starts.append((line_number, match.group(1), match.group(2)))

    out: dict[str, tuple[int, str, str]] = {}
    for index, (line_number, kind, name) in enumerate(starts):
        next_line = starts[index + 1][0] if index + 1 < len(starts) else len(lines) + 1
        source = "\n".join(lines[line_number - 1 : next_line - 1]).strip()
        out[name] = (line_number, kind, source)
    return out


def review_declaration_blocks(interface_text: str) -> dict[str, tuple[int, str, str]]:
    """Return paper-interface theorem/lemma/def/abbrev declarations keyed by name.

    This deliberately excludes structures/classes/inductives so dashboard row
    counts stay focused on paper-facing statements and definitions.
    """

    return lean_declaration_blocks(interface_text, REVIEW_DECL_KIND_RE)


def library_declaration_blocks(interface_text: str) -> dict[str, tuple[int, str, str]]:
    """Return reusable-library declarations, including structures and classes."""

    return lean_declaration_blocks(interface_text, LIBRARY_DECL_KIND_RE)


def _leading_comment_before(lines: list[str], line_number: int) -> str:
    """Return the contiguous comment block immediately before a declaration."""

    index = line_number - 2
    while index >= 0 and not lines[index].strip():
        index -= 1
    if index < 0:
        return ""

    stripped = lines[index].strip()
    if stripped.startswith("--"):
        end = index
        while index >= 0 and lines[index].strip().startswith("--"):
            index -= 1
        return "\n".join(lines[index + 1 : end + 1]).strip()

    if "-/" in stripped:
        end = index
        while index >= 0 and "/-" not in lines[index]:
            index -= 1
        if index >= 0:
            return "\n".join(lines[index : end + 1]).strip()

    return ""


def review_declaration_comments(interface_text: str) -> dict[str, str]:
    """Return leading paper-facing comments keyed by declaration name."""

    lines = interface_text.splitlines()
    return {
        name: _leading_comment_before(lines, line_number)
        for name, (line_number, _kind, _source) in review_declaration_blocks(interface_text).items()
    }


def paper_lean_files(folder: Path) -> list[Path]:
    """Return all paper-local Lean files, including the root import file."""

    files = [path for path in folder.rglob("*.lean") if path.is_file()]
    aggregator = PAPERS / f"{folder.name}.lean"
    if aggregator.exists():
        files.append(aggregator)
    return sorted(set(files))


def paper_lean_declaration_index(folder: Path) -> dict[str, list[LeanDeclaration]]:
    """Index all declarations in a paper, not just the human interface file."""

    declarations: dict[str, list[LeanDeclaration]] = {}
    for path in paper_lean_files(folder):
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        for name, (line, kind, source) in review_declaration_blocks(text).items():
            declarations.setdefault(name, []).append(
                LeanDeclaration(path=path, line=line, kind=kind, name=name, source=source)
            )
    return declarations


def library_lean_files() -> list[Path]:
    """Return tracked reusable-library Lean files."""

    files: list[Path] = []
    try:
        tracked = git_ls_files()
    except subprocess.CalledProcessError:
        tracked = []
    if tracked:
        for rel in tracked:
            path = ROOT / rel
            if path.suffix == ".lean" and path.exists() and path.relative_to(ROOT).parts[0] == "EconCSLib":
                files.append(path)
        return sorted(files)
    root = ROOT / "EconCSLib"
    if not root.exists():
        return []
    return sorted(path for path in root.rglob("*.lean") if path.is_file())


def library_lean_declaration_index() -> dict[str, list[LeanDeclaration]]:
    """Index reusable-library declarations by unqualified and module-qualified names."""

    declarations: dict[str, list[LeanDeclaration]] = {}
    for path in library_lean_files():
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        rel = path.relative_to(ROOT).with_suffix("")
        module_name = ".".join(rel.parts)
        for name, (line, kind, source) in library_declaration_blocks(text).items():
            declaration = LeanDeclaration(path=path, line=line, kind=kind, name=name, source=source)
            declarations.setdefault(name, []).append(declaration)
            declarations.setdefault(f"{module_name}.{name}", []).append(declaration)
    return declarations


def alias_target_name(source: str) -> str | None:
    """Return the first declaration name targeted by a thin `:= @foo` alias."""

    match = ALIAS_TARGET_RE.search(source)
    if not match:
        return None
    return match.group(1)


def resolve_paper_local_target(
    declaration_index: dict[str, list[LeanDeclaration]], target_name: str | None
) -> list[LeanDeclaration]:
    """Resolve a possibly qualified target name against paper-local declarations."""

    if not target_name:
        return []
    unqualified = target_name.rsplit(".", 1)[-1]
    if target_name in declaration_index:
        return declaration_index[target_name]
    return declaration_index.get(unqualified, [])


def resolve_paper_local_alias_chain(
    declaration_index: dict[str, list[LeanDeclaration]], source: str, max_depth: int = 4
) -> list[LeanDeclaration]:
    """Follow thin local aliases far enough to inspect their real signatures."""

    seen: set[tuple[Path, int, str]] = set()
    resolved: list[LeanDeclaration] = []

    def visit(target_name: str | None, depth: int) -> None:
        if depth <= 0:
            return
        for declaration in resolve_paper_local_target(declaration_index, target_name):
            key = (declaration.path, declaration.line, declaration.name)
            if key in seen:
                continue
            seen.add(key)
            resolved.append(declaration)
            if declaration.kind in {"abbrev", "def"}:
                visit(alias_target_name(declaration.source), depth - 1)

    visit(alias_target_name(source), max_depth)
    return resolved


def assumption_finding_severity(strict_assumption_policy: bool, status: object) -> str:
    """Completed papers should not hide proof-boundary premises."""

    if status not in {"formalized", "formalized with caveat"}:
        return "WARN"
    if strict_assumption_policy:
        return "ERROR"
    return "ERROR"


def completed_status_finding_severity(status: object) -> str:
    """Completed paper claims should satisfy the strict review-surface checks."""

    if status in {"formalized", "formalized with caveat"}:
        return "ERROR"
    return "WARN"


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


def is_assumption_decl_name(name: str) -> bool:
    """Return whether a declaration name is meant to be a paper assumption."""

    return bool(ASSUMPTION_DECL_NAME_RE.search(name))


def review_surface_assumption_names(review_surface: dict[str, object]) -> tuple[set[str], list[str]]:
    """Read the explicit paper-assumption ledger from status.json review_surface."""

    raw = review_surface.get("assumption_names")
    if raw is None:
        return set(), []
    if not isinstance(raw, list):
        return set(), ["`review_surface.assumption_names` should be a string list"]
    names: set[str] = set()
    problems: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            problems.append(f"`review_surface.assumption_names[{index}]` should be a nonempty string")
            continue
        names.add(value.strip())
    return names, problems


def assumption_source_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-local Lean file that declares reviewed assumptions."""

    raw_path = review_surface.get("assumption_source_file")
    if isinstance(raw_path, str) and raw_path.strip():
        return ROOT / raw_path.strip()
    return folder / DEFAULT_ASSUMPTION_SOURCE_FILE


def assumption_judgment_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-root LLM assumption-provenance judgment file."""

    llm_assumption_review = review_surface.get("llm_assumption_review")
    if isinstance(llm_assumption_review, dict):
        raw_path = llm_assumption_review.get("assumption_judgment_file")
        if isinstance(raw_path, str) and raw_path.strip():
            return ROOT / raw_path.strip()
    return folder / DEFAULT_LLM_ASSUMPTION_JUDGE_FILE


def assumption_declarations_from_file(path: Path) -> dict[str, tuple[int, str, str]]:
    """Return assumption declarations from a paper-local Assumptions.lean file."""

    if not path.exists() or not path.is_file():
        return {}
    try:
        declarations = review_declaration_blocks(path.read_text(encoding="utf-8"))
    except OSError:
        return {}
    return {
        name: declaration
        for name, declaration in declarations.items()
        if is_assumption_decl_name(name)
    }


def assumption_premises_from_file(path: Path) -> dict[str, set[str]]:
    """Read `-- audit-premise: ...` comments attached to assumption declarations."""

    if not path.exists() or not path.is_file():
        return {}
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {}
    pending: list[str] = []
    block_depth = 0
    out: dict[str, set[str]] = {}
    for line in lines:
        premise_match = ASSUMPTION_AUDIT_PREMISE_RE.match(line)
        if premise_match:
            pending.append(normalize_premise_text(premise_match.group(1)))
            continue
        declaration_match = REVIEW_DECL_KIND_RE.match(line)
        if not declaration_match:
            stripped = line.strip()
            if "/-" in line:
                block_depth += line.count("/-")
            if "-/" in line:
                block_depth = max(0, block_depth - line.count("-/"))
            if (
                pending
                and stripped
                and block_depth == 0
                and not line.lstrip().startswith(("--", "/--", "/-", "*", "-/"))
            ):
                pending = []
            continue
        name = declaration_match.group(2)
        if is_assumption_decl_name(name) and pending:
            out.setdefault(name, set()).update(pending)
        pending = []
    return out


def normalize_assumption_judgment(raw: object) -> str:
    """Normalize source-assumption judge verdicts."""

    if isinstance(raw, bool):
        return "paper_assumption" if raw else "not_paper_assumption"
    value = str(raw or "").strip().lower()
    if value in {
        "paper_assumption",
        "paper assumption",
        "matches",
        "match",
        "yes",
        "true",
        "source_assumption",
        "source assumption",
        "model_assumption",
        "model assumption",
    }:
        return "paper_assumption"
    if value in {
        "source_text",
        "source text",
        "source_text_assumption",
        "source text assumption",
        "source_text_condition",
        "source text condition",
    }:
        return "source_text"
    if value in {
        "source_text_model_primitive",
        "source text model primitive",
        "source_model_primitive",
        "source model primitive",
        "model_primitive",
        "model primitive",
    }:
        return "source_text_model_primitive"
    if value in {
        "derived_from_source_primitives",
        "derived from source primitives",
        "derived_in_lean",
        "derived in lean",
        "derived",
    }:
        return "derived_from_source_primitives"
    if value in {
        "paper_condition",
        "paper condition",
        "source_condition",
        "source condition",
        "statement_condition",
        "statement condition",
        "theorem_condition",
        "theorem condition",
        "paper_statement_condition",
        "paper statement condition",
    }:
        return "paper_condition"
    if value in {
        "documented_caveat",
        "documented caveat",
        "paper_caveat",
        "paper caveat",
        "source_caveat",
        "source caveat",
        "repair_condition",
        "repair condition",
    }:
        return "documented_caveat"
    if value in {
        "partial_boundary",
        "partial boundary",
        "partial_formalization_boundary",
        "partial formalization boundary",
        "unresolved_boundary",
        "unresolved boundary",
        "needs_derivation",
        "needs derivation",
    }:
        return "partial_boundary"
    if value in {
        "not_paper_assumption",
        "not paper assumption",
        "proof_assumption",
        "proof assumption",
        "not_in_paper",
        "not in paper",
        "not_source_text",
        "not source text",
        "not_source",
        "not source",
        "mismatch",
        "no",
        "false",
    }:
        return "not_paper_assumption"
    if value in {"uncertain", "unknown", "unsure", "needs_review", "needs review", "partial"}:
        return "uncertain"
    return value


def normalize_premise_text(text: str) -> str:
    """Normalize a theorem-premise string for assumption-ledger matching."""

    return re.sub(r"\s+", " ", str(text or "").strip())


def _premises_from_raw_value(raw_value: object) -> set[str]:
    """Extract exact theorem-premise strings from an assumption judgment item."""

    premises: set[str] = set()
    if not isinstance(raw_value, dict):
        return premises
    raw_premises = (
        raw_value.get("premises")
        or raw_value.get("lean_premises")
        or raw_value.get("audit_premises")
        or raw_value.get("theorem_premises")
    )
    if isinstance(raw_premises, str):
        raw_premises = [raw_premises]
    if isinstance(raw_premises, list):
        for premise in raw_premises:
            normalized = normalize_premise_text(str(premise))
            if normalized:
                premises.add(normalized)
    return premises


def _premise_judgments_from_raw_value(raw_value: object) -> dict[str, dict[str, object]]:
    """Extract per-premise source/provenance judgments from an assumption item."""

    if not isinstance(raw_value, dict):
        return {}
    raw_items = (
        raw_value.get("premise_judgments")
        or raw_value.get("premise_items")
        or raw_value.get("premise_validations")
        or raw_value.get("premises_judged")
    )
    out: dict[str, dict[str, object]] = {}

    def add_item(premise: object, raw_item: object) -> None:
        normalized_premise = normalize_premise_text(str(premise or ""))
        if not normalized_premise:
            return
        if isinstance(raw_item, dict):
            raw_judgment = (
                raw_item.get("judgment")
                or raw_item.get("verdict")
                or raw_item.get("status")
                or raw_item.get("source_text_judgment")
            )
            out[normalized_premise] = {
                "judgment": normalize_assumption_judgment(raw_judgment),
                "reason": str(
                    raw_item.get("reason")
                    or raw_item.get("notes")
                    or raw_item.get("explanation")
                    or ""
                ).strip(),
                "source_location": str(raw_item.get("source_location") or "").strip(),
            }
        else:
            out[normalized_premise] = {
                "judgment": normalize_assumption_judgment(raw_item),
                "reason": "",
                "source_location": "",
            }

    if isinstance(raw_items, dict):
        for premise, raw_item in raw_items.items():
            add_item(premise, raw_item)
    elif isinstance(raw_items, list):
        for raw_item in raw_items:
            if isinstance(raw_item, dict):
                add_item(raw_item.get("premise"), raw_item)
            else:
                add_item(raw_item, "uncertain")
    return out


def load_assumption_judgments(path: Path, paper_id: str) -> dict[str, dict[str, object]]:
    """Load paper-assumption provenance judgments keyed by declaration name."""

    if not path.exists() or not path.is_file():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, paper_id}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, dict[str, str]] = {}
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if not name:
            continue
        if isinstance(raw_value, dict):
            raw_judgment = (
                raw_value.get("judgment")
                or raw_value.get("verdict")
                or raw_value.get("status")
                or raw_value.get("paper_assumption")
            )
            out[name] = {
                "judgment": normalize_assumption_judgment(raw_judgment),
                "reason": str(
                    raw_value.get("reason")
                    or raw_value.get("notes")
                    or raw_value.get("explanation")
                    or ""
                ).strip(),
                "premises": sorted(_premises_from_raw_value(raw_value)),
                "premise_judgments": _premise_judgments_from_raw_value(raw_value),
            }
        else:
            out[name] = {
                "judgment": normalize_assumption_judgment(raw_value),
                "reason": "",
                "premises": [],
                "premise_judgments": {},
            }
    return out


def declaration_header(source: str) -> str:
    """Return the declaration signature before the proof/body."""

    head = source.split(":=", 1)[0]
    head = head.split(" where", 1)[0]
    return re.sub(r"\s+", " ", head).strip()


def _binder_names(raw_names: str) -> list[str]:
    """Split Lean binder name groups, dropping common binder modifiers."""

    names = []
    for chunk in re.split(r"\s+", raw_names.strip()):
        name = chunk.strip()
        if not name or name in {"_", "inst"}:
            continue
        if name.startswith("[") or name.endswith("]"):
            continue
        names.append(name)
    return names


def _is_hypothesis_binder(names: list[str], type_text: str) -> bool:
    """Heuristic for binders that represent assumptions/proof boundaries."""

    normalized_type = f" {type_text.strip()} "
    non_arrow_proposition_like = (
        any(marker in normalized_type for marker in NON_ARROW_PROPOSITION_TYPE_MARKERS)
        or PREDICATE_TYPE_WORD_RE.search(type_text) is not None
    )
    if "→" in type_text and not type_text.strip().endswith("Prop") and not non_arrow_proposition_like:
        return False
    proposition_like = (
        any(marker in normalized_type for marker in PROPOSITION_TYPE_MARKERS)
        or PREDICATE_TYPE_WORD_RE.search(type_text) is not None
    )
    if any(HYPOTHESIS_NAME_RE.match(name) for name in names):
        return proposition_like or PROOF_BOUNDARY_TYPE_RE.search(type_text) is not None
    if PROOF_BOUNDARY_TYPE_RE.search(type_text):
        return not DATA_PARAMETER_TYPE_RE.match(type_text)
    return False


def hidden_premise_binders(source: str, assumption_names: set[str]) -> list[str]:
    """Return theorem binders that do not route through explicit assumption rows."""

    header = declaration_header(source)
    hidden: list[str] = []
    for match in LEAN_BINDER_RE.finditer(header):
        names = _binder_names(match.group(1))
        type_text = match.group(2).strip()
        if not names or not _is_hypothesis_binder(names, type_text):
            continue
        if any(name in assumption_names for name in names):
            continue
        if any(assumption in type_text for assumption in assumption_names):
            continue
        hidden.append(normalize_premise_text(f"{' '.join(names)} : {type_text}"))
    return hidden


def explicit_boundary_premises(premises: list[str]) -> list[str]:
    """Return visible premises that are still proof/provenance boundaries."""

    return [
        premise
        for premise in premises
        if REVIEW_EXPLICIT_BOUNDARY_RE.search(premise)
        or LIBRARY_EXTERNAL_BOUNDARY_RE.search(premise)
    ]


def library_boundary_binders(source: str) -> list[tuple[str, str]]:
    """Return certificate/source-boundary-shaped binders from a library declaration.

    Library theorem hypotheses are usually legitimate mathematical preconditions.
    This classifier intentionally reports only certificate-like, source-row-like,
    or external-boundary-like parameters that paper wrappers must discharge before
    being called fully formalized.
    """

    header = declaration_header(source)
    boundaries: list[tuple[str, str]] = []
    for match in LEAN_BINDER_RE.finditer(header):
        names = _binder_names(match.group(1))
        type_text = match.group(2).strip()
        if not names:
            continue
        premise = normalize_premise_text(f"{' '.join(names)} : {type_text}")
        joined_names = " ".join(names)
        haystack = f"{joined_names} {type_text}"
        if LIBRARY_EXTERNAL_BOUNDARY_RE.search(haystack):
            boundaries.append(("external", premise))
            continue
        if LIBRARY_BOUNDARY_TYPE_RE.search(type_text) or LIBRARY_CERTIFICATE_BOUNDARY_RE.search(joined_names):
            boundaries.append(("certificate", premise))
            continue
        if re.search(r"\bsource\b", haystack, re.I) and re.search(r"\b(?:row|table|formula|equation|surface)\b", haystack, re.I):
            boundaries.append(("source-row", premise))
            continue
    return boundaries


def resolve_library_target(
    declaration_index: dict[str, list[LeanDeclaration]], target_name: str | None
) -> list[LeanDeclaration]:
    """Resolve a thin alias target against reusable-library declarations."""

    if not target_name:
        return []
    candidates: list[LeanDeclaration] = []
    if target_name in declaration_index:
        candidates.extend(declaration_index[target_name])
    unqualified = target_name.rsplit(".", 1)[-1]
    candidates.extend(declaration_index.get(unqualified, []))
    seen: set[tuple[Path, int, str]] = set()
    out: list[LeanDeclaration] = []
    for declaration in candidates:
        key = (declaration.path, declaration.line, declaration.name)
        if key in seen:
            continue
        seen.add(key)
        out.append(declaration)
    return out


def unique_declarations(
    declaration_index: dict[str, list[LeanDeclaration]]
) -> list[LeanDeclaration]:
    """Return declarations from an index without qualified-name duplicates."""

    seen: set[tuple[Path, int, str]] = set()
    out: list[LeanDeclaration] = []
    for declarations in declaration_index.values():
        for declaration in declarations:
            key = declaration_key(declaration)
            if key in seen:
                continue
            seen.add(key)
            out.append(declaration)
    return out


def _boundary_dependency_key(
    dependency: BoundaryDependency,
) -> tuple[str, str, Path, int, str]:
    declaration = dependency.declaration
    return (
        dependency.category,
        dependency.premise,
        declaration.path,
        declaration.line,
        declaration.name,
    )


def dedupe_boundary_dependencies(
    dependencies: list[BoundaryDependency],
) -> list[BoundaryDependency]:
    seen: set[tuple[str, str, Path, int, str]] = set()
    out: list[BoundaryDependency] = []
    for dependency in dependencies:
        key = _boundary_dependency_key(dependency)
        if key in seen:
            continue
        seen.add(key)
        out.append(dependency)
    return out


def paper_local_reference_target_map(
    declarations: list[LeanDeclaration],
    declaration_index: dict[str, list[LeanDeclaration]],
) -> dict[tuple[Path, int, str], list[LeanDeclaration]]:
    """Resolve paper-local declaration references once for fixed-point scans."""

    out: dict[tuple[Path, int, str], list[LeanDeclaration]] = {}
    for declaration in declarations:
        targets: list[LeanDeclaration] = []
        seen: set[tuple[Path, int, str]] = set()
        for reference in declaration_reference_names(declaration.source):
            for target in resolve_paper_local_target(declaration_index, reference):
                key = declaration_key(target)
                if key == declaration_key(declaration) or key in seen:
                    continue
                seen.add(key)
                targets.append(target)
        out[declaration_key(declaration)] = targets
    return out


def source_reference_library_boundary_dependencies(
    source: str,
    library_declaration_index: dict[str, list[LeanDeclaration]],
    library_boundary_dependency_index: dict[tuple[Path, int, str], list[BoundaryDependency]],
) -> list[BoundaryDependency]:
    """Return certificate dependencies of library declarations referenced by `source`."""

    dependencies: list[BoundaryDependency] = []
    seen_targets: set[tuple[Path, int, str]] = set()
    for reference in declaration_reference_names(source):
        for target in resolve_library_target(library_declaration_index, reference):
            target_key = declaration_key(target)
            if target_key in seen_targets:
                continue
            seen_targets.add(target_key)
            for dependency in library_boundary_dependency_index.get(target_key, []):
                dependencies.append(
                    BoundaryDependency(
                        category=dependency.category,
                        premise=dependency.premise,
                        declaration=dependency.declaration,
                        via=target.name,
                    )
                )
    return dedupe_boundary_dependencies(dependencies)


def library_boundary_dependency_index(
    declaration_index: dict[str, list[LeanDeclaration]],
) -> dict[tuple[Path, int, str], list[BoundaryDependency]]:
    """Propagate reusable-library certificate/source boundaries through calls.

    Direct boundary binders mark a declaration immediately.  A fixed point over
    lexical declaration references then marks reusable helpers that call such
    APIs.  The index is rebuilt from current Lean files on each audit run, so it
    cannot go stale like a checked-in dependency manifest.
    """

    declarations = unique_declarations(declaration_index)
    dependencies: dict[tuple[Path, int, str], list[BoundaryDependency]] = {}
    for declaration in declarations:
        direct = [
            BoundaryDependency(
                category=category,
                premise=premise,
                declaration=declaration,
                via=declaration.name,
            )
            for category, premise in library_boundary_binders(declaration.source)
        ]
        if direct:
            dependencies[declaration_key(declaration)] = direct

    changed = True
    while changed:
        changed = False
        for declaration in declarations:
            key = declaration_key(declaration)
            current = dependencies.get(key, [])
            propagated = source_reference_library_boundary_dependencies(
                declaration.source,
                declaration_index,
                dependencies,
            )
            merged = dedupe_boundary_dependencies(current + propagated)
            if len(merged) != len(current):
                dependencies[key] = merged
                changed = True
    return dependencies


def paper_boundary_dependency_index(
    declaration_index: dict[str, list[LeanDeclaration]],
    library_declaration_index: dict[str, list[LeanDeclaration]],
    library_boundary_dependencies: dict[tuple[Path, int, str], list[BoundaryDependency]],
) -> dict[tuple[Path, int, str], list[BoundaryDependency]]:
    """Propagate library boundary dependencies through paper-local wrappers."""

    declarations = unique_declarations(declaration_index)
    reference_targets = paper_local_reference_target_map(declarations, declaration_index)
    dependencies: dict[tuple[Path, int, str], list[BoundaryDependency]] = {}
    for declaration in declarations:
        direct = source_reference_library_boundary_dependencies(
            declaration.source,
            library_declaration_index,
            library_boundary_dependencies,
        )
        if direct:
            dependencies[declaration_key(declaration)] = direct

    changed = True
    while changed:
        changed = False
        for declaration in declarations:
            key = declaration_key(declaration)
            current = dependencies.get(key, [])
            propagated: list[BoundaryDependency] = []
            for target in reference_targets.get(key, []):
                target_key = declaration_key(target)
                for dependency in dependencies.get(target_key, []):
                    propagated.append(
                        BoundaryDependency(
                            category=dependency.category,
                            premise=dependency.premise,
                            declaration=dependency.declaration,
                            via=target.name,
                        )
                    )
            merged = dedupe_boundary_dependencies(current + propagated)
            if len(merged) != len(current):
                dependencies[key] = merged
                changed = True
    return dependencies


def paper_hidden_premise_dependency_index(
    declaration_index: dict[str, list[LeanDeclaration]],
    assumption_names: set[str],
) -> dict[tuple[Path, int, str], list[BoundaryDependency]]:
    """Propagate paper-local certificate/source-boundary premises.

    Direct certificate/source-row/external binders mark a declaration
    immediately.  A fixed point over body references then marks wrappers that
    depend on helpers with such boundary premises.  Ordinary mathematical side
    conditions are not propagated here: a caller may derive them from stronger
    visible source conditions, and the paper-facing statement judge is
    responsible for validating those visible conditions.
    """

    declarations = unique_declarations(declaration_index)
    reference_targets = paper_local_reference_target_map(declarations, declaration_index)
    dependencies: dict[tuple[Path, int, str], list[BoundaryDependency]] = {}
    for declaration in declarations:
        if declaration.name in assumption_names or is_assumption_decl_name(declaration.name):
            continue
        direct_hidden = hidden_premise_binders(declaration.source, assumption_names)
        direct = [
            BoundaryDependency(
                category="paper-premise",
                premise=premise,
                declaration=declaration,
                via=declaration.name,
            )
            for premise in explicit_boundary_premises(direct_hidden)
        ]
        if direct:
            dependencies[declaration_key(declaration)] = direct

    changed = True
    while changed:
        changed = False
        for declaration in declarations:
            key = declaration_key(declaration)
            current = dependencies.get(key, [])
            propagated: list[BoundaryDependency] = []
            for target in reference_targets.get(key, []):
                target_key = declaration_key(target)
                for dependency in dependencies.get(target_key, []):
                    propagated.append(
                        BoundaryDependency(
                            category=dependency.category,
                            premise=dependency.premise,
                            declaration=dependency.declaration,
                            via=target.name,
                        )
                    )
            merged = dedupe_boundary_dependencies(current + propagated)
            if len(merged) != len(current):
                dependencies[key] = merged
                changed = True
    return dependencies


def source_specific_library_smells(declaration: LeanDeclaration) -> list[str]:
    """Heuristically flag source-shaped formulas living in the reusable library."""

    reasons: list[str] = []
    name = declaration.name
    header = declaration_header(declaration.source)
    if SOURCE_SHAPED_LIBRARY_NAME_RE.search(name):
        reasons.append("source/paper-shaped reusable declaration name")
    if re.search(r"(?:^|_)(?:paper|displayed|appendix)(?:_|$)", name, re.I):
        reasons.append("paper/displayed-shaped declaration name")
    if re.search(r"(?:^|_)source(?:_|$).*(?:row|formula|equation|surface|displayed|paper)", name, re.I):
        reasons.append("source-row/formula-shaped declaration name")
    if re.search(r"(?:^|_)(?:theorem|thm|lemma|lem|proposition|prop|corollary|claim)[A-Z]?\d+", name, re.I):
        reasons.append("numbered-paper-result-shaped declaration name")
    if re.search(r"\bSource status\s*:", declaration.source, re.I):
        reasons.append("paper-review provenance text appears inside library declaration")
    if re.search(r"\b(?:paper|displayed)\b", header, re.I) and FORMULA_SPECIFIC_NAME_RE.search(header):
        reasons.append("source-shaped formula appears in declaration signature")
    return reasons


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


def check_machine_paper_status(library_premise_audit: bool = False) -> list[Finding]:
    findings: list[Finding] = []
    library_declaration_index = library_lean_declaration_index()
    library_boundary_dependencies = (
        library_boundary_dependency_index(library_declaration_index)
        if library_premise_audit
        else {}
    )
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
        assumption_names, assumption_name_problems = review_surface_assumption_names(review_surface)
        for problem in assumption_name_problems:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` {problem}"))
        assumption_policy = str(review_surface.get("assumption_policy") or "").strip().lower()
        strict_assumption_policy = assumption_policy in ASSUMPTION_POLICY_STRICT_VALUES
        if assumption_policy and not strict_assumption_policy:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}.review_surface.assumption_policy` should be one of "
                    + ", ".join(sorted(ASSUMPTION_POLICY_STRICT_VALUES)),
                )
            )

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
        declaration_comments = review_declaration_comments(interface_text)
        declaration_index = paper_lean_declaration_index(PAPERS / paper_id)
        paper_hidden_premise_dependencies = paper_hidden_premise_dependency_index(
            declaration_index,
            assumption_names,
        )
        paper_boundary_dependencies = (
            paper_boundary_dependency_index(
                declaration_index,
                library_declaration_index,
                library_boundary_dependencies,
            )
            if library_premise_audit
            else {}
        )
        assumption_source_file = assumption_source_file_path(PAPERS / paper_id, review_surface)
        assumption_declarations = assumption_declarations_from_file(assumption_source_file)
        assumption_file_premises = assumption_premises_from_file(assumption_source_file)
        assumption_judgments: dict[str, dict[str, object]] = {}
        validated_assumption_premises: set[str] = set()
        hidden_premise_finding_keys: set[tuple[Path, int, str, str, tuple[str, ...]]] = set()
        hidden_premise_severity = assumption_finding_severity(strict_assumption_policy, status)

        def add_hidden_premise_finding(
            declaration: LeanDeclaration, hidden: list[str], context: str
        ) -> None:
            hidden = list(dict.fromkeys(
                premise
                for premise in hidden
                if normalize_premise_text(premise) not in validated_assumption_premises
            ))
            if not hidden:
                return
            key = (declaration.path, declaration.line, declaration.name, context, tuple(hidden))
            if key in hidden_premise_finding_keys:
                return
            hidden_premise_finding_keys.add(key)
            findings.append(
                Finding(
                    hidden_premise_severity,
                    declaration.path,
                    f"`{paper_id}` {context} `{declaration.name}` at line {declaration.line} "
                    "has premises not routed through explicit Assumptions.lean paper assumptions: "
                    + "; ".join(hidden[:4])
                    + ("; ..." if len(hidden) > 4 else ""),
                )
            )

        recorded_line_count = interface.get("line_count")
        if recorded_line_count != actual_line_count:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` line_count is {recorded_line_count}, expected {actual_line_count}",
                )
            )
        discovered_assumptions = {
            name for name in actual_review_names if is_assumption_decl_name(name)
        }
        discovered_assumptions.update(assumption_declarations)
        unlisted_assumptions = discovered_assumptions - assumption_names
        if unlisted_assumptions:
            findings.append(
                Finding(
                    "ERROR" if strict_assumption_policy else "WARN",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` has assumption-like declarations not listed in "
                    "`review_surface.assumption_names`: "
                    + ", ".join(sorted(unlisted_assumptions)),
                )
            )
        declared_assumption_names = set(actual_review_names) | set(assumption_declarations)
        missing_assumption_rows = assumption_names - declared_assumption_names
        if missing_assumption_rows:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` assumption_names are not exported by PaperInterface.lean or "
                    f"{assumption_source_file.relative_to(ROOT)}: "
                    + ", ".join(sorted(missing_assumption_rows)),
                )
            )
        if assumption_names and not assumption_source_file.exists() and not any(
            name in actual_review_names for name in assumption_names
        ):
            findings.append(
                Finding(
                    "ERROR" if strict_assumption_policy else "WARN",
                    assumption_source_file,
                    f"`{paper_id}` lists assumptions but has no `{DEFAULT_ASSUMPTION_SOURCE_FILE}` "
                    "or legacy PaperInterface assumption declarations",
                )
            )
        if assumption_names:
            assumption_judge_file = assumption_judgment_file_path(interface_path.parent, review_surface)
            if not assumption_judge_file.exists():
                findings.append(
                    Finding(
                        "ERROR" if strict_assumption_policy else "WARN",
                        assumption_judge_file,
                        f"`{paper_id}` has explicit paper assumptions but no assumption-provenance LLM judge file",
                    )
                )
                assumption_judgments = {}
            else:
                assumption_judgments = load_assumption_judgments(assumption_judge_file, paper_id)
                if not assumption_judgments:
                    findings.append(
                        Finding(
                            "ERROR" if strict_assumption_policy else "WARN",
                            assumption_judge_file,
                            f"`{paper_id}` assumption judge file is missing schema-1 judgments",
                        )
                    )
            for assumption_name in sorted(assumption_names):
                judgment = assumption_judgments.get(assumption_name, {}).get("judgment", "")
                if judgment not in APPROVED_ASSUMPTION_JUDGMENTS:
                    findings.append(
                        Finding(
                            "ERROR" if strict_assumption_policy else "WARN",
                            assumption_judge_file,
                            f"`{paper_id}` assumption `{assumption_name}` lacks a current "
                            "`paper_assumption`, `paper_condition`, `documented_caveat`, "
                            "or `partial_boundary` "
                            "LLM provenance judgment",
                        )
                    )
                else:
                    if judgment == "partial_boundary" and status in {"formalized", "formalized with caveat"}:
                        findings.append(
                            Finding(
                                "ERROR",
                                assumption_judge_file,
                                f"`{paper_id}` assumption `{assumption_name}` is marked as a "
                                "partial-formalization boundary, but the paper status is "
                                f"`{status}`",
                            )
                        )
                    premise_judgments = assumption_judgments.get(assumption_name, {}).get(
                        "premise_judgments", {}
                    )
                    if not isinstance(premise_judgments, dict):
                        premise_judgments = {}
                    expected_premises = {
                        normalize_premise_text(premise)
                        for premise in assumption_file_premises.get(assumption_name, set())
                    }
                    judged_premises = {
                        normalize_premise_text(premise)
                        for premise in premise_judgments
                        if normalize_premise_text(premise)
                    }
                    missing_premise_judgments = sorted(expected_premises - judged_premises)
                    if missing_premise_judgments:
                        findings.append(
                            Finding(
                                "ERROR" if strict_assumption_policy else "WARN",
                                assumption_judge_file,
                                f"`{paper_id}` assumption `{assumption_name}` lacks per-premise "
                                "source-text judgments for: "
                                + "; ".join(missing_premise_judgments[:4])
                                + ("; ..." if len(missing_premise_judgments) > 4 else ""),
                            )
                        )
                    extra_premise_judgments = sorted(judged_premises - expected_premises)
                    if extra_premise_judgments:
                        findings.append(
                            Finding(
                                "WARN",
                                assumption_judge_file,
                                f"`{paper_id}` assumption `{assumption_name}` has per-premise "
                                "judgments that do not match current Assumptions.lean premises: "
                                + "; ".join(extra_premise_judgments[:4])
                                + ("; ..." if len(extra_premise_judgments) > 4 else ""),
                            )
                        )
                    for premise in sorted(expected_premises & judged_premises):
                        raw_premise_judgment = premise_judgments.get(premise)
                        if raw_premise_judgment is None:
                            for key, value in premise_judgments.items():
                                if normalize_premise_text(key) == premise:
                                    raw_premise_judgment = value
                                    break
                        if not isinstance(raw_premise_judgment, dict):
                            premise_judgment = normalize_assumption_judgment(raw_premise_judgment)
                            source_location = ""
                        else:
                            premise_judgment = normalize_assumption_judgment(
                                raw_premise_judgment.get("judgment")
                                or raw_premise_judgment.get("verdict")
                                or raw_premise_judgment.get("status")
                            )
                            source_location = str(raw_premise_judgment.get("source_location") or "").strip()
                        if premise_judgment not in APPROVED_ASSUMPTION_PREMISE_JUDGMENTS:
                            findings.append(
                                Finding(
                                    "ERROR" if strict_assumption_policy else "WARN",
                                    assumption_judge_file,
                                    f"`{paper_id}` assumption `{assumption_name}` premise `{premise}` "
                                    f"has non-source or unresolved judgment `{premise_judgment or 'missing'}`",
                                )
                            )
                            continue
                        if premise_judgment == "partial_boundary":
                            findings.append(
                                Finding(
                                    "ERROR" if status in {"formalized", "formalized with caveat"} else "WARN",
                                    assumption_judge_file,
                                    f"`{paper_id}` assumption `{assumption_name}` premise `{premise}` "
                                    "is a visible partial-formalization boundary, not a source-text assumption",
                                )
                            )
                            if status not in {"formalized", "formalized with caveat"}:
                                validated_assumption_premises.add(premise)
                            continue
                        if premise_judgment in {
                            "paper_assumption",
                            "paper_condition",
                            "source_text",
                            "source_text_model_primitive",
                        } and not source_location:
                            findings.append(
                                Finding(
                                    "ERROR" if strict_assumption_policy else "WARN",
                                    assumption_judge_file,
                                    f"`{paper_id}` assumption `{assumption_name}` premise `{premise}` "
                                    "needs a source_location for its source-text judgment",
                                )
                            )
                            continue
                        validated_assumption_premises.add(premise)
        elif strict_assumption_policy:
            llm_assumption_review = review_surface.get("llm_assumption_review")
            if not isinstance(llm_assumption_review, dict):
                findings.append(
                    Finding(
                        "WARN",
                        PAPER_STATUS_FILE,
                        f"`{paper_id}` strict assumption policy should declare "
                        "`review_surface.llm_assumption_review` even when there are no assumptions",
                    )
                )
        for name in include_names:
            declaration = declaration_blocks.get(name)
            if not declaration:
                continue
            line_no, kind, source = declaration
            leading_comment = declaration_comments.get(name, "")
            comment_and_name = f"{leading_comment}\n{name}"
            numbered_result_row = bool(
                NUMBERED_SOURCE_RESULT_RE.search(leading_comment)
                or NUMBERED_SOURCE_NAME_RE.search(name)
            )
            broad_review_row = bool(BROAD_REVIEW_ROW_NAME_RE.search(name))
            formula_specific_row = bool(FORMULA_SPECIFIC_NAME_RE.search(name))
            definition_review_row = bool(re.match(r"^definition[A-Z0-9_]", name, re.I))
            formula_facing_row = bool(
                not definition_review_row
                and (SOURCE_FORMULA_TEXT_RE.search(leading_comment) or formula_specific_row)
            )
            if numbered_result_row and broad_review_row and not formula_specific_row:
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        interface_path,
                        f"`{paper_id}` review row `{name}` at line {line_no} appears to summarize a "
                        "numbered source result with a broad aggregate name; split displayed formulas, "
                        "subclaims, and source-defining equations into exact paper-facing rows before "
                        "claiming the result is fully formalized",
                    )
                )
            if formula_facing_row and leading_comment and not SOURCE_STATUS_LINE_RE.search(leading_comment):
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        interface_path,
                        f"`{paper_id}` formula-bearing review row `{name}` at line {line_no} "
                        "has no `Source status:` provenance line in its paper-facing comment",
                    )
                )
            if (
                formula_facing_row
                and is_signature_only_review_alias(kind, source)
                and not formula_specific_row
            ):
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        interface_path,
                        f"`{paper_id}` formula-bearing review row `{name}` at line {line_no} is an "
                        "opaque alias/signature; expose the displayed formula or theorem subclaim "
                        "directly, or route any non-derived premise through Assumptions.lean",
                    )
                )
            if formula_facing_row and re.search(r"source[-_ ]rows?", comment_and_name, re.I):
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        interface_path,
                        f"`{paper_id}` review row `{name}` at line {line_no} mentions a source-row "
                        "formula boundary; source-row wrappers are partial endpoints unless derived "
                        "from primitives or validated as explicit paper assumptions",
                    )
            )
            if kind in {"theorem", "lemma", "def", "abbrev"} and name not in assumption_names and not is_assumption_decl_name(name):
                row_declaration = LeanDeclaration(
                    path=interface_path,
                    line=line_no,
                    kind=kind,
                    name=name,
                    source=source,
                )
                row_key = declaration_key(row_declaration)
                visible_premises = {
                    normalize_premise_text(premise)
                    for premise in hidden_premise_binders(source, assumption_names)
                }
                visible_statement_premises = {
                    premise
                    for premise in visible_premises
                    if not explicit_boundary_premises([premise])
                }
                direct_boundary_premises = explicit_boundary_premises(
                    sorted(visible_premises)
                )
                if direct_boundary_premises:
                    add_hidden_premise_finding(
                        row_declaration,
                        direct_boundary_premises,
                        "review row",
                    )
                alias_targets = resolve_paper_local_alias_chain(declaration_index, source)
                alias_target_keys = {declaration_key(target) for target in alias_targets}
                directly_reported_keys = {row_key} | alias_target_keys
                for target_declaration in alias_targets:
                    if target_declaration.name in assumption_names or is_assumption_decl_name(target_declaration.name):
                        continue
                    target_hidden = [
                        premise
                        for premise in hidden_premise_binders(
                            target_declaration.source, assumption_names
                        )
                        if normalize_premise_text(premise) not in visible_statement_premises
                    ]
                    if target_hidden:
                        add_hidden_premise_finding(
                            target_declaration,
                            target_hidden,
                            f"review row `{name}` resolves to",
                        )
                transitive_hidden_dependencies = [
                    dependency
                    for dependency in paper_hidden_premise_dependencies.get(row_key, [])
                    if declaration_key(dependency.declaration) not in directly_reported_keys
                    and normalize_premise_text(dependency.premise)
                    not in visible_statement_premises
                ]
                if transitive_hidden_dependencies:
                    add_hidden_premise_finding(
                        row_declaration,
                        [dependency.premise for dependency in transitive_hidden_dependencies],
                        "review row transitively depends on paper-local hidden premise",
                    )
                if library_premise_audit:
                    row_boundary_dependencies = paper_boundary_dependencies.get(
                        (interface_path, line_no, name),
                        [],
                    )
                    if row_boundary_dependencies:
                        add_hidden_premise_finding(
                            row_declaration,
                            [dependency.premise for dependency in row_boundary_dependencies],
                            "review row transitively depends on library boundary API",
                        )
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
                "top-level README should include a concise human status table: `Paper | Status | Review | Interface | Human summary`",
            )
        )
        return findings

    if len(matching_tables) > 1:
        findings.append(Finding("WARN", readme, "top-level README has multiple human status tables"))

    header, rows = matching_tables[0]
    paper_idx = header.index("Paper")
    status_idx = header.index("Status")
    review_idx = header.index("Review")
    interface_idx = header.index("Interface")
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
        if path.suffix == ".pdf" and path.name not in ALLOWED_TRACKED_PAPER_PDFS:
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
                "top-level README should use the concise `Paper | Status | Review | Interface | Human summary` table, not the full paper ledger",
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


def check_library_certificate_boundaries() -> list[Finding]:
    """List reusable-library APIs that require explicit certificates/boundaries.

    These are not errors by themselves. Library theorems may and often should
    require source-shaped certificates. The important invariant is that a paper
    wrapper cannot be marked fully formalized while leaving such a certificate
    to its caller unless that certificate is a validated paper assumption.
    """

    findings: list[Finding] = []
    seen: set[tuple[Path, int, str]] = set()
    declaration_index = library_lean_declaration_index()
    boundary_dependency_index = library_boundary_dependency_index(declaration_index)
    for declaration in unique_declarations(declaration_index):
        key = declaration_key(declaration)
        if key in seen:
            continue
        seen.add(key)
        if re.match(r"\s*private\s+", declaration.source):
            continue
        boundaries = library_boundary_binders(declaration.source)
        if boundaries:
            samples = [f"{category}: {premise}" for category, premise in boundaries[:4]]
            findings.append(
                Finding(
                    "INFO",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} exposes "
                    "certificate/source-boundary parameter(s): "
                    + "; ".join(samples)
                    + ("; ..." if len(boundaries) > 4 else "")
                    + ". Paper wrappers must construct these certificates or remain conditional/partial.",
                )
            )
        elif key in boundary_dependency_index:
            dependencies = boundary_dependency_index[key]
            samples = [
                f"{dependency.category}: {dependency.premise} via `{dependency.via}`"
                for dependency in dependencies[:4]
            ]
            findings.append(
                Finding(
                    "INFO",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} transitively "
                    "depends on certificate/source-boundary API(s): "
                    + "; ".join(samples)
                    + ("; ..." if len(dependencies) > 4 else "")
                    + ". Paper wrappers that use this helper must still discharge or expose the boundary.",
                )
            )
        smells = source_specific_library_smells(declaration)
        if smells:
            findings.append(
                Finding(
                    "INFO",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} is source-shaped "
                    "inside reusable code: "
                    + "; ".join(smells)
                    + ". Prefer a generic API whose source formulas/certificates are explicit inputs "
                    "or move the paper-specific formula into the paper folder.",
                )
            )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def check_library_source_hygiene() -> list[Finding]:
    """Fail reusable code that appears to bake a paper/source formula into API names."""

    findings: list[Finding] = []
    seen: set[tuple[Path, int, str]] = set()
    for declaration in unique_declarations(library_lean_declaration_index()):
        key = declaration_key(declaration)
        if key in seen:
            continue
        seen.add(key)
        if re.match(r"\s*private\s+", declaration.source):
            continue
        smells = source_specific_library_smells(declaration)
        if not smells:
            continue
        findings.append(
            Finding(
                "ERROR",
                declaration.path,
                f"library `{declaration.name}` at line {declaration.line} is source-shaped "
                "inside reusable code: "
                + "; ".join(smells)
                + ". Rename it to a paper-neutral API, make the source formula an explicit "
                "certificate parameter, or move the paper-specific formula into the paper folder.",
            )
        )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def run_library(
    strict_style: bool,
    library_premise_audit: bool = False,
) -> list[Finding]:
    files = library_lean_files()
    findings: list[Finding] = []
    findings.extend(check_sorries_in_files(files))
    findings.extend(check_axiom_like_declarations_in_files(files))
    findings.extend(check_hidden_variable_premises_in_files(files))
    findings.extend(check_guarded_checks_in_files(files))
    findings.extend(check_library_source_hygiene())
    if strict_style:
        findings.extend(check_strict_lean_style())
    if library_premise_audit:
        findings.extend(check_library_certificate_boundaries())
    return findings


def run(
    include_active: bool,
    strict_style: bool,
    library_premise_audit: bool = False,
) -> list[Finding]:
    findings: list[Finding] = []
    findings.extend(check_sorries(include_active))
    findings.extend(check_axiom_like_declarations(include_active))
    findings.extend(check_hidden_variable_premises(include_active))
    findings.extend(check_guarded_checks(include_active))
    findings.extend(check_library_source_hygiene())
    findings.extend(check_paper_contract(include_active))
    findings.extend(check_review_launcher_readiness(include_active))
    findings.extend(check_dag_status_styles())
    findings.extend(check_paper_facing_ledgers(include_active))
    findings.extend(check_post_paper_audit_interfaces(include_active))
    findings.extend(check_machine_paper_status(library_premise_audit=library_premise_audit))
    findings.extend(check_status_label_vocabulary())
    findings.extend(check_readme_status_tables(include_active))
    findings.extend(check_tracked_artifacts(include_active))
    findings.extend(check_stale_architecture_terms())
    findings.extend(check_human_facing_readme())
    if strict_style:
        findings.extend(check_strict_lean_style())
    if library_premise_audit:
        findings.extend(check_library_certificate_boundaries())
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
    parser.add_argument(
        "--library-premise-audit",
        action="store_true",
        help="also list reusable-library APIs that expose certificate/source-boundary parameters",
    )
    parser.add_argument(
        "--library-only",
        action="store_true",
        help="audit only reusable EconCSLib code and library provenance checks",
    )
    parser.add_argument(
        "--info-limit",
        type=int,
        default=80,
        help=(
            "maximum INFO findings to print; use 0 to suppress INFO output or a negative "
            "number to print all INFO findings"
        ),
    )
    args = parser.parse_args()

    if args.library_only:
        findings = run_library(
            strict_style=args.strict_style,
            library_premise_audit=args.library_premise_audit,
        )
    else:
        findings = run(
            include_active=args.include_active,
            strict_style=args.strict_style,
            library_premise_audit=args.library_premise_audit,
        )
    printed_infos = 0
    omitted_infos = 0
    for finding in findings:
        if finding.severity == "INFO" and args.info_limit >= 0:
            if printed_infos >= args.info_limit:
                omitted_infos += 1
                continue
            printed_infos += 1
        print(finding.format())
    if omitted_infos:
        print(
            f"[INFO] omitted {omitted_infos} additional info finding(s); "
            "rerun with `--info-limit -1` to print all"
        )

    errors = [finding for finding in findings if finding.severity == "ERROR"]
    warnings = [finding for finding in findings if finding.severity == "WARN"]
    infos = [finding for finding in findings if finding.severity == "INFO"]
    print(
        f"Audit complete: {len(errors)} error(s), {len(warnings)} warning(s)"
        + ("; active paper folders included" if args.include_active else "; active paper folders skipped")
        + ("; strict style included" if args.strict_style else "")
        + ("; library premise audit included" if args.library_premise_audit else "")
        + ("; library-only" if args.library_only else "")
        + (f"; {len(infos)} info finding(s)" if infos else "")
    )
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
