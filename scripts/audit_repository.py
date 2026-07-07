#!/usr/bin/env python3
"""Repository hygiene audit for EconCSLib.

The checks here are intentionally mechanical. They are meant to catch stale
paper-folder structure, hidden Lean proof placeholders, noisy `#check` ledgers,
and status-surface overclaims. Semantic theorem fidelity still requires the
paper-by-paper PDF/DAG audit.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
from dataclasses import dataclass
from datetime import date
from pathlib import Path

try:
    from root_readme_policy import validate_root_readme
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports
    from scripts.root_readme_policy import validate_root_readme


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
PUBLIC_RELEASE = (ROOT / "docs" / "PAPER_STATUS.md").exists()
AUDIT_CONFIG = PAPERS / "audit_config.json"


def load_audit_config() -> dict[str, object]:
    if not AUDIT_CONFIG.exists():
        return {}
    payload = json.loads(AUDIT_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{AUDIT_CONFIG.relative_to(ROOT)} should contain a JSON object")
    if payload.get("schema") != 1:
        raise ValueError(f"{AUDIT_CONFIG.relative_to(ROOT)} should use schema 1")
    return payload


AUDIT_CONFIG_PAYLOAD = load_audit_config()


def audit_config_string_set(key: str) -> set[str]:
    raw = AUDIT_CONFIG_PAYLOAD.get(key, [])
    if not isinstance(raw, list):
        raise ValueError(f"{key} should be a list")
    return {str(item).strip() for item in raw if str(item).strip()}


ACTIVE_PAPERS = audit_config_string_set("active_papers")
GENERIC_SOURCE_HYGIENE_ALLOWED_TERMS = audit_config_string_set(
    "generic_source_hygiene_allowed_terms"
)


def paper_relative_file(folder: Path, preferred: str, legacy: str | None = None) -> Path:
    """Return the organized paper-local path, falling back to a legacy root file."""

    preferred_path = folder / preferred
    if preferred_path.exists() or legacy is None:
        return preferred_path
    legacy_path = folder / legacy
    if legacy_path.exists():
        return legacy_path
    return preferred_path


PAPER_DOCS_DIR = "docs"
PAPER_AUDIT_DIR = "audit"
FINAL_VALIDATION_REPORT_FILE = "FINAL_VALIDATION_REPORT.md"
POST_FORMALIZATION_AUDIT_FILE = f"{PAPER_DOCS_DIR}/POST_FORMALIZATION_AUDIT.md"
DEPENDENCY_DAG_TEX_FILE = f"{PAPER_DOCS_DIR}/DependencyDAG.tex"
DEPENDENCY_DAG_PDF_FILE = f"{PAPER_DOCS_DIR}/DependencyDAG.pdf"
AGENT_SOURCE_AUDIT_FILE = f"{PAPER_DOCS_DIR}/AGENT_SOURCE_AUDIT.md"
REQUIRED_PAPER_FILES = {
    ".gitignore",
    "MainTheorems.lean",
    "PaperInterface.lean",
    "status.json",
}
REQUIRED_GITIGNORE_PATTERNS = {
    "*.pdf",
    "!docs/DependencyDAG.pdf",
    "*.aux",
    "*.log",
    "*.fls",
    "*.fdb_latexmk",
    "*.synctex.gz",
}
REVIEW_LAUNCHER_NAME = "review-dashboard.sh"
REVIEW_LAUNCHER_TARGET = "scripts/launch_review_dashboard.sh"
REVIEW_TRACE_CACHE = ".review_traces/paper_interface_cache.json"
DEFAULT_LLM_ASSUMPTION_JUDGE_FILE = f"{PAPER_AUDIT_DIR}/assumption_match_llm.json"
DEFAULT_ASSUMPTION_SOURCE_FILE = "Assumptions.lean"
DEFAULT_SOURCE_RECORD_AUDIT_FILE = f"{PAPER_AUDIT_DIR}/source_record_audit.json"
DEFAULT_SOURCE_RECORD_JUDGE_FILE = f"{PAPER_AUDIT_DIR}/source_record_match_llm.json"
SOURCE_RECORD_AUDIT_HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
REQUIRED_LLM_ASSUMPTION_PROMPT_VERSION = "assumption-provenance-v3-semantic-exact-premise-source"
REQUIRED_LLM_STATEMENT_PROMPT_VERSION = "statement-match-v3-semantic-full-statement"
REQUIRED_SOURCE_RECORD_PROMPT_VERSION = "source-record-v2-semantic-boundary-inputs"
APPROVED_SOURCE_RECORD_CLASSIFICATIONS = {
    "container_recursively_audited",
    "derived_consequence_record",
    "nonpropositional_witness_data",
    "proved_from_primitives",
    "validated_source_assumption",
    "approved_external_boundary",
}
UNRESOLVED_SOURCE_RECORD_CLASSIFICATIONS = {
    "unresolved_assumed_math",
    "uncertain",
    "mismatch",
    "unknown",
}
REVIEW_ROW_WARN_THRESHOLD = 80
PAPER_STATUS_FILE = PAPERS / "status.json"
HUMAN_STATUS_FILE = PAPERS / "human_status.json"
PAPER_INTERFACE_OVERSIZED_LINE_THRESHOLD = 3000
PAPER_INTERFACE_COMPACT_LINE_THRESHOLD = 1000
ROOT_STATUS_VALUES = {
    "Formalized",
    "Formalized with caveat",
    "Formalized with documented caveat",
    "Main endpoints formalized",
    "Main endpoints formalized with documented deviations",
    "Partially formalized",
    "Conditional",
    "Paper draft",
    "Scaffold",
    "Not formalized",
    "Active validation",
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
    "paper draft",
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
    r"(?:theorem|lemma|def|abbrev|axiom|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b",
    re.M,
)
REVIEW_DECL_KIND_RE = re.compile(
    r"^\s*(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b",
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
GENERIC_SOURCE_THEOREM_LABEL_RE = re.compile(
    r"\b(?:Definition|Lemma|Proposition|Theorem|Corollary|Claim)\s+"
    r"[A-Z]?\d+(?:\.\d+)*(?:\s*\([^)]+\))?",
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
ASSUMPTION_POLICY_ALLOWED_VALUES = ASSUMPTION_POLICY_STRICT_VALUES | {
    "source-plus-proof-boundary",
}
ASSUMPTION_DECL_NAME_RE = re.compile(
    r"^(?:paper_)?assumption(?:_|$)|^source_assumption(?:_|$)|_assumption(?:_|$)"
)
AXIOM_LIKE_DECL_NAME_RE = re.compile(
    r"^\s*(?:axiom|opaque|constant|unsafe\s+(?:axiom|def|theorem|lemma))\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
ASSUMPTION_AUDIT_PREMISE_RE = re.compile(r"^\s*--\s*audit-premise:\s*(.+?)\s*$")
APPROVED_ASSUMPTION_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "documented_additional_assumption",
    "documented_caveat",
    "partial_boundary",
}
APPROVED_ASSUMPTION_PREMISE_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "source_text",
    "source_text_model_primitive",
    "derived_from_source_primitives",
    "documented_additional_assumption",
    "documented_caveat",
    "partial_boundary",
}
LEAN_BINDER_RE = re.compile(r"[\(\{]([^()\{\}\[\]]+?)\s*:\s*([^()\{\}\[\]]+?)[\)\}]")
HYPOTHESIS_NAME_RE = re.compile(
    r"^(?:h[A-Za-z0-9_']*|.*(?:assumption|certificate|hypothesis|premise|regularity|bridge|replay|process|row|threshold|capacity).*)$",
    re.I,
)
PROOF_BOUNDARY_TYPE_RE = re.compile(
    r"\b(?:Prop|[A-Za-z0-9_']*(?:Certificate|Assumption|Hypothesis|Witness|Boundary|"
    r"Bridge|Rows?|Table|SourceModel|SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|"
    r"Window|Windows|Package|Regularity|Invariant|Replay|Process))\b",
    re.I,
)
VARIABLE_BOUNDARY_TYPE_RE = re.compile(
    r"\b[A-Za-z0-9_']*(?:Certificate|Assumption|Hypothesis|Witness|Boundary|Bridge|"
    r"Rows?|Table|SourceModel|SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|Window|"
    r"Windows|Package|Regularity|Invariant|Replay|Process)\b",
    re.I,
)
LIBRARY_CERTIFICATE_BOUNDARY_RE = re.compile(
    r"(?:^|[_A-Za-z0-9'])("
    r"cert(?:ificate)?|source[-_ ]?rows?|source[-_ ]?table|row[-_ ]?package|"
    r"external|oracle|boundary|witness|bridge|replay|process|assumption|hypothesis"
    r")",
    re.I,
)
LIBRARY_BOUNDARY_TYPE_RE = re.compile(
    r"\b[A-Za-z0-9_']*(?:"
    r"Certificate|Assumption|Hypothesis|Witness|Boundary|Bridge|Rows?|"
    r"SourceModel|SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|Window|Windows|Package|"
    r"Regularity|Replay|Process"
    r")\b",
    re.I,
)
LIBRARY_EXTERNAL_BOUNDARY_RE = re.compile(r"\b(?:external|oracle|npEqZPP|NP|ZPP|hardness)\b", re.I)
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
APPROVED_LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PRINT_AXIOMS_RE = re.compile(r"'([^']+)'\s+depends on axioms:\s*\[(.*?)\]", re.S)
PRINT_NO_AXIOMS_RE = re.compile(r"'([^']+)'\s+does not depend on any axioms")
LIBRARY_STANDARD_DEFINITION_AUDIT_FILE = ROOT / "EconCSLib" / "LibraryDefinitionAudit.lean"
REQUIRED_LIBRARY_STANDARD_AUDITS = {
    "jensenConvex_iff_convexOn_univ": "JensenConvex matches mathlib `ConvexOn ℝ Set.univ`",
    "jensenConcave_iff_concaveOn_univ": "JensenConcave matches mathlib `ConcaveOn ℝ Set.univ`",
    "strictQuasiConvexOnPositive_iff_expected": (
        "StrictQuasiConvexOnPositive has the expected positive-domain strict "
        "quasi-convex inequality"
    ),
    "strictQuasiConcaveOnPositive_iff_expected": (
        "StrictQuasiConcaveOnPositive has the expected positive-domain strict "
        "quasi-concave inequality"
    ),
}
LIBRARY_FORBIDDEN_SOURCE_ASSUMPTION_RE = re.compile(
    r"(?:^|_)(?:source|paper)?(?:assumption|hypothesis)(?:_|$)|"
    r"(?:Source|Paper)?(?:Assumption|Hypothesis)$"
)
REUSABLE_LIBRARY_PROVENANCE_TEXT_RE = re.compile(
    r"\b(?:"
    r"source[- ]paper|source[- ]rows?|source[- ]facing|source[- ]formula|"
    r"source[- ]threshold|displayed source[- ]threshold|displayed formula|"
    r"paper[- ]specific|paper's"
    r")\b",
    re.I,
)
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
    haystack = lean_code_text(haystack)
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


def lean_code_lines_from_text(text: str) -> list[tuple[int, str]]:
    """Return Lean code lines with line and block comments removed."""

    code_lines: list[tuple[int, str]] = []
    depth = 0
    for line_no, line in enumerate(text.splitlines(), start=1):
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


def lean_code_lines(path: Path) -> list[tuple[int, str]]:
    """Return Lean file lines with line and block comments removed."""

    return lean_code_lines_from_text(path.read_text(encoding="utf-8"))


def lean_code_text(text: str) -> str:
    """Return Lean source text with line and nested block comments removed."""

    code_lines: list[str] = []
    depth = 0
    for line in text.splitlines():
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
        code_lines.append(strip_line_comment("".join(out)))
    return "\n".join(code_lines)


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


def approved_paper_proof_boundary_declarations() -> dict[Path, set[str]]:
    """Return paper-local Assumptions.lean declarations approved as proof debt."""

    approved: dict[Path, set[str]] = {}
    if not PAPERS.exists():
        return approved
    for status_path in sorted(PAPERS.glob("*/status.json")):
        try:
            payload = json.loads(status_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        review_surface = payload.get("review_surface")
        if not isinstance(review_surface, dict):
            continue
        raw_names = review_surface.get("proof_boundary_names")
        if not isinstance(raw_names, list):
            continue
        names = {name for name in raw_names if isinstance(name, str) and name}
        if not names:
            continue
        raw_source = review_surface.get("assumption_source_file")
        if isinstance(raw_source, str) and raw_source:
            source_path = ROOT / raw_source
        else:
            source_path = status_path.parent / DEFAULT_ASSUMPTION_SOURCE_FILE
        approved.setdefault(source_path.resolve(), set()).update(names)
    return approved


def check_axiom_like_declarations_in_files(files: list[Path]) -> list[Finding]:
    """Reject declarations that can hide unproved premises from paper audits."""

    findings: list[Finding] = []
    approved_boundaries = approved_paper_proof_boundary_declarations()
    for path in files:
        approved_names = approved_boundaries.get(path.resolve(), set())
        for line_no, code in lean_code_lines(path):
            stripped = code.strip()
            if AXIOM_LIKE_DECL_RE.match(stripped):
                match = AXIOM_LIKE_DECL_NAME_RE.match(stripped)
                if match and match.group("name") in approved_names:
                    continue
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
    return (
        path.suffix == ".pdf"
        and path.name not in ALLOWED_TRACKED_PAPER_PDFS
        and not is_declared_tracked_pdf_artifact(path)
    )


def declared_tracked_pdf_artifacts(folder: Path) -> set[Path]:
    """Return non-source PDF artifacts explicitly declared by paper status."""

    payload = load_json_object(folder / "status.json")
    artifacts = payload.get("artifacts") if payload else None
    if not isinstance(artifacts, dict):
        return set()
    declared: set[Path] = set()
    for key, raw_path in artifacts.items():
        if not isinstance(key, str) or "source" in key.lower():
            continue
        if not isinstance(raw_path, str) or not raw_path.endswith(".pdf"):
            continue
        artifact_path = ROOT / raw_path
        try:
            artifact_path.relative_to(folder)
        except ValueError:
            continue
        declared.add(artifact_path)
    return declared


def is_declared_tracked_pdf_artifact(path: Path) -> bool:
    if path.suffix != ".pdf":
        return False
    absolute = path if path.is_absolute() else ROOT / path
    try:
        rel = absolute.relative_to(PAPERS)
    except ValueError:
        return False
    if len(rel.parts) < 2:
        return False
    folder = PAPERS / rel.parts[0]
    return absolute in declared_tracked_pdf_artifacts(folder)


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

        dag_pdf = paper_relative_file(folder, DEPENDENCY_DAG_PDF_FILE, "DependencyDAG.pdf")
        if not dag_pdf.exists():
            findings.append(Finding("WARN", folder, "rendered `DependencyDAG.pdf` is absent locally"))
        dag_tex = paper_relative_file(folder, DEPENDENCY_DAG_TEX_FILE, "DependencyDAG.tex")
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


FINAL_REPORT_FORMALIZED_RE = re.compile(
    r"(?mi)^\s*(?:-\s*)?(?:Completion status|Lean formalization status)\s*:\s*"
    r"(?:formalized|complete(?:d)?)(?:\s|\.|$)"
)
FINAL_REPORT_PARTIAL_RE = re.compile(
    r"(?mi)^\s*(?:-\s*)?(?:Completion status|Lean formalization status)\s*:\s*"
    r"(?:partially formalized|partial(?:ly)?)(?:\s|\.|$)"
)
FINAL_REPORT_HUMAN_VERDICT_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Human\s+Verdict\b"
)
FINAL_REPORT_CLOSEOUT_STATUS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Closeout\s+Status\b"
)
FINAL_REPORT_SOURCE_SCOPE_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Source\s+(?:and|And)\s+Scope\b"
)
FINAL_REPORT_RESEARCHER_SUMMARY_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Researcher\s+Summary\s+of\s+Checked\s+Results\b"
)
FINAL_REPORT_REMAINING_BOUNDARIES_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Remaining\s+Boundaries\s+and\s+Gaps\b"
)
FINAL_REPORT_ADDITIONAL_ASSUMPTIONS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Additional\s+Assumptions\s+Beyond\s+Paper\b"
)
FINAL_REPORT_PROOF_DEVIATIONS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Proof-Strategy\s+Deviations\b"
)
FINAL_REPORT_PROOF_TRICKS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Proof\s+Tricks\s+Worth\s+Reusing\b"
)
FINAL_REPORT_GENERALIZATIONS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Generalizations,\s+Conjectures,\s+and\s+Extensions\b"
)
FINAL_REPORT_SOURCE_FIXES_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Mathematical\s+Typos\s+or\s+Other\s+Fixes\s+"
    r"Suggested\s+(?:in|for)\s+the\s+Source\s+Paper\b"
)
FINAL_REPORT_ISSUES_CAVEATS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Paper\s+Issues\s+or\s+Caveats\b"
)
FINAL_REPORT_DETAILED_EVIDENCE_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Detailed\s+Formalization\s+Evidence\b"
)
FINAL_REPORT_MACHINE_FRONT_MATTER_RE = re.compile(
    r"(?i)\b("
    r"python3|lake\s+build|#print|transitive-source-premise-audit|"
    r"Axiom,\s*Premise|Lean\s+Axiom|Lean\s+footprint|"
    r"LLM\s+statement-translation\s+audit|Model/agent|validator\s+rows?|"
    r"validator\s+status|audit\s+digest|source-record\s+audit|"
    r"source-record\s+sidecar|Lean\s+formalization\s+status|"
    r"Human\s+dashboard\s+review\s+status|Paper\s+interface:|Review\s+surface:"
    r")\b"
)
FINAL_REPORT_OLD_FINAL_VERDICT_RE = re.compile(
    r"(?mi)^##+\s+\d+\.\s+Final\s+Verdict\b"
)
FINAL_REPORT_OLD_ISSUES_CAVEATS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Paper\s+Issues\s+or\s+(?:Formalization\s+Caveats|Errors)\b"
)
FINAL_REPORT_OLD_WHAT_PROVEN_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?(?:What\s+Has\s+Been\s+Proven|What\s+Lean\s+Proves)\b"
)
FINAL_REPORT_CHECKLIST_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?"
    r"(?:Paper\s+Assumption\s+Provenance|Displayed\s+Formula\s+Provenance|"
    r"Library\s+Lift\s+Pass|DAG\s+Audit|"
    r"Validation\s+Checks|Validation\s+Commands|Paper\s+Definitions\s+Checked|"
    r"Named\s+Theorem\s+Statements\s+Checked|Paper-Facing\s+Statement\s+Validator\s+Ledger|"
    r"Statement\s+Validator\s+Ledger|Statement\s+Validator\s+Findings)\b"
)
CLOSEOUT_PAPER_STATUSES = {
    "formalized",
    "formalized with caveat",
    "conditional",
}
CLOSEOUT_DAG_REPORT_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?DAG\s+(?:Audit|Status)\b"
)
CLOSEOUT_VALIDATION_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Validation\s+(?:Checks|Commands)\b"
)
CLOSEOUT_AUDIT_DAG_HEADING_RE = re.compile(r"(?mi)^##+\s+DAG\s+(?:Audit|Status)\b")
CLOSEOUT_AUDIT_COMMANDS_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:Validation\s+)?Commands\b"
)
CLOSEOUT_STALE_PLACEHOLDER_RE = re.compile(
    r"(?mi)"
    r"^\s*-\s*(?:Rendered artifact|Topology|Layout)\s*:\s*not checked\s*$|"
    r"^\s*-\s*Not run\.\s*$|"
    r"\b(?:TODO|TBD|to be filled|not yet rendered|not inspected)\b"
)
CLOSEOUT_VISUAL_DAG_EVIDENCE_RE = re.compile(
    r"\b(?:visual(?:ly)?|render(?:ed|ing)?|layout|overlap|pdflatex|latexmk|mutool|png)\b",
    re.I,
)


def paper_local_status(folder: Path) -> str:
    status_file = folder / "status.json"
    if not status_file.exists():
        return ""
    try:
        payload = json.loads(status_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ""
    status = payload.get("status")
    return status.strip().lower() if isinstance(status, str) else ""


def is_closeout_status(status: str) -> bool:
    return status in CLOSEOUT_PAPER_STATUSES or status.startswith("formalized")


def check_final_report_status_alignment(
    include_active: bool,
    paper_filter: str | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    for folder in paper_dirs():
        if paper_filter is not None and folder.name != paper_filter:
            continue
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        status_file = folder / "status.json"
        report = paper_relative_file(
            folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
        )
        if not status_file.exists() or not report.exists():
            continue
        try:
            payload = json.loads(status_file.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        status = str(payload.get("status", "")).strip().lower()
        report_text = report.read_text(encoding="utf-8")
        says_formalized = bool(FINAL_REPORT_FORMALIZED_RE.search(report_text))
        says_partial = bool(FINAL_REPORT_PARTIAL_RE.search(report_text))
        if status.startswith("partially") and says_formalized:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report has a whole-paper `formalized` verdict line, "
                    "but paper-local status.json is partially formalized",
                )
            )
        if status in {"formalized", "formalized with caveat"} and says_partial and not says_formalized:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report has a whole-paper partial verdict line, "
                    "but paper-local status.json is formalized",
                )
            )
    return findings


def check_final_report_human_facing_front_matter(
    include_active: bool,
    paper_filter: str | None = None,
) -> list[Finding]:
    """Keep the top of final reports useful to researchers before audit detail."""

    findings: list[Finding] = []
    for folder in paper_dirs(include_template=True):
        if paper_filter is not None and folder.name != paper_filter:
            continue
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        report = paper_relative_file(
            folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
        )
        if not report.exists():
            continue
        report_text = report.read_text(encoding="utf-8")
        human_verdict = FINAL_REPORT_HUMAN_VERDICT_RE.search(report_text)
        if not human_verdict:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report should start with a short `Human Verdict` section",
                )
            )
            continue
        next_heading = re.search(r"(?m)^##+\s+", report_text[human_verdict.end():])
        front_matter_end = human_verdict.end() + next_heading.start() if next_heading else min(
            len(report_text),
            human_verdict.start() + 3000,
        )
        front_matter = report_text[human_verdict.start():front_matter_end]
        verdict_body = front_matter.split("\n", 1)[1] if "\n" in front_matter else ""

        if re.search(r"(?m)^###", verdict_body):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "Human Verdict should be concise prose, not nested audit subsections",
                )
            )
        if FINAL_REPORT_MACHINE_FRONT_MATTER_RE.search(verdict_body):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "Human Verdict should avoid commands, Lean identifiers, validator ledgers, "
                    "and audit counters; move machine evidence below Source and Scope",
                )
            )
        if len(re.findall(r"\b\w+\b", verdict_body)) > 140:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "Human Verdict is too long; keep it to a few researcher-facing sentences",
                )
            )
        if len(re.findall(r"(?m)^\s*-\s+", verdict_body)) >= 3:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "Human Verdict looks like an audit ledger; use short prose instead",
                )
            )
        if FINAL_REPORT_OLD_FINAL_VERDICT_RE.search(report_text):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "use `Closeout Status` instead of a repetitive `Final Verdict` section",
                )
            )
        if FINAL_REPORT_OLD_ISSUES_CAVEATS_RE.search(report_text):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "use the human-facing `Paper Issues or Caveats` section title, "
                    "even when the body is `None found.`",
                )
            )
        if FINAL_REPORT_OLD_WHAT_PROVEN_RE.search(report_text):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "use `Researcher Summary of Checked Results` plus later "
                    "`Detailed Formalization Evidence`, not `What Has Been Proven`",
                )
            )

        closeout = FINAL_REPORT_CLOSEOUT_STATUS_RE.search(report_text)
        source_scope = FINAL_REPORT_SOURCE_SCOPE_RE.search(report_text, human_verdict.end())
        summary = FINAL_REPORT_RESEARCHER_SUMMARY_RE.search(report_text)
        remaining = FINAL_REPORT_REMAINING_BOUNDARIES_RE.search(report_text)
        additional = FINAL_REPORT_ADDITIONAL_ASSUMPTIONS_RE.search(report_text)
        deviations = FINAL_REPORT_PROOF_DEVIATIONS_RE.search(report_text)
        tricks = FINAL_REPORT_PROOF_TRICKS_RE.search(report_text)
        generalizations = FINAL_REPORT_GENERALIZATIONS_RE.search(report_text)
        source_fixes = FINAL_REPORT_SOURCE_FIXES_RE.search(report_text)
        issues = FINAL_REPORT_ISSUES_CAVEATS_RE.search(report_text)
        detailed = FINAL_REPORT_DETAILED_EVIDENCE_RE.search(report_text)
        required_front = [
            ("Closeout Status", closeout),
            ("Source and Scope", source_scope),
            ("Researcher Summary of Checked Results", summary),
            ("Remaining Boundaries and Gaps", remaining),
            ("Additional Assumptions Beyond Paper", additional),
            ("Proof-Strategy Deviations", deviations),
            ("Proof Tricks Worth Reusing", tricks),
            ("Generalizations, Conjectures, and Extensions", generalizations),
            ("Paper Issues or Caveats", issues),
            ("Detailed Formalization Evidence", detailed),
        ]
        for title, match in required_front:
            if not match:
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        f"final validation report should include `{title}` in its standard front order",
                    )
                )
        present_positions = [
            human_verdict.start(),
            *[
                match.start()
                for match in [
                    closeout,
                    source_scope,
                    summary,
                    remaining,
                    additional,
                    deviations,
                    tricks,
                    generalizations,
                    source_fixes,
                    issues,
                    detailed,
                ]
                if match
            ],
        ]
        if present_positions != sorted(present_positions):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report should order front sections as Human Verdict, "
                    "Closeout Status, Source and Scope, Researcher Summary, "
                    "Remaining Boundaries, Additional Assumptions, Proof-Strategy "
                    "Deviations, Proof Tricks, Generalizations/Conjectures/"
                    "Extensions, optional source-paper fixes, Paper Issues or "
                    "Caveats, then Detailed Formalization Evidence",
                )
            )
        if detailed:
            pre_detail = report_text[human_verdict.start():detailed.start()]
            if FINAL_REPORT_CHECKLIST_HEADING_RE.search(pre_detail):
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        "checklist/provenance/Lean evidence headings should appear after "
                        "`Detailed Formalization Evidence`, not in the researcher-facing front matter",
                    )
                )
    return findings


def check_dag_and_validation_report_closeout(
    include_active: bool,
    paper_filter: str | None = None,
) -> list[Finding]:
    """Ensure completed paper closeout audits include DAG/report evidence."""

    findings: list[Finding] = []
    for folder in paper_dirs():
        if paper_filter is not None and folder.name != paper_filter:
            continue
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        status = paper_local_status(folder)
        if not is_closeout_status(status):
            continue

        report = paper_relative_file(
            folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
        )
        post_audit = paper_relative_file(
            folder, POST_FORMALIZATION_AUDIT_FILE, "POST_FORMALIZATION_AUDIT.md"
        )
        dag_tex = paper_relative_file(folder, DEPENDENCY_DAG_TEX_FILE, "DependencyDAG.tex")
        dag_pdf = paper_relative_file(folder, DEPENDENCY_DAG_PDF_FILE, "DependencyDAG.pdf")
        agent_source_audit = folder / AGENT_SOURCE_AUDIT_FILE

        if not report.exists():
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    "completed paper is missing `FINAL_VALIDATION_REPORT.md`",
                )
            )
        else:
            report_text = report.read_text(encoding="utf-8")
            if not CLOSEOUT_DAG_REPORT_HEADING_RE.search(report_text):
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        "final validation report should include a `DAG Audit` or `DAG Status` section",
                    )
                )
            if not CLOSEOUT_VALIDATION_HEADING_RE.search(report_text):
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        "final validation report should include a `Validation Checks` or `Validation Commands` section",
                    )
                )
            for artifact in ("DependencyDAG.tex", "DependencyDAG.pdf"):
                if artifact not in report_text:
                    findings.append(
                        Finding(
                            "WARN",
                            report,
                            f"final validation report should name `{artifact}` in the DAG audit evidence",
                        )
                    )
            if not CLOSEOUT_VISUAL_DAG_EVIDENCE_RE.search(report_text):
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        "final validation report should record rendered/visual DAG inspection evidence",
                    )
                )
            if f"--paper {folder.name}" not in report_text or "scripts/audit_repository.py" not in report_text:
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        "final validation report should record the targeted repository audit command",
                    )
                )
            if CLOSEOUT_STALE_PLACEHOLDER_RE.search(report_text):
                findings.append(
                    Finding(
                        "ERROR",
                        report,
                        "completed-paper final validation report still contains stale placeholder audit language",
                    )
                )

        if not agent_source_audit.exists():
            findings.append(
                Finding(
                    "ERROR",
                    agent_source_audit,
                    "completed paper is missing `docs/AGENT_SOURCE_AUDIT.md` source-first holistic audit",
                )
            )
        else:
            agent_audit_text = agent_source_audit.read_text(encoding="utf-8")
            normalized_agent_audit_text = re.sub(r"\s+", " ", agent_audit_text)
            if not re.search(r"^##\s+Overall status:\s+PASS\s*$", agent_audit_text, re.M):
                findings.append(
                    Finding(
                        "ERROR",
                        agent_source_audit,
                        "`docs/AGENT_SOURCE_AUDIT.md` should record `## Overall status: PASS`",
                    )
                )
            if re.search(r"NEEDS AGENT REVIEW|scaffold has not performed", agent_audit_text, re.I):
                findings.append(
                    Finding(
                        "ERROR",
                        agent_source_audit,
                        "`docs/AGENT_SOURCE_AUDIT.md` is still a scaffold, not a completed holistic audit",
                    )
                )
            for required_phrase in (
                "independent source-first",
                "not merely summarize existing sidecars",
                "source inventory from the source itself",
                "omissions, hidden strengthening/weakening, and semantic mismatches",
            ):
                if required_phrase not in normalized_agent_audit_text:
                    findings.append(
                        Finding(
                            "ERROR",
                            agent_source_audit,
                            "`docs/AGENT_SOURCE_AUDIT.md` must document an independent "
                            "source-paper/source-text read, source-inventory construction "
                            "from the source itself, and Lean-interface comparison for "
                            "omissions, hidden strengthening/weakening, and semantic "
                            "mismatches; it must not merely summarize existing sidecars",
                        )
                    )
                    break
            for heading in (
                "Source Inventory",
                "Lean Interface Comparison",
                "Machine Audit Results",
                "Findings",
            ):
                if not re.search(rf"^##\s+{re.escape(heading)}\s*$", agent_audit_text, re.M):
                    findings.append(
                        Finding(
                            "WARN",
                            agent_source_audit,
                            f"`docs/AGENT_SOURCE_AUDIT.md` should include a `{heading}` section",
                        )
                    )

        if post_audit.exists():
            audit_text = post_audit.read_text(encoding="utf-8")
            if not CLOSEOUT_AUDIT_DAG_HEADING_RE.search(audit_text):
                findings.append(
                    Finding(
                        "WARN",
                        post_audit,
                        "post-formalization audit should include a `DAG Audit` section",
                    )
                )
            if not CLOSEOUT_AUDIT_COMMANDS_HEADING_RE.search(audit_text):
                findings.append(
                    Finding(
                        "WARN",
                        post_audit,
                        "post-formalization audit should include a commands/validation commands section",
                    )
                )
            for artifact in ("FINAL_VALIDATION_REPORT.md", "DependencyDAG.tex", "DependencyDAG.pdf"):
                if artifact not in audit_text:
                    findings.append(
                        Finding(
                            "WARN",
                            post_audit,
                            f"post-formalization audit should name `{artifact}`",
                        )
                    )
            if f"--paper {folder.name}" not in audit_text or "scripts/audit_repository.py" not in audit_text:
                findings.append(
                    Finding(
                        "WARN",
                        post_audit,
                        "post-formalization audit should record the targeted repository audit command",
                    )
                )
            if CLOSEOUT_STALE_PLACEHOLDER_RE.search(audit_text):
                findings.append(
                    Finding(
                        "ERROR",
                        post_audit,
                        "completed-paper post-formalization audit still contains stale placeholder audit language",
                    )
                )

        if not dag_pdf.exists():
            findings.append(
                Finding(
                    "ERROR",
                    dag_pdf,
                    "completed paper is missing rendered `DependencyDAG.pdf`",
                )
            )
        elif dag_tex.exists() and dag_pdf.stat().st_mtime + 1 < dag_tex.stat().st_mtime:
            findings.append(
                Finding(
                    "WARN",
                    dag_pdf,
                    "`DependencyDAG.pdf` is older than `DependencyDAG.tex`; rerender and visually inspect it",
                )
            )

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
    """Return review-surface declarations keyed by name.

    Structures/classes/inductives are included so paper-local source
    assumptions declared in `Assumptions.lean` can be audited through the same
    provenance ledger as theorem-like assumptions.
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


def namespace_stack_at_line(text: str, line_number: int) -> list[str]:
    """Return the simple Lean namespace stack before `line_number`.

    Paper interfaces in this repository use ordinary `namespace ...`/`end ...`
    blocks. Tracking that stack is enough to generate fully qualified names for
    Lean-native `#print axioms` checks without maintaining a separate index.
    """

    stack: list[str] = []
    for current_line, code in lean_code_lines_from_text(text):
        if current_line >= line_number:
            break
        stripped = code.strip()
        match = re.match(r"^namespace\s+(.+)$", stripped)
        if match:
            stack.extend(
                part
                for part in re.split(r"\s+", match.group(1).strip())
                if part
            )
            continue
        match = re.match(r"^end(?:\s+(.+))?$", stripped)
        if not match:
            continue
        raw_names = (match.group(1) or "").strip()
        if raw_names:
            for _ in re.split(r"\s+", raw_names):
                if stack:
                    stack.pop()
        elif stack:
            stack.pop()
    return stack


def qualified_review_decl_name(interface_text: str, line_number: int, name: str) -> str:
    namespaces = namespace_stack_at_line(interface_text, line_number)
    return ".".join([*namespaces, name]) if namespaces else name


def lean_module_name(path: Path) -> str:
    """Return the Lean module name corresponding to a repository Lean file."""

    rel = path.relative_to(ROOT).with_suffix("")
    parts = list(rel.parts)
    if parts and parts[0] == "papers":
        parts = parts[1:]
    return ".".join(parts)


def parse_print_axioms_output(output: str) -> dict[str, set[str]]:
    """Parse Lean `#print axioms` output keyed by fully qualified declaration."""

    parsed: dict[str, set[str]] = {}
    for match in PRINT_NO_AXIOMS_RE.finditer(output):
        parsed[match.group(1)] = set()
    for match in PRINT_AXIOMS_RE.finditer(output):
        raw_axioms = match.group(2)
        axioms = {
            axiom.strip()
            for axiom in re.split(r",|\n", raw_axioms)
            if axiom.strip()
        }
        parsed[match.group(1)] = axioms
    return parsed


def check_paper_interface_axiom_closure(
    paper_id: str,
    interface_path: Path,
    interface_text: str,
    include_names: list[str],
    declaration_blocks: dict[str, tuple[int, str, str]],
    status: object,
    approved_boundary_axioms: set[str] | None = None,
) -> list[Finding]:
    """Run Lean-native `#print axioms` on paper-facing review rows.

    This is the exact transitive proof-debt check. It catches `sorryAx`,
    declared axioms/constants, and opaque unsafe foundations no matter how many
    reusable-library layers lie between the paper theorem and the dependency.
    It deliberately does not try to classify theorem parameters; visible
    premise/source-assumption checks handle those separately from the expanded
    Lean statement.
    """

    rows: list[tuple[str, str, int]] = []
    for name in include_names:
        declaration = declaration_blocks.get(name)
        if declaration is None:
            continue
        line_no, _kind, _source = declaration
        rows.append((name, qualified_review_decl_name(interface_text, line_no, name), line_no))
    if not rows:
        return []

    script_lines = [
        f"import {lean_module_name(interface_path)}",
        "set_option pp.universes false",
        "",
    ]
    for _name, qualified_name, _line_no in rows:
        script_lines.append(f"#print axioms {qualified_name}")
    script = "\n".join(script_lines) + "\n"

    severity = completed_status_finding_severity(status)
    module_name = lean_module_name(interface_path)
    try:
        build_proc = subprocess.run(
            ["lake", "build", module_name],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=600,
        )
        if build_proc.returncode != 0:
            details = (build_proc.stderr or build_proc.stdout).strip().splitlines()
            excerpt = " ".join(details[:3])[:600] if details else "Lake returned a nonzero status"
            return [
                Finding(
                    severity,
                    interface_path,
                    f"`{paper_id}` Lean axiom audit could not build `{module_name}`: {excerpt}",
                )
            ]

        audit_tmp_root = ROOT / ".lake" / "paper_axiom_audit"
        audit_tmp_root.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=audit_tmp_root) as tmpdir:
            script_path = Path(tmpdir) / "paper_axiom_audit.lean"
            script_path.write_text(script, encoding="utf-8")
            proc = subprocess.run(
                ["lake", "env", "lean", str(script_path)],
                cwd=ROOT,
                check=False,
                capture_output=True,
                text=True,
                timeout=180,
            )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return [
            Finding(
                severity,
                interface_path,
                f"`{paper_id}` Lean axiom audit could not run for PaperInterface rows: {exc}",
            )
        ]

    if proc.returncode != 0:
        details = (proc.stderr or proc.stdout).strip().splitlines()
        excerpt = " ".join(details[:3])[:600] if details else "Lean returned a nonzero status"
        return [
            Finding(
                severity,
                interface_path,
                f"`{paper_id}` Lean axiom audit failed for PaperInterface rows: {excerpt}",
            )
        ]

    parsed = parse_print_axioms_output(proc.stdout)
    approved_boundary_axioms = approved_boundary_axioms or set()
    approved_axioms = set(APPROVED_LEAN_AXIOMS)
    for name in approved_boundary_axioms:
        approved_axioms.add(name)
        approved_axioms.add(f"{paper_id}.{name}")
    findings: list[Finding] = []
    for name, qualified_name, line_no in rows:
        if qualified_name not in parsed:
            findings.append(
                Finding(
                    severity,
                    interface_path,
                    f"`{paper_id}` Lean axiom audit produced no `#print axioms` row for "
                    f"`{name}` at line {line_no}",
                )
            )
            continue
        unapproved = sorted(parsed[qualified_name] - approved_axioms)
        if not unapproved:
            continue
        findings.append(
            Finding(
                severity,
                interface_path,
                f"`{paper_id}` review row `{name}` at line {line_no} depends on "
                "unapproved Lean axiom(s): "
                + ", ".join(unapproved)
                + ". Only "
                + ", ".join(sorted(approved_axioms))
                + " are accepted as standard Lean/mathlib foundations or "
                "declared paper-local proof boundaries.",
            )
        )
    return findings


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


def resolve_declaration_name(
    declaration_index: dict[str, list[LeanDeclaration]], name: object
) -> list[LeanDeclaration]:
    """Resolve an unqualified or module-qualified declaration name."""

    target = str(name or "").strip()
    if not target:
        return []
    if target in declaration_index:
        return declaration_index[target]
    return declaration_index.get(target.rsplit(".", 1)[-1], [])


def library_lean_files() -> list[Path]:
    """Return tracked reusable-library Lean files."""

    files: set[Path] = set()
    root = ROOT / "EconCSLib"
    if root.exists():
        files.update(path for path in root.rglob("*.lean") if path.is_file())
    try:
        tracked = git_ls_files()
    except subprocess.CalledProcessError:
        tracked = []
    for rel in tracked:
        path = ROOT / rel
        if path.suffix == ".lean" and path.exists() and path.relative_to(ROOT).parts[0] == "EconCSLib":
            files.add(path)
    return sorted(files)


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

    body = lean_code_text(declaration_body(source)).strip()
    match = re.fullmatch(
        r"@?\s*((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)",
        body,
    )
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

    if status not in {"formalized", "formalized with caveat", "partially formalized", "conditional"}:
        return "WARN"
    if strict_assumption_policy:
        return "ERROR"
    return "ERROR"


def completed_status_finding_severity(status: object) -> str:
    """Completed paper claims should satisfy the strict review-surface checks."""

    if status in {"formalized", "formalized with caveat", "partially formalized", "conditional"}:
        return "ERROR"
    return "WARN"


def paper_statement_sidecar_findings(
    paper_id: str,
    folder: Path,
    status: object,
) -> list[Finding]:
    """Check current statement/review-surface LLM sidecars for one paper.

    The dashboard owns the sidecar schema and digest logic.  The repository
    audit enforces that completed papers do not pass CI with stale or missing
    statement-translation evidence.
    """

    severity = completed_status_finding_severity(status)
    findings = paper_statement_map_declaration_findings(paper_id, folder, status)
    try:
        from review_dashboard import (
            assumption_provenance_audit_summary,
            paper_coverage_audit_summary,
            review_items_for_paper,
            review_surface_audit_summary,
            statement_translation_audit_summary,
        )

        items = review_items_for_paper(folder, use_cache=False)
        surface = review_surface_audit_summary(folder, items)
        statements = statement_translation_audit_summary(folder, items)
        paper_coverage = paper_coverage_audit_summary(folder, items)
        assumptions = assumption_provenance_audit_summary(folder, items)
    except Exception as exc:  # noqa: BLE001 - audit should report parser failures.
        return findings + [
            Finding(
                severity,
                folder,
                f"`{paper_id}` statement-sidecar audit could not run: {exc}",
            )
        ]

    strict_evidence_required = status in {
        "formalized",
        "formalized with caveat",
        "partially formalized",
        "conditional",
    }
    surface_needs_attention = bool(
        surface.get("needs_attention")
        or (strict_evidence_required and not surface.get("has_completed_audit"))
    )
    if surface_needs_attention:
        reasons: list[str] = []
        if strict_evidence_required and not surface.get("has_completed_audit"):
            reasons.append("missing explicit review-surface LLM pass")
        if surface.get("missing_required"):
            reasons.append("missing review-surface LLM audit")
        if surface.get("stale"):
            reasons.append("stale review-surface LLM audit")
        if surface.get("metadata_missing"):
            reasons.append("review-surface audit missing validator/timestamp success metadata")
        if surface.get("judgment") in {"needs_curation", "uncertain"}:
            reasons.append(f"review-surface judgment `{surface.get('judgment')}`")
        if surface.get("unknown_judgment"):
            reasons.append(f"unrecognized review-surface judgment `{surface.get('judgment') or 'missing'}`")
        findings.append(
            Finding(
                severity,
                folder / f"{PAPER_AUDIT_DIR}/review_surface_llm.json",
                f"`{paper_id}` review-surface audit needs attention: "
                + (", ".join(reasons) if reasons else "unknown issue"),
            )
        )

    if paper_coverage.get("needs_attention"):
        parts: list[str] = []
        for key, label in (
            ("missing_inventory", "missing required source-statement inventory"),
            ("unresolved_statement_map", "unresolved audit/paper_statement_map.json"),
            ("missing_required", "missing paper-level coverage audit"),
            ("missing_coverage_count", "source statement without coverage judgment"),
            ("partial_count", "partially covered source statement"),
            ("missing_count", "missing source statement"),
            ("uncertain_count", "uncertain source-coverage judgment"),
            ("unknown_count", "unknown source-coverage judgment"),
            ("stale_statement_count", "stale source-statement digest"),
            ("extra_coverage_count", "stale extra coverage item"),
            ("coverage_metadata_missing_count", "coverage item missing validator/timestamp metadata"),
            ("invalid_row_link_count", "invalid linked dashboard row"),
            ("covered_without_rows_count", "covered source statement without linked row"),
            (
                "required_out_of_scope_count",
                "required source-visible review target marked out of scope/not a paper target",
            ),
        ):
            value = paper_coverage.get(key)
            if isinstance(value, bool):
                if value:
                    parts.append(label)
            elif isinstance(value, int) and value:
                parts.append(f"{value} {label}(s)")
        if paper_coverage.get("stale_inventory"):
            parts.append("stale source-inventory digest")
        if paper_coverage.get("stale_surface"):
            parts.append("stale review-surface digest")
        if paper_coverage.get("audit_metadata_missing"):
            parts.append("paper-coverage audit missing validator/timestamp success metadata")
        findings.append(
            Finding(
                severity,
                folder / f"{PAPER_AUDIT_DIR}/paper_coverage_llm.json",
                f"`{paper_id}` paper-coverage audit needs attention: "
                + (", ".join(parts) if parts else "unknown issue"),
            )
        )
    if paper_coverage.get("source_to_lean_needs_attention"):
        parts = []
        for key, label in (
            ("support_only_named_claim_count", "theorem-like source statement only support-covered"),
            (
                "support_only_required_source_item_count",
                "required source-visible review target only support-covered",
            ),
            (
                "required_out_of_scope_count",
                "required source-visible review target marked out of scope/not a paper target",
            ),
            ("row_statement_match_missing_count", "source-to-row link without row-local statement judgment"),
            ("row_statement_match_stale_count", "source-to-row link with stale row-local statement judgment"),
            ("row_statement_match_mismatch_count", "source-to-row link with mismatched row-local statement judgment"),
            ("row_statement_match_uncertain_count", "source-to-row link with uncertain row-local statement judgment"),
            ("row_statement_match_unknown_count", "source-to-row link with unknown row-local statement judgment"),
            (
                "row_statement_match_conditional_without_coverage_boundary_count",
                "direct source coverage link whose row is only conditionally matched",
            ),
            (
                "row_statement_match_missing_statement_digest_count",
                "source-to-row link without row-local statement digest",
            ),
            (
                "row_statement_match_wrong_statement_digest_count",
                "source-to-row link with wrong row-local statement digest",
            ),
            ("row_assumption_provenance_missing_count", "source-to-assumption link without provenance judgment"),
            ("row_assumption_provenance_stale_count", "source-to-assumption link with stale provenance judgment"),
            ("row_assumption_provenance_mismatch_count", "source-to-assumption link with provenance mismatch"),
            ("row_assumption_provenance_uncertain_count", "source-to-assumption link with uncertain provenance"),
            ("row_assumption_provenance_unknown_count", "source-to-assumption link with unknown provenance"),
            (
                "row_assumption_provenance_conditional_without_coverage_boundary_count",
                "direct source coverage link whose assumption is only a partial boundary",
            ),
        ):
            value = paper_coverage.get(key)
            if isinstance(value, int) and value:
                parts.append(f"{value} {label}(s)")
        if parts:
            findings.append(
                Finding(
                    severity,
                    folder / f"{PAPER_AUDIT_DIR}/paper_coverage_llm.json",
                    f"`{paper_id}` source-to-Lean audit needs attention: " + ", ".join(parts),
                )
            )

    if statements.get("needs_attention"):
        parts: list[str] = []
        for key, label in (
            ("missing_draft_count", "missing Lean-to-TeX draft"),
            ("stale_draft_count", "stale Lean-to-TeX draft"),
            ("missing_judgment_count", "missing statement-judge row"),
            ("stale_judgment_count", "stale statement-judge row"),
            ("mismatch_count", "statement mismatch"),
            ("uncertain_count", "uncertain statement judgment"),
            ("unknown_count", "unknown statement judgment"),
        ):
            value = statements.get(key)
            if isinstance(value, int) and value:
                parts.append(f"{value} {label}(s)")
        findings.append(
            Finding(
                severity,
                folder / f"{PAPER_AUDIT_DIR}/statement_match_llm.json",
                f"`{paper_id}` statement-translation audit needs attention: "
                + (", ".join(parts) if parts else "unknown issue"),
            )
        )
    if assumptions.get("needs_attention"):
        parts = []
        for key, label in (
            ("missing_rows_count", "configured assumption declaration missing from review surface"),
            ("unlisted_rows_count", "assumption-like declaration not listed in status.json"),
            ("missing_judgment_count", "missing assumption-provenance judgment"),
            ("stale_judgment_count", "stale assumption-provenance judgment"),
            ("not_paper_assumption_count", "assumption judged not paper/source backed"),
            ("uncertain_count", "uncertain assumption-provenance judgment"),
            ("unknown_count", "unknown assumption-provenance judgment"),
            ("unresolved_premise_count", "unresolved premise-level provenance judgment"),
            ("missing_source_location_premise_count", "source-text premise judgment without source location"),
        ):
            value = assumptions.get(key)
            if isinstance(value, int) and value:
                parts.append(f"{value} {label}(s)")
        findings.append(
            Finding(
                severity,
                folder / f"{PAPER_AUDIT_DIR}/assumption_match_llm.json",
                f"`{paper_id}` assumption-provenance audit needs attention: "
                + (", ".join(parts) if parts else "unknown issue"),
            )
        )
    return findings


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


def paper_statement_map_declaration_findings(
    paper_id: str,
    folder: Path,
    status: object,
) -> list[Finding]:
    """Check that source-inventory Lean declaration names resolve."""

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    if not statement_map.exists():
        return []
    try:
        payload = json.loads(statement_map.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [
            Finding(
                completed_status_finding_severity(status),
                statement_map,
                f"`{paper_id}` source inventory is not readable JSON: {exc}",
            )
        ]
    items = payload.get("items") if isinstance(payload, dict) else None
    if not isinstance(items, dict):
        return []

    paper_declarations = paper_lean_declaration_index(folder)
    library_declarations = library_lean_declaration_index()
    missing: list[str] = []
    malformed: list[str] = []
    for source_key, item in items.items():
        if not isinstance(item, dict):
            continue
        raw_declarations = item.get("lean_declarations")
        if raw_declarations is None:
            continue
        if not isinstance(raw_declarations, list):
            malformed.append(str(source_key))
            continue
        for raw_name in raw_declarations:
            name = str(raw_name or "").strip()
            if not name:
                malformed.append(str(source_key))
                continue
            if resolve_declaration_name(paper_declarations, name):
                continue
            if resolve_declaration_name(library_declarations, name):
                continue
            missing.append(f"{source_key}:{name}")

    findings: list[Finding] = []
    severity = completed_status_finding_severity(status)
    if malformed:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory has malformed lean_declarations for "
                + ", ".join(malformed[:8])
                + ("; ..." if len(malformed) > 8 else ""),
            )
        )
    if missing:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory names {len(missing)} Lean declaration(s) "
                "that do not resolve in paper-local or reusable-library Lean files: "
                + ", ".join(missing[:8])
                + ("; ..." if len(missing) > 8 else ""),
            )
        )
    return findings


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


def review_surface_proof_boundary_names(review_surface: dict[str, object]) -> tuple[set[str], list[str]]:
    """Read approved paper-local proof-boundary declarations from status.json."""

    raw = review_surface.get("proof_boundary_names")
    if raw is None:
        return set(), []
    if not isinstance(raw, list):
        return set(), ["`review_surface.proof_boundary_names` should be a string list"]
    names: set[str] = set()
    problems: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            problems.append(f"`review_surface.proof_boundary_names[{index}]` should be a nonempty string")
            continue
        names.add(value.strip())
    return names, problems


def review_surface_auxiliary_names(review_surface: dict[str, object]) -> tuple[set[str], list[str]]:
    """Read proof-facing declarations intentionally excluded from statement review."""

    raw = review_surface.get("auxiliary_names")
    if raw is None:
        return set(), []
    if not isinstance(raw, list):
        return set(), ["`review_surface.auxiliary_names` should be a string list"]
    names: set[str] = set()
    problems: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            problems.append(f"`review_surface.auxiliary_names[{index}]` should be a nonempty string")
            continue
        names.add(value.strip())
    return names, problems


def assumption_source_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-local Lean file that declares reviewed assumptions."""

    raw_path = review_surface.get("assumption_source_file")
    if isinstance(raw_path, str) and raw_path.strip():
        return ROOT / raw_path.strip()
    return folder / DEFAULT_ASSUMPTION_SOURCE_FILE


def review_surface_source_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the Lean file that contains the configured review-surface rows."""

    raw_path = review_surface.get("source_file")
    if isinstance(raw_path, str) and raw_path.strip():
        return ROOT / raw_path.strip()
    return folder / "PaperInterface.lean"


def assumption_judgment_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-root LLM assumption-provenance judgment file."""

    llm_assumption_review = review_surface.get("llm_assumption_review")
    if isinstance(llm_assumption_review, dict):
        raw_path = llm_assumption_review.get("assumption_judgment_file")
        if isinstance(raw_path, str) and raw_path.strip():
            return ROOT / raw_path.strip()
    return folder / DEFAULT_LLM_ASSUMPTION_JUDGE_FILE


def source_record_audit_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-root generated source-record audit payload path."""

    llm_source_record_review = review_surface.get("llm_source_record_review")
    if isinstance(llm_source_record_review, dict):
        raw_path = llm_source_record_review.get("source_record_audit_file")
        if isinstance(raw_path, str) and raw_path.strip():
            return ROOT / raw_path.strip()
    return folder / DEFAULT_SOURCE_RECORD_AUDIT_FILE


def source_record_judgment_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-root LLM source-record judgment sidecar path."""

    llm_source_record_review = review_surface.get("llm_source_record_review")
    if isinstance(llm_source_record_review, dict):
        raw_path = llm_source_record_review.get("source_record_judgment_file")
        if isinstance(raw_path, str) and raw_path.strip():
            return ROOT / raw_path.strip()
    return folder / DEFAULT_SOURCE_RECORD_JUDGE_FILE


def load_json_object(path: Path) -> dict[str, object] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def repo_display_path(path: Path) -> str:
    """Return a stable repository-relative path string for messages."""

    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        if not path.is_absolute():
            return str(path)
        return str(path)


def run_source_record_audit_helper(paper_id: str) -> tuple[dict[str, object] | None, str]:
    """Run the skill-bundled source-record audit helper and return its JSON payload."""

    if not SOURCE_RECORD_AUDIT_HELPER.exists():
        return None, f"missing source-record audit helper `{SOURCE_RECORD_AUDIT_HELPER.relative_to(ROOT)}`"
    with tempfile.NamedTemporaryFile("w", suffix=".json", encoding="utf-8", delete=False) as handle:
        out_path = Path(handle.name)
    try:
        proc = subprocess.run(
            [
                "python3",
                str(SOURCE_RECORD_AUDIT_HELPER),
                "--paper",
                paper_id,
                "--out",
                str(out_path),
                "--max-lean-output-chars",
                "30000",
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        payload = load_json_object(out_path)
        if proc.returncode != 0:
            excerpt = "\n".join(proc.stdout.splitlines()[-30:]) if proc.stdout else ""
            if payload is not None:
                recursion_failures = payload.get("recursion_failures")
                if isinstance(recursion_failures, list) and recursion_failures:
                    excerpt = "; ".join(
                        str(item.get("message") or item)
                        for item in recursion_failures[:5]
                        if isinstance(item, dict)
                    )
                lean_check = payload.get("lean_check")
                if not excerpt and isinstance(lean_check, dict):
                    output = str(lean_check.get("output") or "")
                    if output:
                        excerpt = "\n".join(output.splitlines()[-30:])
            return payload, f"source-record audit helper failed with exit code {proc.returncode}: {excerpt}"
        if payload is None:
            return None, "source-record audit helper did not write a JSON object"
        return payload, ""
    finally:
        try:
            out_path.unlink()
        except FileNotFoundError:
            pass


def source_record_judgment_items(path: Path, paper_id: str) -> dict[str, dict[str, object]]:
    """Load LLM source-record field judgments keyed by `Structure.field`."""

    payload = load_json_object(path)
    if not payload or payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, paper_id}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        items = payload.get("field_judgments")
    if not isinstance(items, dict):
        return {}
    prompt_version = str(payload.get("prompt_version") or "").strip()
    prompt_version_stale = prompt_version != REQUIRED_SOURCE_RECORD_PROMPT_VERSION
    payload_audit_digest = str(payload.get("source_record_audit_sha256") or "").strip()
    payload_has_validator = bool(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
    )
    payload_has_validated_at = bool(
        payload.get("validated_at") or payload.get("timestamp") or payload.get("generated_at")
    )
    out: dict[str, dict[str, object]] = {}
    for raw_key, raw_item in items.items():
        key = str(raw_key).strip()
        if not key:
            continue
        if isinstance(raw_item, dict):
            classification = str(
                raw_item.get("classification")
                or raw_item.get("judgment")
                or raw_item.get("verdict")
                or raw_item.get("status")
                or ""
            ).strip()
            out[key] = {
                **raw_item,
                "classification": classification,
                "prompt_version": prompt_version,
                "prompt_version_stale": prompt_version_stale,
                "metadata_missing": not bool(
                    (
                        raw_item.get("validator")
                        or raw_item.get("model")
                        or raw_item.get("judge")
                        or raw_item.get("agent")
                        or raw_item.get("generator")
                        or payload_has_validator
                    )
                    and (
                        raw_item.get("validated_at")
                        or raw_item.get("timestamp")
                        or raw_item.get("generated_at")
                        or payload_has_validated_at
                    )
                ),
                "source_record_audit_sha256": str(
                    raw_item.get("source_record_audit_sha256") or payload_audit_digest
                ).strip(),
            }
        else:
            out[key] = {
                "classification": str(raw_item).strip(),
                "prompt_version": prompt_version,
                "prompt_version_stale": prompt_version_stale,
                "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
                "source_record_audit_sha256": payload_audit_digest,
            }
    return out


def check_source_record_audit(
    paper_id: str,
    folder: Path,
    review_surface: dict[str, object],
    status: object,
    strict_assumption_policy: bool,
) -> list[Finding]:
    """Run and validate recursive source-record audit coverage for a paper."""

    severity = assumption_finding_severity(strict_assumption_policy, status)
    payload, error = run_source_record_audit_helper(paper_id)
    if error:
        return [Finding(severity, folder / "PaperInterface.lean", f"`{paper_id}` source-record audit failed: {error}")]
    if payload is None:
        return [Finding(severity, folder / "PaperInterface.lean", f"`{paper_id}` source-record audit produced no payload")]

    field_count = int(payload.get("recursive_field_count") or 0)
    input_count = int(payload.get("boundary_input_count") or 0)
    row_count = len(payload.get("rows_with_record_premises") or [])
    recursion_failures = [
        item for item in payload.get("recursion_failures") or []
        if isinstance(item, dict)
    ]
    if recursion_failures:
        return [
            Finding(
                severity,
                folder / "PaperInterface.lean",
                f"`{paper_id}` source-record recursion failed before reaching source-backed leaves: "
                + "; ".join(
                    str(item.get("path") or item.get("structure") or item)
                    + ": "
                    + str(item.get("message") or item.get("kind") or "unexplained recursion failure")
                    for item in recursion_failures[:5]
                )
                + ("; ..." if len(recursion_failures) > 5 else ""),
            )
        ]
    if field_count <= 0 and input_count <= 0 and row_count <= 0:
        return []

    digest = str(payload.get("source_record_audit_sha256") or "").strip()
    expected_keys = {
        str(key).strip()
        for key in payload.get("expected_field_judgment_keys") or []
        if str(key).strip()
    }
    expected_input_keys = {
        str(key).strip()
        for key in payload.get("expected_input_judgment_keys") or []
        if str(key).strip()
    }
    expected_keys.update(expected_input_keys)
    findings: list[Finding] = []
    audit_file = source_record_audit_file_path(folder, review_surface)
    judgment_file = source_record_judgment_file_path(folder, review_surface)
    saved_audit = load_json_object(audit_file)
    if not saved_audit:
        findings.append(
            Finding(
                severity,
                audit_file,
                f"`{paper_id}` source-record audit found {input_count} boundary-shaped input(s), "
                f"{row_count} record-backed row(s), and {field_count} recursive field(s), but "
                f"`{repo_display_path(audit_file)}` is missing. Run the source-record audit helper "
                "and feed the generated Lean-checked input/field payload to the LLM judge.",
            )
        )
    else:
        saved_digest = str(saved_audit.get("source_record_audit_sha256") or "").strip()
        if digest and saved_digest != digest:
            findings.append(
                Finding(
                    severity,
                    audit_file,
                    f"`{paper_id}` source-record audit payload is stale: saved digest "
                    f"`{saved_digest or 'missing'}` but current digest is `{digest}`.",
                )
            )
        saved_prompt_version = str(saved_audit.get("prompt_version") or "").strip()
        if saved_prompt_version != REQUIRED_SOURCE_RECORD_PROMPT_VERSION:
            findings.append(
                Finding(
                    severity,
                    audit_file,
                    f"`{paper_id}` source-record audit payload prompt version is stale or missing: "
                    f"`{saved_prompt_version or 'missing'}`.",
                )
            )

    judgments = source_record_judgment_items(judgment_file, paper_id)
    if not judgments:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge has {input_count} boundary input(s) and "
                f"{field_count} field(s) requiring LLM provenance judgments, "
                f"but `{repo_display_path(judgment_file)}` is missing or invalid.",
            )
        )
        return findings

    field_items = {
        str(item.get("judgment_key") or "").strip(): item
        for item in payload.get("recursive_field_items") or []
        if isinstance(item, dict) and str(item.get("judgment_key") or "").strip()
    }
    nested_children: dict[str, set[str]] = {}
    for key, item in field_items.items():
        children: set[str] = set()
        for nested_name in item.get("nested_structures") or []:
            nested = str(nested_name).strip()
            if not nested:
                continue
            children.update(
                child_key for child_key, child in field_items.items()
                if str(child.get("structure") or "").strip() == nested
            )
        nested_children[key] = children

    missing = sorted(expected_keys - set(judgments))
    extra = sorted(set(judgments) - expected_keys)
    unresolved = sorted(
        key
        for key, item in judgments.items()
        if key in expected_keys
        and str(item.get("classification") or "").strip() not in APPROVED_SOURCE_RECORD_CLASSIFICATIONS
    )
    stale_prompt = sorted(
        key for key, item in judgments.items() if key in expected_keys and item.get("prompt_version_stale")
    )
    missing_metadata = sorted(
        key for key, item in judgments.items() if key in expected_keys and item.get("metadata_missing")
    )
    stale_judgment_digest = sorted(
        key
        for key, item in judgments.items()
        if key in expected_keys
        and digest
        and str(item.get("source_record_audit_sha256") or "").strip() != digest
    )
    invalid_context: list[str] = []
    for key in sorted((expected_keys - expected_input_keys) & set(judgments)):
        classification = str(judgments[key].get("classification") or "").strip()
        field_item = field_items.get(key, {})
        nested = [str(name).strip() for name in field_item.get("nested_structures") or [] if str(name).strip()]
        if classification == "approved_external_boundary" and status in {"formalized", "formalized with caveat"}:
            invalid_context.append(
                f"{key} classified `approved_external_boundary` but paper status is `{status}`"
            )
        if nested and classification not in {
            "container_recursively_audited",
            "approved_external_boundary",
            "derived_consequence_record",
        }:
            invalid_context.append(
                f"{key} classified `{classification or 'missing'}` but points to nested source record(s) "
                + ", ".join(nested)
            )
        if classification == "container_recursively_audited":
            children = nested_children.get(key, set())
            if not nested or not children:
                invalid_context.append(
                    f"{key} classified `container_recursively_audited` but no nested audited field judgments were found"
                )
                continue
            bad_children = sorted(
                child for child in children
                if child not in judgments
                or str(judgments[child].get("classification") or "").strip()
                not in APPROVED_SOURCE_RECORD_CLASSIFICATIONS
            )
            if bad_children:
                invalid_context.append(
                    f"{key} classified `container_recursively_audited` but nested field(s) are missing/unapproved: "
                    + ", ".join(bad_children[:5])
                    + ("; ..." if len(bad_children) > 5 else "")
                )
        if classification == "nonpropositional_witness_data" and nested:
            invalid_context.append(
                f"{key} classified `nonpropositional_witness_data` but points to nested source record(s) "
                + ", ".join(nested)
            )
    for key in sorted(expected_input_keys & set(judgments)):
        classification = str(judgments[key].get("classification") or "").strip()
        source_location = str(
            judgments[key].get("source_location")
            or judgments[key].get("source_evidence")
            or judgments[key].get("source_key")
            or judgments[key].get("paper_statement_key")
            or ""
        ).strip()
        lean_derivation = str(
            judgments[key].get("lean_derivation")
            or judgments[key].get("constructor")
            or judgments[key].get("derived_from")
            or judgments[key].get("derivation")
            or ""
        ).strip()
        if classification in {"container_recursively_audited", "nonpropositional_witness_data"}:
            invalid_context.append(
                f"{key} classified `{classification}` but boundary-shaped theorem inputs need "
                "source evidence, a Lean derivation, approved external-boundary status, or unresolved status"
            )
        if classification == "validated_source_assumption" and not source_location:
            invalid_context.append(
                f"{key} classified `validated_source_assumption` but gives no source key/location/evidence"
            )
        if classification == "proved_from_primitives" and not lean_derivation:
            invalid_context.append(
                f"{key} classified `proved_from_primitives` but gives no Lean constructor/derivation"
            )
        if classification == "approved_external_boundary" and status in {"formalized", "formalized with caveat"}:
            invalid_context.append(
                f"{key} classified `approved_external_boundary` but paper status is `{status}`"
            )
    if missing:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge is missing {len(missing)} boundary/source-record judgment(s): "
                + ", ".join(missing[:8])
                + ("; ..." if len(missing) > 8 else ""),
            )
        )
    if extra:
        findings.append(
            Finding(
                "WARN",
                judgment_file,
                f"`{paper_id}` source-record judge has {len(extra)} stale/extra boundary/source-record judgment(s): "
                + ", ".join(extra[:8])
                + ("; ..." if len(extra) > 8 else ""),
            )
        )
    if unresolved:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge marks {len(unresolved)} boundary/source-record item(s) as unresolved or unapproved: "
                + ", ".join(unresolved[:8])
                + ("; ..." if len(unresolved) > 8 else ""),
            )
        )
    if stale_prompt:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge uses stale or missing prompt version for "
                f"{len(stale_prompt)} item(s): "
                + ", ".join(stale_prompt[:8])
                + ("; ..." if len(stale_prompt) > 8 else ""),
            )
        )
    if missing_metadata:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge lacks validator/timestamp success metadata for "
                f"{len(missing_metadata)} item(s): "
                + ", ".join(missing_metadata[:8])
                + ("; ..." if len(missing_metadata) > 8 else ""),
            )
        )
    if stale_judgment_digest:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge has {len(stale_judgment_digest)} item(s) "
                "not tied to the current source_record_audit_sha256: "
                + ", ".join(stale_judgment_digest[:8])
                + ("; ..." if len(stale_judgment_digest) > 8 else ""),
            )
        )
    if invalid_context:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge has {len(invalid_context)} context-invalid classification(s): "
                + "; ".join(invalid_context[:5])
                + ("; ..." if len(invalid_context) > 5 else ""),
            )
        )
    return findings


def _source_record_source_location(judgment: dict[str, object]) -> str:
    return str(
        judgment.get("source_location")
        or judgment.get("source_evidence")
        or judgment.get("source_key")
        or judgment.get("paper_statement_key")
        or ""
    ).strip()


def _source_record_lean_derivation(judgment: dict[str, object]) -> str:
    return str(
        judgment.get("lean_derivation")
        or judgment.get("constructor")
        or judgment.get("derived_from")
        or judgment.get("derivation")
        or ""
    ).strip()


def _source_record_boundary_input_is_validated(
    judgment: dict[str, object],
    *,
    digest: str,
    status: object,
) -> bool:
    """Return true only for current source-record judgments that route theorem inputs.

    Source-record inputs are an alternate explicit provenance lane for visible
    source-model/source-row premises.  This should not weaken the hidden-premise
    audit: missing metadata, stale prompts, unresolved judgments, partial
    external boundaries in completed papers, or missing source/derivation
    evidence all fail closed here and remain hidden-premise findings.
    """

    classification = str(judgment.get("classification") or "").strip()
    if classification not in APPROVED_SOURCE_RECORD_CLASSIFICATIONS:
        return False
    if judgment.get("prompt_version_stale") or judgment.get("metadata_missing"):
        return False
    if digest and str(judgment.get("source_record_audit_sha256") or "").strip() != digest:
        return False
    if classification in {"container_recursively_audited", "nonpropositional_witness_data"}:
        return False
    if classification == "approved_external_boundary" and status in {"formalized", "formalized with caveat"}:
        return False
    if classification == "validated_source_assumption" and not _source_record_source_location(judgment):
        return False
    if classification == "proved_from_primitives" and not _source_record_lean_derivation(judgment):
        return False
    return True


def source_record_validated_boundary_premises(
    paper_id: str,
    folder: Path,
    review_surface: dict[str, object],
    status: object,
) -> set[str]:
    """Return visible theorem premises routed through current source-record judgments."""

    audit_file = source_record_audit_file_path(folder, review_surface)
    saved_audit = load_json_object(audit_file)
    if not saved_audit:
        return set()
    digest = str(saved_audit.get("source_record_audit_sha256") or "").strip()
    if str(saved_audit.get("prompt_version") or "").strip() != REQUIRED_SOURCE_RECORD_PROMPT_VERSION:
        return set()

    judgment_file = source_record_judgment_file_path(folder, review_surface)
    judgments = source_record_judgment_items(judgment_file, paper_id)
    if not judgments:
        return set()

    routed: set[str] = set()
    for raw_item in saved_audit.get("boundary_input_items") or []:
        if not isinstance(raw_item, dict):
            continue
        key = str(raw_item.get("judgment_key") or "").strip()
        if not key:
            continue
        judgment = judgments.get(key)
        if not isinstance(judgment, dict):
            continue
        if not _source_record_boundary_input_is_validated(judgment, digest=digest, status=status):
            continue
        raw_input = raw_item.get("input")
        if not isinstance(raw_input, dict):
            continue
        names = str(raw_input.get("names") or "").strip()
        type_text = str(raw_input.get("type") or "").strip()
        if names and type_text:
            routed.add(normalize_premise_text(f"{names} : {type_text}"))
            routed.add(premise_type_text(f"{names} : {type_text}"))
    return routed


def current_statement_conditional_boundary_rows(folder: Path) -> set[str]:
    """Return rows with current LLM-reviewed conditional statement boundaries."""

    path = paper_relative_file(
        folder, f"{PAPER_AUDIT_DIR}/statement_match_llm.json", "statement_match_llm.json"
    )
    payload = load_json_object(path)
    if not payload or payload.get("schema") != 1:
        return set()
    if payload.get("paper") not in {None, folder.name}:
        return set()
    if str(payload.get("prompt_version") or "").strip() != REQUIRED_LLM_STATEMENT_PROMPT_VERSION:
        return set()
    items = payload.get("items")
    if not isinstance(items, dict):
        return set()
    payload_has_validator = bool(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
    )
    payload_has_validated_at = bool(
        payload.get("validated_at") or payload.get("timestamp") or payload.get("generated_at")
    )
    out: set[str] = set()
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if not name or not isinstance(raw_value, dict):
            continue
        judgment = str(
            raw_value.get("judgment")
            or raw_value.get("verdict")
            or raw_value.get("status")
            or ""
        ).strip().lower()
        resolution = str(
            raw_value.get("resolution")
            or raw_value.get("accepted_resolution")
            or raw_value.get("review_resolution")
            or ""
        ).strip().lower()
        has_validator = bool(
            raw_value.get("validator")
            or raw_value.get("model")
            or raw_value.get("judge")
            or raw_value.get("agent")
            or raw_value.get("generator")
            or payload_has_validator
        )
        has_validated_at = bool(
            raw_value.get("validated_at")
            or raw_value.get("timestamp")
            or raw_value.get("generated_at")
            or payload_has_validated_at
        )
        if (
            judgment in {"mismatch", "does_not_match", "no", "false"}
            and resolution in {"conditional_boundary", "documented_boundary", "accepted_conditional_boundary"}
            and has_validator
            and has_validated_at
        ):
            out.add(name)
    return out


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
        "documented_additional_assumption",
        "documented additional assumption",
        "additional_assumption",
        "additional assumption",
        "human_approved_additional_assumption",
        "human approved additional assumption",
    }:
        return "documented_additional_assumption"
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


def premise_type_text(premise: str) -> str:
    """Return the normalized type side of a premise string.

    Lean pretty-prints unused proof arguments in expanded `#check` output as
    anonymous arrows (`SomeRows ... → ...`) rather than named binders.  The
    assumption ledger records the corresponding `-- audit-premise:` comments
    with human-readable names.  Matching on the type side lets the audit route
    those anonymous arrows through the same explicit source-assumption rows.
    """

    normalized = normalize_premise_text(premise)
    def dequalify(text: str) -> str:
        return re.sub(
            r"\b(?:[A-Za-z_][A-Za-z0-9_']*\.)+([A-Za-z_][A-Za-z0-9_']*)",
            r"\1",
            text,
        )

    if " : " in normalized:
        return dequalify(normalized.split(" : ", 1)[1].strip())
    if normalized.startswith("anonymous : "):
        return dequalify(normalized.split(" : ", 1)[1].strip())
    return dequalify(normalized)


def is_review_explicit_boundary_premise(premise: str) -> bool:
    """Return true when a premise's type head is a source/proof boundary.

    This intentionally looks at the type head rather than the full expression:
    ordinary source formulas can mention helper constants whose names contain
    `Certificate` without themselves being certificate assumptions.
    The head check is case-sensitive for suffixes such as `Table`; otherwise
    ordinary source predicates such as `stable` or `AllPairsAcceptable` are
    misclassified because they end in the letters "table".
    """

    type_text = premise_type_text(premise)
    head = type_text.strip().split(None, 1)[0].strip("(){}[]")
    short_head = head.rsplit(".", 1)[-1]
    boundary_suffixes = (
        "Certificate",
        "Oracle",
        "External",
        "Boundary",
        "Bridge",
        "SourceModel",
        "SourceFamilyRows",
        "SourceRows",
        "SourceTable",
        "Rows",
        "Table",
        "Package",
        "Window",
        "Windows",
        "Replay",
        "Process",
    )
    return short_head.endswith(boundary_suffixes) or re.search(
        r"\b(?:source[-_ ]?rows?|source[-_ ]?table|row[-_ ]?package)\b",
        type_text,
        re.I,
    ) is not None


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


def load_expanded_review_statements(folder: Path) -> dict[str, tuple[str, int]]:
    """Load dashboard-expanded Lean statements keyed by review row name."""

    path = folder / REVIEW_TRACE_CACHE
    if not path.exists() or not path.is_file():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(payload, dict):
        return {}
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return {}
    expanded: dict[str, tuple[str, int]] = {}
    for raw_row in rows:
        if not isinstance(raw_row, dict):
            continue
        name = str(raw_row.get("name") or "").strip()
        lean_statement = str(raw_row.get("lean_statement") or "").strip()
        if not name or not lean_statement:
            continue
        raw_line = raw_row.get("line_number")
        line_number = raw_line if isinstance(raw_line, int) else 0
        expanded[name] = (lean_statement, line_number)
    return expanded


def expanded_statement_boundary_premises(
    lean_statement: str, assumption_names: set[str]
) -> list[str]:
    """Return source-boundary binders visible only after Lean `#check` expansion."""

    hidden: list[str] = []
    for match in LEAN_BINDER_RE.finditer(lean_statement):
        names = _binder_names(match.group(1))
        type_text = match.group(2).strip()
        if not names:
            continue
        if any(name in assumption_names for name in names):
            continue
        if any(assumption in type_text for assumption in assumption_names):
            continue
        premise = normalize_premise_text(f"{' '.join(names)} : {type_text}")
        if is_review_explicit_boundary_premise(premise):
            hidden.append(premise)
    hidden.extend(expanded_statement_anonymous_boundary_premises(lean_statement))
    return list(dict.fromkeys(hidden))


def expanded_statement_anonymous_boundary_premises(lean_statement: str) -> list[str]:
    """Return anonymous top-level proof-boundary arrows in expanded output.

    Lean omits binder names for proof arguments that are not referenced in the
    theorem's result type, printing them as top-level arrows:

        SomeSourceRows ... → OtherRows ... → conclusion

    These are still theorem premises and must route through `Assumptions.lean`
    when they are source-row/certificate boundaries.
    """

    text = normalize_premise_text(lean_statement)
    pieces: list[str] = []
    current: list[str] = []
    depth = 0
    for char in text:
        if char in "([{⦃":
            depth += 1
        elif char in ")]}⦄" and depth > 0:
            depth -= 1
        if char == "→" and depth == 0:
            pieces.append("".join(current).strip())
            current = []
            continue
        current.append(char)
    hidden: list[str] = []
    for piece in pieces:
        candidate = piece.rsplit(",", 1)[-1].strip()
        if not candidate or " : " in candidate:
            continue
        if is_review_explicit_boundary_premise(candidate):
            hidden.append(normalize_premise_text(f"anonymous : {candidate}"))
    return hidden


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
        if is_review_explicit_boundary_premise(premise)
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


def library_reference_target_map(
    declarations: list[LeanDeclaration],
    library_declaration_index: dict[str, list[LeanDeclaration]],
) -> dict[tuple[Path, int, str], list[LeanDeclaration]]:
    """Resolve reusable-library declaration references once for fixed-point scans."""

    out: dict[tuple[Path, int, str], list[LeanDeclaration]] = {}
    for declaration in declarations:
        targets: list[LeanDeclaration] = []
        seen: set[tuple[Path, int, str]] = set()
        for reference in declaration_reference_names(declaration.source):
            for target in resolve_library_target(library_declaration_index, reference):
                key = declaration_key(target)
                if key == declaration_key(declaration) or key in seen:
                    continue
                seen.add(key)
                targets.append(target)
        out[declaration_key(declaration)] = targets
    return out


def declaration_result_type_text(source: str) -> str:
    header = declaration_header(source)
    if " : " not in header:
        return ""
    return normalize_premise_text(header.rsplit(" : ", 1)[1])


def declaration_result_type_head(declaration: LeanDeclaration) -> str:
    result = declaration_result_type_text(declaration.source)
    if not result:
        return ""
    return result.strip().split(None, 1)[0].strip("(){}[]").rsplit(".", 1)[-1]


def boundary_type_alias_map(declarations: list[LeanDeclaration]) -> dict[str, set[str]]:
    """Discover transparent boundary aliases from declarations.

    Standard/template: a boundary alias is a declaration of the form
    `def Alias ... : Prop := Target ...`, where both `Alias` and `Target` have
    certificate/source-boundary-shaped heads. This lets the audit recognize
    closed constructors for definitionally equivalent certificate types without
    naming paper- or library-specific functions.
    """

    aliases: dict[str, set[str]] = {}
    for declaration in declarations:
        if declaration.kind != "def":
            continue
        if declaration_result_type_text(declaration.source) != "Prop":
            continue
        alias_head = declaration.name.rsplit(".", 1)[-1]
        if not LIBRARY_BOUNDARY_TYPE_RE.fullmatch(alias_head):
            continue
        body = lean_code_text(declaration_body(declaration.source)).strip()
        match = DECLARATION_REFERENCE_RE.search(body)
        if not match:
            continue
        target_head = match.group(0).rsplit(".", 1)[-1]
        if not LIBRARY_BOUNDARY_TYPE_RE.fullmatch(target_head):
            continue
        aliases.setdefault(alias_head, set()).add(target_head)

    changed = True
    while changed:
        changed = False
        for alias, targets in list(aliases.items()):
            expanded = set(targets)
            for target in list(targets):
                expanded.update(aliases.get(target, set()))
            if not expanded.issubset(targets):
                aliases[alias] = targets | expanded
                changed = True
    return aliases


def boundary_type_heads_for_premise(
    premise: str,
    boundary_aliases: dict[str, set[str]] | None = None,
) -> set[str]:
    type_text = premise_type_text(premise)
    head = type_text.strip().split(None, 1)[0].strip("(){}[]")
    unqualified = head.rsplit(".", 1)[-1]
    heads = {unqualified}
    if boundary_aliases:
        heads.update(boundary_aliases.get(unqualified, set()))
    return heads


def references_discharge_boundary(
    referenced_targets: list[LeanDeclaration],
    dependency_indexes: list[dict[tuple[Path, int, str], list[BoundaryDependency]]],
    premise: str,
    boundary_aliases: dict[str, set[str]],
) -> bool:
    """Return true when references include a closed constructor for `premise`.

    Standard/template: a constructor discharges a boundary only when it returns
    the same boundary type head (modulo transparent boundary aliases) and the
    constructor itself has no currently known boundary dependencies.
    """

    type_heads = boundary_type_heads_for_premise(premise, boundary_aliases)
    for target in referenced_targets:
        target_key = declaration_key(target)
        if any(target_key in dependency_index for dependency_index in dependency_indexes):
            continue
        if declaration_result_type_head(target) in type_heads:
            return True
    return False


def referenced_library_boundary_dependencies(
    referenced_targets: list[LeanDeclaration],
    library_boundary_dependency_index: dict[tuple[Path, int, str], list[BoundaryDependency]],
    boundary_aliases: dict[str, set[str]],
) -> list[BoundaryDependency]:
    """Return certificate dependencies of referenced reusable-library declarations."""

    dependencies: list[BoundaryDependency] = []
    seen_targets: set[tuple[Path, int, str]] = set()
    for target in referenced_targets:
        target_key = declaration_key(target)
        if target_key in seen_targets:
            continue
        seen_targets.add(target_key)
        for dependency in library_boundary_dependency_index.get(target_key, []):
            if references_discharge_boundary(
                referenced_targets,
                [library_boundary_dependency_index],
                dependency.premise,
                boundary_aliases,
            ):
                continue
            dependencies.append(
                BoundaryDependency(
                    category=dependency.category,
                    premise=dependency.premise,
                    declaration=dependency.declaration,
                    via=target.name,
                )
            )
    return dedupe_boundary_dependencies(dependencies)


def merge_boundary_alias_maps(*maps: dict[str, set[str]]) -> dict[str, set[str]]:
    out: dict[str, set[str]] = {}
    for mapping in maps:
        for key, values in mapping.items():
            out.setdefault(key, set()).update(values)
    return out


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
    reference_targets = library_reference_target_map(declarations, declaration_index)
    boundary_aliases = boundary_type_alias_map(declarations)
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
            propagated = referenced_library_boundary_dependencies(
                reference_targets.get(key, []),
                dependencies,
                boundary_aliases,
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
    library_reference_targets = library_reference_target_map(declarations, library_declaration_index)
    boundary_aliases = merge_boundary_alias_maps(
        boundary_type_alias_map(unique_declarations(library_declaration_index)),
        boundary_type_alias_map(declarations),
    )
    dependencies: dict[tuple[Path, int, str], list[BoundaryDependency]] = {}
    for declaration in declarations:
        key = declaration_key(declaration)
        direct = referenced_library_boundary_dependencies(
            library_reference_targets.get(key, []),
            library_boundary_dependencies,
            boundary_aliases,
        )
        if direct:
            dependencies[key] = direct

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
                    if references_discharge_boundary(
                        reference_targets.get(key, []) + library_reference_targets.get(key, []),
                        [dependencies, library_boundary_dependencies],
                        dependency.premise,
                        boundary_aliases,
                    ):
                        continue
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
    boundary_aliases = boundary_type_alias_map(declarations)
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
                    if references_discharge_boundary(
                        reference_targets.get(key, []),
                        [dependencies],
                        dependency.premise,
                        boundary_aliases,
                    ):
                        continue
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


def check_library_source_assumption_standards() -> list[Finding]:
    """Reject source assumptions as reusable-library API objects.

    Reusable code may expose explicit certificates/oracles for external
    mathematical facts.  It should not define reusable `Assumption` or
    `Hypothesis` records: those are paper-local provenance objects and must live
    in a paper folder where the source text and LLM/human judgments can validate
    them directly.
    """

    findings: list[Finding] = []
    seen: set[tuple[Path, int, str]] = set()
    for declaration in unique_declarations(library_lean_declaration_index()):
        key = declaration_key(declaration)
        if key in seen:
            continue
        seen.add(key)
        if re.match(r"\s*private\s+", declaration.source):
            continue
        if LIBRARY_FORBIDDEN_SOURCE_ASSUMPTION_RE.search(declaration.name):
            findings.append(
                Finding(
                    "ERROR",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} uses "
                    "`Assumption`/`Hypothesis` naming; paper assumptions must live in "
                    "paper-local `Assumptions.lean`, and reusable APIs should require "
                    "generic certificates or derived proofs instead",
                )
            )
        if ASSUMPTION_AUDIT_PREMISE_RE.search(declaration.source):
            findings.append(
                Finding(
                    "ERROR",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} contains "
                    "`audit-premise`; source-premise validation belongs in paper-local "
                    "`Assumptions.lean`, not reusable library code",
                )
            )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def check_library_reusable_provenance_language() -> list[Finding]:
    """Reject paper/source-provenance wording in reusable Lean modules."""

    findings: list[Finding] = []
    for path in library_lean_files():
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        for line_no, line in enumerate(text.splitlines(), start=1):
            match = REUSABLE_LIBRARY_PROVENANCE_TEXT_RE.search(line)
            if not match:
                continue
            findings.append(
                Finding(
                    "ERROR",
                    path,
                    f"reusable library line {line_no} uses paper/source-provenance "
                    f"wording `{match.group(0)}`; put source-text provenance in "
                    "paper-local files and describe shared declarations as generic "
                    "mathematical APIs",
                )
            )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def check_library_standard_definition_audits() -> list[Finding]:
    """Require Lean-checked audit lemmas for standard-name definitions."""

    findings: list[Finding] = []
    audit_file = LIBRARY_STANDARD_DEFINITION_AUDIT_FILE
    if not audit_file.exists():
        return [
            Finding(
                "ERROR",
                audit_file,
                "missing reusable definition audit module; standard mathematical "
                "wrappers need build-checked equivalence lemmas",
            )
        ]

    text = audit_file.read_text(encoding="utf-8")
    root_module = ROOT / "EconCSLib.lean"
    if root_module.exists() and "import EconCSLib.LibraryDefinitionAudit" not in root_module.read_text(
        encoding="utf-8"
    ):
        findings.append(
            Finding(
                "ERROR",
                root_module,
                "`EconCSLib.LibraryDefinitionAudit` should be imported by the root "
                "library target so CI builds the standard-definition checks",
            )
        )

    for decl_name, description in REQUIRED_LIBRARY_STANDARD_AUDITS.items():
        if not re.search(rf"^\s*(?:theorem|lemma)\s+{re.escape(decl_name)}\b", text, re.M):
            findings.append(
                Finding(
                    "ERROR",
                    audit_file,
                    f"missing standard-definition audit `{decl_name}` ({description})",
                )
            )
    return findings


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

        status_file = folder / "status.json"
        review_surface: dict[str, object] = {}
        if status_file.exists():
            try:
                payload = json.loads(status_file.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                payload = {}
            if isinstance(payload, dict) and isinstance(payload.get("review_surface"), dict):
                review_surface = payload["review_surface"]  # type: ignore[assignment]
        review_source = review_surface_source_file_path(folder, review_surface)
        if not review_source.exists():
            findings.append(Finding("ERROR", review_source, "configured review surface does not exist"))
            continue
        review_source_text = review_source.read_text(encoding="utf-8")
        item_count = len(review_rows_from_interface_text(review_source_text))
        if item_count == 0:
            findings.append(Finding("ERROR", review_source, "review dashboard finds no review rows"))
        elif item_count > REVIEW_ROW_WARN_THRESHOLD:
            problems, counts = review_surface_slice_counts(review_source_text, status_file)
            for problem in sorted(set(problems)):
                findings.append(Finding("ERROR", status_file, problem))
            max_slice = max(counts.values()) if counts else item_count
            if not status_file.exists():
                findings.append(
                    Finding(
                        "WARN",
                        review_source,
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
    template = PAPERS / "TEMPLATE" / DEPENDENCY_DAG_TEX_FILE
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

        review_surface: dict[str, object] = {}
        status_file = folder / "status.json"
        if status_file.exists():
            try:
                status_payload = json.loads(status_file.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                status_payload = {}
            if isinstance(status_payload, dict) and isinstance(status_payload.get("review_surface"), dict):
                review_surface = status_payload["review_surface"]  # type: ignore[assignment]
        review_source = review_surface_source_file_path(folder, review_surface)
        ledger_candidates = [folder / "MainTheorems.lean", folder / "PaperInterface.lean"]
        if review_source.exists() and review_source not in ledger_candidates:
            ledger_candidates.append(review_source)
        existing = [path for path in ledger_candidates if path.exists()]
        if not existing:
            continue

        for ledger in existing:
            text = ledger.read_text(encoding="utf-8")
            if LEDGER_PLACEHOLDER_RE.search(text):
                findings.append(
                    Finding("ERROR", ledger, "paper-facing ledger still contains template placeholders")
                )
            compact_import_shim = (
                ledger.name == "PaperInterface.lean"
                and review_source.exists()
                and review_source.resolve() != ledger.resolve()
            )
            if not compact_import_shim and not LEAN_DECL_RE.search(text):
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
    interface_required = {
        folder.name
        for folder in paper_dirs()
        if is_closeout_status(paper_local_status(folder))
    }

    for folder in paper_dirs():
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue

        interface = folder / "PaperInterface.lean"
        audit = folder / "PostPaperAudit.lean"
        report = paper_relative_file(
            folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
        )
        aggregator = PAPERS / f"{folder.name}.lean"
        review_surface: dict[str, object] = {}
        status_file = folder / "status.json"
        if status_file.exists():
            try:
                status_payload = json.loads(status_file.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                status_payload = {}
            if isinstance(status_payload, dict) and isinstance(status_payload.get("review_surface"), dict):
                review_surface = status_payload["review_surface"]  # type: ignore[assignment]
        review_source = review_surface_source_file_path(folder, review_surface)
        human_interface = review_source if review_source.exists() else interface

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
        if human_interface.exists():
            text = human_interface.read_text(encoding="utf-8")
            if "PProd" in text:
                findings.append(
                    Finding("ERROR", human_interface, "human-facing interface should not use tuple witnesses")
                )
            if INTERFACE_WITNESS_RE.search(text):
                findings.append(
                    Finding(
                        "ERROR",
                        human_interface,
                        "human-facing interface should not expose tuple/prod witness declarations",
                    )
                )
            if not re.search(r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+", text, re.M):
                findings.append(
                    Finding(
                        "WARN",
                        human_interface,
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
                    Finding("WARN", human_interface, "human-facing interface has no visible theorem statements")
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

        post_audit = paper_relative_file(
            folder, POST_FORMALIZATION_AUDIT_FILE, "POST_FORMALIZATION_AUDIT.md"
        )
        for markdown_report in (report, post_audit):
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


def check_machine_paper_status(
    library_premise_audit: bool = False,
    paper_filter: str | None = None,
) -> list[Finding]:
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
    using_paper_local_fallback = False
    if paper_filter is not None and not any(
        isinstance(entry, dict) and entry.get("id") == paper_filter for entry in papers
    ):
        local_status = PAPERS / paper_filter / "status.json"
        if local_status.exists():
            try:
                local_payload = json.loads(local_status.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                findings.append(Finding("ERROR", local_status, f"invalid JSON: {exc.msg}"))
                local_payload = None
            if isinstance(local_payload, dict):
                papers = [local_payload]
                using_paper_local_fallback = True

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
        if paper_filter is not None and paper_id != paper_filter:
            continue

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
        proof_boundary_names, proof_boundary_name_problems = review_surface_proof_boundary_names(review_surface)
        for problem in proof_boundary_name_problems:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` {problem}"))
        missing_boundary_assumptions = proof_boundary_names - assumption_names
        if missing_boundary_assumptions:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` proof_boundary_names must also be listed in "
                    "`review_surface.assumption_names`: "
                    + ", ".join(sorted(missing_boundary_assumptions)),
                )
            )
        auxiliary_names, auxiliary_name_problems = review_surface_auxiliary_names(review_surface)
        for problem in auxiliary_name_problems:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` {problem}"))
        auxiliary_overlap = auxiliary_names.intersection(set(include_names)).union(
            auxiliary_names.intersection(assumption_names)
        )
        if auxiliary_overlap:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` auxiliary_names overlap reviewed or assumption declarations: "
                    + ", ".join(sorted(auxiliary_overlap)),
                )
            )
        assumption_policy = str(review_surface.get("assumption_policy") or "").strip().lower()
        strict_assumption_policy = assumption_policy in ASSUMPTION_POLICY_STRICT_VALUES
        if assumption_policy and assumption_policy not in ASSUMPTION_POLICY_ALLOWED_VALUES:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}.review_surface.assumption_policy` should be one of "
                    + ", ".join(sorted(ASSUMPTION_POLICY_ALLOWED_VALUES)),
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
        review_source_path = review_surface_source_file_path(PAPERS / paper_id, review_surface)
        if not review_source_path.exists():
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` review surface source file does not exist: "
                    f"`{review_source_path.relative_to(ROOT)}`",
                )
            )
            continue
        review_source_text = review_source_path.read_text(encoding="utf-8")
        review_source_is_interface = review_source_path.resolve() == interface_path.resolve()
        audit_surface_value = interface.get("audit_surface_path")
        if review_source_is_interface:
            if actual_line_count > PAPER_INTERFACE_COMPACT_LINE_THRESHOLD:
                findings.append(
                    Finding(
                        "ERROR",
                        PAPER_STATUS_FILE,
                        f"`{paper_id}` PaperInterface.lean has {actual_line_count} lines; "
                        "move row-level dashboard or LLM audit declarations into "
                        "`AuditInterface.lean` and keep `PaperInterface.lean` compact",
                    )
                )
        else:
            if actual_line_count > PAPER_INTERFACE_COMPACT_LINE_THRESHOLD:
                findings.append(
                    Finding(
                        "ERROR",
                        PAPER_STATUS_FILE,
                        f"`{paper_id}` compact PaperInterface.lean has {actual_line_count} lines "
                        f"even though review rows are routed through "
                        f"`{review_source_path.relative_to(ROOT)}`",
                    )
                )
            if not isinstance(audit_surface_value, str) or not audit_surface_value.strip():
                findings.append(
                    Finding(
                        "ERROR",
                        PAPER_STATUS_FILE,
                        f"`{paper_id}.paper_interface.audit_surface_path` should name the "
                        "non-compact review surface when `review_surface.source_file` is not "
                        "`PaperInterface.lean`",
                    )
                )
            else:
                audit_surface_path = ROOT / audit_surface_value.strip()
                if audit_surface_path.resolve() != review_source_path.resolve():
                    findings.append(
                        Finding(
                            "ERROR",
                            PAPER_STATUS_FILE,
                            f"`{paper_id}.paper_interface.audit_surface_path` "
                            f"({audit_surface_value}) should match "
                            f"`review_surface.source_file` "
                            f"({review_source_path.relative_to(ROOT)})",
                        )
                    )
                if review_source_path.name != "AuditInterface.lean":
                    findings.append(
                        Finding(
                            "WARN",
                            PAPER_STATUS_FILE,
                            f"`{paper_id}` uses `{review_source_path.relative_to(ROOT)}` as the "
                            "non-compact review surface; prefer `AuditInterface.lean` for "
                            "row-level dashboard and LLM audit declarations",
                        )
                    )
        findings.extend(
            paper_statement_sidecar_findings(
                paper_id,
                PAPERS / paper_id,
                status,
            )
        )
        actual_review_names = [
            name for _line, name in review_rows_from_interface_text(review_source_text)
        ]
        declaration_blocks = review_declaration_blocks(review_source_text)
        declaration_comments = review_declaration_comments(review_source_text)
        declaration_index = paper_lean_declaration_index(PAPERS / paper_id)
        assumption_source_file = assumption_source_file_path(PAPERS / paper_id, review_surface)
        assumption_declarations = assumption_declarations_from_file(assumption_source_file)
        assumption_file_premises = assumption_premises_from_file(assumption_source_file)
        assumption_judgments: dict[str, dict[str, object]] = {}
        validated_assumption_premises: set[str] = set()
        validated_assumption_premise_types: set[str] = set()
        accepted_conditional_boundary_rows = (
            set()
            if status in {"formalized", "formalized with caveat"}
            else current_statement_conditional_boundary_rows(PAPERS / paper_id)
        )
        hidden_premise_finding_keys: set[tuple[Path, int, str, str, tuple[str, ...]]] = set()
        hidden_premise_severity = assumption_finding_severity(strict_assumption_policy, status)

        def add_hidden_premise_finding(
            declaration: LeanDeclaration,
            hidden: list[str],
            context: str,
            row_name: str | None = None,
        ) -> None:
            if row_name and row_name in accepted_conditional_boundary_rows:
                return
            hidden = list(dict.fromkeys(
                premise
                for premise in hidden
                if normalize_premise_text(premise) not in validated_assumption_premises
                and premise_type_text(premise) not in validated_assumption_premise_types
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
                    f"`{paper_id}` assumption_names are not exported by the review surface or "
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
        findings.extend(
            check_paper_interface_axiom_closure(
                paper_id,
                review_source_path,
                review_source_text,
                include_names,
                declaration_blocks,
                status,
                proof_boundary_names,
            )
        )
        source_record_findings = check_source_record_audit(
            paper_id,
            PAPERS / paper_id,
            review_surface,
            status,
            strict_assumption_policy,
        )
        findings.extend(source_record_findings)
        if not any(finding.severity == "ERROR" for finding in source_record_findings):
            for premise in source_record_validated_boundary_premises(
                paper_id,
                PAPERS / paper_id,
                review_surface,
                status,
            ):
                validated_assumption_premises.add(normalize_premise_text(premise))
                validated_assumption_premise_types.add(premise_type_text(premise))
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
                            "`paper_assumption`, `paper_condition`, "
                            "`documented_additional_assumption`, `documented_caveat`, "
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
                                validated_assumption_premise_types.add(premise_type_text(premise))
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
                        validated_assumption_premise_types.add(premise_type_text(premise))
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
        expanded_review_statements = load_expanded_review_statements(PAPERS / paper_id)
        for name, (expanded_statement, expanded_line) in expanded_review_statements.items():
            if name in assumption_names or is_assumption_decl_name(name):
                continue
            expanded_boundary_premises = expanded_statement_boundary_premises(
                expanded_statement,
                assumption_names,
            )
            if not expanded_boundary_premises:
                continue
            declaration = declaration_blocks.get(name)
            if declaration:
                line_no, kind, source = declaration
            else:
                line_no = expanded_line or 1
                kind = "abbrev"
                source = expanded_statement
            add_hidden_premise_finding(
                LeanDeclaration(
                    path=review_source_path,
                    line=line_no,
                    kind=kind,
                    name=name,
                    source=source,
                ),
                expanded_boundary_premises,
                "expanded review row",
                row_name=name,
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
                        review_source_path,
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
                        review_source_path,
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
                        review_source_path,
                        f"`{paper_id}` formula-bearing review row `{name}` at line {line_no} is an "
                        "opaque alias/signature; expose the displayed formula or theorem subclaim "
                        "directly, or route any non-derived premise through Assumptions.lean",
                    )
                )
            if formula_facing_row and re.search(r"source[-_ ]rows?", comment_and_name, re.I):
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        review_source_path,
                        f"`{paper_id}` review row `{name}` at line {line_no} mentions a source-row "
                        "formula boundary; source-row wrappers are partial endpoints unless derived "
                        "from primitives or validated as explicit paper assumptions",
                    )
            )
            if kind in {"theorem", "lemma", "def", "abbrev"} and name not in assumption_names and not is_assumption_decl_name(name):
                row_declaration = LeanDeclaration(
                    path=review_source_path,
                    line=line_no,
                    kind=kind,
                    name=name,
                    source=source,
                )
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
                        row_name=name,
                    )
                alias_targets = resolve_paper_local_alias_chain(declaration_index, source)
                for target_declaration in alias_targets:
                    if target_declaration.name in assumption_names or is_assumption_decl_name(target_declaration.name):
                        continue
                    target_hidden = explicit_boundary_premises(
                        [
                            premise
                            for premise in hidden_premise_binders(
                                target_declaration.source, assumption_names
                            )
                            if normalize_premise_text(premise)
                            not in visible_statement_premises
                        ]
                    )
                    if target_hidden:
                        add_hidden_premise_finding(
                            target_declaration,
                            target_hidden,
                            f"review row `{name}` resolves to",
                            row_name=name,
                        )
            if not is_signature_only_review_alias(kind, source):
                continue
            candidates = source_equation_wrapper_candidates(name, set(declaration_blocks))
            if candidates:
                findings.append(
                    Finding(
                        "ERROR",
                        review_source_path,
                        f"`{paper_id}` review row `{name}` at line {line_no} is an opaque signature/alias; "
                        f"use source-equation wrapper `{candidates[0]}` in `status.json` `review_surface.include_names`",
                    )
                )
        total_rows = review.get("total_rows") if isinstance(review, dict) else None
        review_rows = interface.get("review_rows")
        source_condition_rows = len(assumption_names)
        if (
            isinstance(total_rows, int)
            and isinstance(review_rows, int)
            and review_rows != total_rows
            and review_rows + source_condition_rows != total_rows
        ):
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` review_rows plus source-condition rows should match human_review.total_rows",
                )
            )
        configured_review_surface_names = set(include_names).union(assumption_names)
        if isinstance(total_rows, int) and include_names and len(configured_review_surface_names) != total_rows:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` include_names plus assumption_names length should match "
                    "human_review.total_rows",
                )
            )
        missing_review_names = set(include_names) - set(actual_review_names)
        if missing_review_names:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` status names are not exported by the review surface: "
                    + ", ".join(sorted(missing_review_names)),
                )
            )
        missing_auxiliary_names = auxiliary_names - set(actual_review_names)
        if missing_auxiliary_names:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` auxiliary_names are not exported by the review surface: "
                    + ", ".join(sorted(missing_auxiliary_names)),
                )
            )
        unclassified_review_names = (
            set(actual_review_names) - set(include_names) - assumption_names - auxiliary_names
        )
        if unclassified_review_names:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` review-surface declarations are neither reviewed, "
                    "assumptions, nor explicit auxiliary proof-facing rows: "
                    + ", ".join(sorted(unclassified_review_names)),
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

    if not using_paper_local_fallback:
        missing = known - set(entries)
        extra = set(entries) - known
        if missing:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"missing paper status entries: {', '.join(sorted(missing))}"))
        if extra:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"unknown paper status entries: {', '.join(sorted(extra))}"))

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
    for folder in paper_dirs(include_template=True):
        paths.append(
            paper_relative_file(folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md")
        )
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


def check_generated_human_status_labels() -> list[Finding]:
    findings: list[Finding] = []
    if not HUMAN_STATUS_FILE.exists():
        return findings
    try:
        data = json.loads(HUMAN_STATUS_FILE.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return [Finding("ERROR", HUMAN_STATUS_FILE, f"invalid JSON: {exc.msg}")]
    papers = data.get("papers")
    if not isinstance(papers, list):
        return findings
    for idx, entry in enumerate(papers, start=1):
        if not isinstance(entry, dict):
            continue
        paper_id = str(entry.get("id") or f"row {idx}")
        label = str(entry.get("llm_as_judge_translation") or "")
        if re.search(r"\badditional assumptions?\b", label, re.I):
            findings.append(
                Finding(
                    "ERROR",
                    HUMAN_STATUS_FILE,
                    f"`{paper_id}.llm_as_judge_translation` should describe statement translation/boundary rows, not additional assumptions",
                )
            )
        human_match = re.fullmatch(r"\d+/(\d+)", str(entry.get("human_review") or "").strip())
        llm_match = re.search(r"\b\d+/(\d+)(?: statement rows)? match\b", label)
        if human_match and llm_match:
            human_total = int(human_match.group(1))
            statement_total = int(llm_match.group(1))
            source_total = sum(
                int(match.group(1))
                for match in re.finditer(r"\b(\d+) source-condition rows?\b", label)
            )
            if statement_total + source_total != human_total:
                findings.append(
                    Finding(
                        "ERROR",
                        HUMAN_STATUS_FILE,
                        f"`{paper_id}.llm_as_judge_translation` covers {statement_total + source_total} row(s), "
                        f"but human_review covers {human_total}",
                    )
                )
    return findings


def check_readme_status_tables(
    include_active: bool,
    paper_filter: str | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    suspicious_caveat = re.compile(
        r"\b(open|conditional|caveat|mismatch|bug|not formalized|not covered)\b",
        re.I,
    )
    for folder in paper_dirs():
        if paper_filter and folder.name != paper_filter:
            continue
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        readme = folder / "README.md"
        if not readme.exists():
            continue
        readme_text = readme.read_text(encoding="utf-8")
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
            if "<!-- BEGIN GENERATED PAPER FOLDER README -->" in readme_text:
                fields: dict[str, str] = {}
                for header, rows in iter_markdown_tables(readme):
                    normalized = [h.strip().lower() for h in header]
                    if normalized != ["field", "value"]:
                        continue
                    for row in rows:
                        if len(row) >= 2:
                            fields[row[0].strip()] = row[1].strip()
                required = ["Final status", "Paper reference", "Lines of Code"]
                for field in required:
                    if not fields.get(field):
                        findings.append(Finding("ERROR", readme, f"generated README missing `{field}` field"))
                status = fields.get("Final status", "").lower()
                if status and status not in PAPER_STATUS_VALUES:
                    findings.append(
                        Finding(
                            "ERROR",
                            readme,
                            f"unexpected generated README final status `{fields.get('Final status')}`; see docs/STATUS.md",
                        )
                    )
                loc = fields.get("Lines of Code", "")
                if loc and not re.fullmatch(r"\d{1,3}(?:,\d{3})*|\d+", loc):
                    findings.append(Finding("ERROR", readme, f"generated README has invalid Lines of Code `{loc}`"))
                if status == "paper draft":
                    review_link = (
                        "Agent source audit",
                        r"Agent source audit:\s+\[[^\]]+\]\(docs/AGENT_SOURCE_AUDIT\.md\)",
                    )
                else:
                    review_link = (
                        "Final validation report",
                        r"Final validation report:\s+\[[^\]]+\]\(FINAL_VALIDATION_REPORT\.md\)",
                    )
                required_links = [
                    review_link,
                    (
                        "Dependency DAG",
                        r"Dependency DAG:\s+\[[^\]]+\]\(docs/DependencyDAG\.pdf\)",
                    ),
                    ("status.json", r"\[status\.json\]\(status\.json\)"),
                ]
                for label, pattern in required_links:
                    if not re.search(pattern, readme_text):
                        findings.append(Finding("ERROR", readme, f"generated README missing `{label}` link"))
                continue
            findings.append(Finding("ERROR", readme, "no theorem/status markdown table found"))
    if not paper_filter:
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
        if path.parts[2:] == ("docs", "FINAL_VALIDATION_REPORT.md"):
            findings.append(
                Finding(
                    "ERROR",
                    ROOT / path,
                    "legacy validation-report alias; link to the paper-root `FINAL_VALIDATION_REPORT.md`",
                )
            )
        if path.parts[2:] == ("DependencyDAG.pdf",):
            findings.append(
                Finding(
                    "ERROR",
                    ROOT / path,
                    "legacy root-level DAG alias; link to `docs/DependencyDAG.pdf`",
                )
            )
        if (
            path.suffix == ".pdf"
            and path.name not in ALLOWED_TRACKED_PAPER_PDFS
            and not is_declared_tracked_pdf_artifact(path)
        ):
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
                "top-level README should link to the project website and docs status pages instead of embedding a paper-status table",
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


def known_paper_source_terms() -> set[str]:
    """Return paper IDs and citation prefixes discovered from paper folders."""

    terms: set[str] = set()
    if not PAPERS.exists():
        return terms
    for folder in PAPERS.iterdir():
        if not folder.is_dir() or folder.name == "TEMPLATE":
            continue
        if not PAPER_FOLDER_NAME_RE.fullmatch(folder.name):
            continue
        terms.add(folder.name)
        match = re.match(r"^([A-Z][A-Za-z]*)(\d{2})", folder.name)
        if not match:
            continue
        author_prefix = match.group(1)
        year_prefix = f"{author_prefix}{match.group(2)}"
        if len(author_prefix) >= 3:
            terms.add(author_prefix)
        terms.add(year_prefix)
    return terms - GENERIC_SOURCE_HYGIENE_ALLOWED_TERMS


def generic_source_hygiene_paths(*, library_only: bool) -> list[Path]:
    """Return reusable files that should not contain concrete paper references."""

    roots: list[Path] = [ROOT / "EconCSLib"]
    if not library_only:
        roots.extend(
            [
                ROOT / "scripts",
                ROOT / "docs" / "AGENT_FORMALIZATION_WORKFLOW.md",
                ROOT / "docs" / "LIBRARY_PROVENANCE.md",
                ROOT / "docs" / "THEOREM_ERGONOMICS.md",
                ROOT / "docs" / "REVIEW_DASHBOARD.md",
                ROOT / "docs" / "NEW_CONTRIBUTOR_WORKFLOW.md",
                ROOT / "skills" / "econcs-formalizer" / "SKILL.md",
            ]
        )

    paths: set[Path] = set()
    for root in roots:
        if root.is_dir():
            for path in root.rglob("*"):
                if path.suffix in {".lean", ".py", ".md"} and path.is_file():
                    paths.add(path)
        elif root.is_file() and root.suffix in {".lean", ".py", ".md"}:
            paths.add(root)
    return sorted(paths)


def check_generic_source_reference_hygiene(*, library_only: bool = False) -> list[Finding]:
    """Reject concrete paper IDs/theorem-number labels in reusable code.

    The check is data-driven: paper IDs and citation prefixes are discovered from
    `papers/` folder names, while allowed domain/algorithm terms live in
    `papers/audit_config.json`.
    """

    findings: list[Finding] = []
    terms = known_paper_source_terms()
    term_re = None
    if terms:
        term_re = re.compile(
            r"\b(?:"
            + "|".join(re.escape(term) for term in sorted(terms, key=len, reverse=True))
            + r")\b"
        )

    for path in generic_source_hygiene_paths(library_only=library_only):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        for line_no, line in enumerate(lines, start=1):
            if term_re is not None and (match := term_re.search(line)):
                findings.append(
                    Finding(
                        "ERROR",
                        path,
                        f"generic code/doc line {line_no} mentions paper-specific term "
                        f"`{match.group(0)}`; move citation/display metadata to paper-local "
                        "files or data config, or use a paper-neutral domain name",
                    )
                )
            if path.suffix == ".lean" and "EconCSLib" in path.parts:
                if match := GENERIC_SOURCE_THEOREM_LABEL_RE.search(line):
                    findings.append(
                        Finding(
                            "ERROR",
                            path,
                            f"generic Lean comment/source line {line_no} mentions paper "
                            f"numbered label `{match.group(0)}`; theorem numbering belongs "
                            "in paper-local interfaces and validation reports",
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
    findings.extend(check_library_source_assumption_standards())
    findings.extend(check_library_reusable_provenance_language())
    findings.extend(check_library_standard_definition_audits())
    findings.extend(check_library_source_hygiene())
    findings.extend(check_generic_source_reference_hygiene(library_only=True))
    if strict_style:
        findings.extend(check_strict_lean_style())
    if library_premise_audit:
        findings.extend(check_library_certificate_boundaries())
    return findings


def check_root_readme_policy() -> list[Finding]:
    return [
        Finding("ERROR", ROOT / "README.md", message)
        for message in validate_root_readme()
    ]


def run(
    include_active: bool,
    strict_style: bool,
    library_premise_audit: bool = False,
    paper_filter: str | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    findings.extend(check_sorries(include_active))
    findings.extend(check_axiom_like_declarations(include_active))
    findings.extend(check_hidden_variable_premises(include_active))
    findings.extend(check_guarded_checks(include_active))
    findings.extend(check_library_source_assumption_standards())
    findings.extend(check_library_reusable_provenance_language())
    findings.extend(check_library_standard_definition_audits())
    findings.extend(check_library_source_hygiene())
    findings.extend(check_generic_source_reference_hygiene())
    findings.extend(check_paper_contract(include_active))
    findings.extend(check_final_report_status_alignment(include_active, paper_filter=paper_filter))
    findings.extend(
        check_final_report_human_facing_front_matter(
            include_active,
            paper_filter=paper_filter,
        )
    )
    findings.extend(
        check_dag_and_validation_report_closeout(
            include_active=include_active,
            paper_filter=paper_filter,
        )
    )
    findings.extend(check_review_launcher_readiness(include_active))
    findings.extend(check_dag_status_styles())
    findings.extend(check_paper_facing_ledgers(include_active))
    findings.extend(check_post_paper_audit_interfaces(include_active))
    findings.extend(
        check_machine_paper_status(
            library_premise_audit=library_premise_audit,
            paper_filter=paper_filter,
        )
    )
    findings.extend(check_status_label_vocabulary())
    findings.extend(check_generated_human_status_labels())
    findings.extend(check_readme_status_tables(include_active, paper_filter=paper_filter))
    findings.extend(check_tracked_artifacts(include_active))
    findings.extend(check_stale_architecture_terms())
    findings.extend(check_root_readme_policy())
    findings.extend(check_human_facing_readme())
    if strict_style:
        findings.extend(check_strict_lean_style())
    if library_premise_audit:
        findings.extend(check_library_certificate_boundaries())
    return findings


def finding_paper_id(finding: Finding) -> str:
    """Return the paper folder associated with a finding when one is visible."""

    path = finding.path
    parts = path.parts
    if "papers" in parts:
        index = parts.index("papers")
        if index + 1 < len(parts):
            paper = parts[index + 1]
            return paper.removesuffix(".lean") if paper.endswith(".lean") else paper
    match = re.match(r"`([^`]+)`", finding.message)
    if match:
        return match.group(1)
    return "REPO"


def finding_is_for_paper_closeout(finding: Finding, paper_id: str) -> bool:
    """Return whether a finding belongs to one paper's closeout surface."""

    path = finding.path
    rel = path.relative_to(ROOT) if path.is_absolute() else path
    parts = rel.parts
    if len(parts) >= 2 and parts[0] == "papers":
        if parts[1] == paper_id or parts[1] == f"{paper_id}.lean":
            if PUBLIC_RELEASE and "no cached source PDF found" in finding.message:
                return False
            return True
        return False
    return paper_id in finding.message


def paper_status_label(paper_id: str) -> str:
    status_path = PAPERS / paper_id / "status.json"
    if not status_path.exists():
        return "not recorded"
    try:
        payload = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "unreadable status.json"
    status = payload.get("status")
    if isinstance(status, str) and status.strip():
        return status
    return "missing status"


def deep_audit_category(message: str) -> str:
    if "Lean axiom audit" in message or "depends on unapproved Lean axiom" in message:
        return "Lean axiom closure"
    if (
        "broad aggregate name" in message
        or "opaque alias/signature" in message
        or "formula-bearing review row" in message
    ):
        return "broad-or-opaque paper-facing row"
    if (
        "premises not routed through explicit Assumptions.lean" in message
        or "source-row formula boundary" in message
    ):
        return "hidden premise / certificate boundary"
    if "DAG" in message or "final validation report" in message or "post-formalization audit" in message:
        return "DAG/report closeout audit"
    return "other repository audit finding"


def write_markdown_report(
    report_path: Path,
    findings: list[Finding],
    include_active: bool,
    strict_style: bool,
    library_premise_audit: bool,
    library_only: bool,
    paper_filter: str | None = None,
) -> None:
    """Write a durable paper-by-paper audit report.

    This is intentionally generated from the same finding objects printed by the
    CLI so the human report cannot drift from the blocking audit.
    """

    actionable = [finding for finding in findings if finding.severity in {"ERROR", "WARN"}]
    errors = [finding for finding in findings if finding.severity == "ERROR"]
    warnings = [finding for finding in findings if finding.severity == "WARN"]
    infos = [finding for finding in findings if finding.severity == "INFO"]

    by_paper: dict[str, list[Finding]] = {}
    for finding in actionable:
        by_paper.setdefault(finding_paper_id(finding), []).append(finding)

    command_bits = ["python3 scripts/audit_repository.py"]
    if include_active:
        command_bits.append("--include-active")
    if strict_style:
        command_bits.append("--strict-style")
    if library_premise_audit:
        command_bits.append("--library-premise-audit")
    if library_only:
        command_bits.append("--library-only")
    if paper_filter:
        command_bits.extend(["--paper", paper_filter])
    command_bits.append("--info-limit 0")
    command_bits.append(f"--write-report {report_path.as_posix()}")

    lines: list[str] = [
        "# Recursive Provenance Audit Findings",
        "",
        f"- Generated: {date.today().isoformat()}",
        f"- Command: `{' '.join(command_bits)}`",
        f"- Scope: {'library only' if library_only else 'papers and reusable library'}",
        f"- Paper filter: `{paper_filter}`" if paper_filter else "- Paper filter: none",
        f"- Active paper folders: {'included' if include_active else 'skipped'}",
        f"- Strict style: {'included' if strict_style else 'not included'}",
        f"- Library premise audit: {'included' if library_premise_audit else 'not included'}",
        f"- Totals: {len(errors)} error(s), {len(warnings)} warning(s), {len(infos)} info finding(s)",
        "",
        "## How To Use This Report",
        "",
        "Resolve findings paper-by-paper. For a paper claimed as `formalized`,",
        "`#print axioms` on the paper-facing rows should report only approved",
        "standard Lean foundations, no paper-facing row should remain broad or",
        "opaque, and every visible certificate/source-row/external premise should",
        "be either derived or routed through a source-validated `Assumptions.lean`",
        "declaration. Paper-specific formulas should not be hidden inside reusable",
        "library definitions. A paper may remain `partially formalized` only if the",
        "same boundary is explicit in `status.json`, the dependency DAG, and the",
        "final validation report.",
        "",
    ]

    if not actionable:
        lines.extend(["## Findings By Paper", "", "No actionable findings."])
    else:
        lines.extend(["## Findings By Paper", ""])
        for paper_id in sorted(by_paper):
            paper_findings = by_paper[paper_id]
            counts = {
                severity: sum(1 for finding in paper_findings if finding.severity == severity)
                for severity in ("ERROR", "WARN")
            }
            lines.extend(
                [
                    f"### {paper_id}",
                    "",
                    f"- Current status: `{paper_status_label(paper_id)}`",
                    f"- Findings: {counts['ERROR']} error(s), {counts['WARN']} warning(s)",
                    "",
                ]
            )
            for finding in paper_findings:
                rel = finding.path.relative_to(ROOT) if finding.path.is_absolute() else finding.path
                category = deep_audit_category(finding.message)
                lines.append(
                    f"- `[{finding.severity}]` `{rel}` ({category}): {finding.message}"
                )
            lines.append("")

    report_path = report_path if report_path.is_absolute() else ROOT / report_path
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--include-active",
        action="store_true",
        help="also audit folders listed as active in papers/audit_config.json",
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
        "--paper",
        help=(
            "restrict machine-readable paper status checks to one paper folder; "
            "other generic repository checks still run unless --library-only is used"
        ),
    )
    parser.add_argument(
        "--paper-closeout",
        action="store_true",
        help=(
            "with --paper, print and fail only on findings belonging to that paper's "
            "post-formalization closeout surface"
        ),
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
    parser.add_argument(
        "--write-report",
        type=Path,
        help="write a Markdown report grouping actionable findings by paper",
    )
    args = parser.parse_args()
    if args.paper_closeout and not args.paper:
        parser.error("--paper-closeout requires --paper <paper-folder>")

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
            paper_filter=args.paper,
        )
    if args.paper_closeout:
        findings = [
            finding
            for finding in findings
            if finding_is_for_paper_closeout(finding, args.paper)
        ]
    if args.write_report:
        write_markdown_report(
            args.write_report,
            findings,
            include_active=args.include_active,
            strict_style=args.strict_style,
            library_premise_audit=args.library_premise_audit,
            library_only=args.library_only,
            paper_filter=args.paper,
        )
        print(f"Wrote Markdown audit report to {args.write_report}")
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
        + (f"; paper filter {args.paper}" if args.paper else "")
        + ("; paper-closeout scope" if args.paper_closeout else "")
        + (f"; {len(infos)} info finding(s)" if infos else "")
    )
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
