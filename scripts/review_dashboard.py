#!/usr/bin/env python3
"""Generate and persist theorem-review metadata from paper interfaces.

This helper creates a local review page for one paper or all papers.  The page
shows side-by-side the paper-facing claim text (when available) and the Lean
statement from the paper's curated review surface, and lets a reviewer record a
checkbox + note pair per theorem.  Each submission is appended to a local JSONL
trace with the reviewer handle and UTC timestamp.
"""

from __future__ import annotations

import argparse
import mimetypes
import hashlib
import csv
import html
import io
import getpass
import os
import json
import re
import sys
import subprocess
import urllib.parse
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from xml.etree import ElementTree
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"
DEFAULT_PAPER_LOG_FILE = "paper_theorem_validations.jsonl"
DEFAULT_PAPER_INTERFACE_CACHE_FILE = "paper_interface_cache.json"
DEFAULT_REVIEW_SLICES_FILE = "review_slices.json"
DEFAULT_LLM_LEAN_TO_TEX_FILE = "lean_to_tex_llm.json"
PAPER_INTERFACE_CACHE_SCHEMA = 6
REVIEW_SLICES_SCHEMA = 1
REVIEW_SOURCE_FILENAME = "PaperInterface.lean"
REVIEW_DECL_KINDS = {"theorem", "lemma", "def", "abbrev"}


DECL_RE = re.compile(
    r"^(?P<indent>\s*)(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev)\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
COMMENT_START_RE = re.compile(r"^\s*/-[!]?")
NAMESPACE_OPEN_RE = re.compile(
    r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$"
)
SECTION_OPEN_RE = re.compile(r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$")
END_SCOPE_RE = re.compile(r"^\s*end\b(?:\s+([A-Za-z_][A-Za-z0-9_']*)\s*)?$")
REPORT_CLAUSE_RE = re.compile(
    r"^\s*-\s*`(?:[A-Za-z0-9_]+\.)?(?P<name>[A-Za-z_][A-Za-z0-9_']+)`\s*:\s*(?P<text>.*)"
)
THEOREM_ENV_OPEN_RE = re.compile(r"^\s*\\begin\{(theorem|lemma|proposition|corollary|claim|definition)\}")
THEOREM_ENV_CLOSE_RE = re.compile(r"^\s*\\end\{(theorem|lemma|proposition|corollary|claim|definition)\}")
THEOREM_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
PAPER_TEXT_STATEMENT_LABEL_RE = re.compile(
    r"^\s*\f?\s*(?P<kind>Definition|Theorem|Lemma|Proposition|Corollary|Claim)\s+"
    r"(?P<number>[A-Za-z]?\d+(?:\.\d+)?)(?:\s*\((?P<title>[^)]*)\))?\."
)
PAPER_TEXT_STATEMENT_STOP_RE = re.compile(
    r"^\s*(?:Proof\.|Proof\s|The proof\b|To prove\b|The result follows\b|"
    r"The theorem establishes\b|The result establishes\b|Each de|"
    r"Of course\b|Note that\b|Discussion\b|What does\b|Then, we have the following\b)"
)
PAPER_TEX_PRIORITY: list[str] = [
    "{name}.tex",
    "paper.tex",
    "source.tex",
]
AGENT_PREVIEW_TOKEN_RE = re.compile(
    r"^[ \t]*(?:theorem|lemma|def|abbrev)\s+[A-Za-z_][A-Za-z0-9_']*\s*",
    re.MULTILINE,
)
LEAN_TO_TEX_TOKENS: list[tuple[str, str]] = [
    ("→", r"\to"),
    ("↔", r"\iff"),
    ("⇒", r"\Rightarrow"),
    ("⇐", r"\Leftarrow"),
    ("∧", r"\land"),
    ("∨", r"\lor"),
    ("¬", r"\lnot"),
    ("∑", r"\sum"),
    ("∏", r"\prod"),
    ("∫", r"\int"),
    ("∃", r"\exists"),
    ("∀", r"\forall"),
    ("≤", r"\le"),
    ("≥", r"\ge"),
    ("≠", r"\ne"),
    ("≃", r"\simeq"),
    ("≈", r"\approx"),
    ("α", r"\alpha"),
    ("β", r"\beta"),
    ("γ", r"\gamma"),
    ("δ", r"\delta"),
    ("ε", r"\epsilon"),
    ("ι", r"\iota"),
    ("κ", r"\kappa"),
    ("λ", r"\lambda"),
    ("μ", r"\mu"),
    ("ν", r"\nu"),
    ("π", r"\pi"),
    ("σ", r"\sigma"),
    ("τ", r"\tau"),
    ("φ", r"\phi"),
    ("χ", r"\chi"),
    ("ψ", r"\psi"),
    ("ω", r"\omega"),
    ("Γ", r"\Gamma"),
    ("Δ", r"\Delta"),
    ("Π", r"\Pi"),
    ("Σ", r"\Sigma"),
    ("Λ", r"\Lambda"),
    ("Φ", r"\Phi"),
    ("Ψ", r"\Psi"),
    ("Ω", r"\Omega"),
    ("∈", r"\in"),
    ("⊆", r"\subseteq"),
    ("∅", r"\varnothing"),
    ("↦", r"\mapsto"),
]
AGENT_PREVIEW_MAX_LEN = 1800
AGENT_PREVIEW_CHECK_TIMEOUT = 20
PAPER_ASSET_EXTENSIONS = {".pdf", ".txt"}
PAPER_RENDERED_IMAGE_EXTENSIONS = {".png"}
PAPER_RENDERED_STATEMENT_DIR = "paper_statement_images"
PAPER_PDF_PRIORITY: list[str] = [
    "{name}.pdf",
    "source.pdf",
    "paper.pdf",
    "arxiv.pdf",
]
PAPER_TXT_PRIORITY: list[str] = [
    "source.txt",
    "paper.txt",
]
DEFAULT_USER_ENV_VARS = [
    "GITHUB_ACTOR",
    "GITHUB_USER",
    "GITHUB_USERNAME",
    "GITHUB_REPOSITORY_OWNER",
    "USER",
    "USERNAME",
]
AGENT_PREVIEW_CACHE: dict[str, dict[str, str]] = {}


def _normalize_name_key(name: str) -> str:
    """Normalize a declaration-like name into a tolerant lookup key."""

    return re.sub(r"[^A-Za-z0-9_]+", "_", name.strip()).strip("_")


def _add_statement_variant(mapping: dict[str, str], key: str, value: str) -> None:
    mapping[key] = value
    normalized = _normalize_name_key(key)
    if normalized and normalized != key:
        mapping[normalized] = value
    lowered = key.lower()
    if lowered and lowered != key:
        mapping[lowered] = value
    lowered_normalized = normalized.lower()
    if lowered_normalized and lowered_normalized not in {lowered, normalized, key}:
        mapping[lowered_normalized] = value


def _paper_statement_key(kind: str, number: str) -> str:
    """Return a declaration-name-friendly key for a paper statement number."""

    normalized_number = number.strip().replace(".", "_").lower()
    return f"{kind.strip().lower()}{normalized_number}"


def _read_git_config_value(key: str) -> str:
    """Read a git configuration value for this repo, returning empty on failure."""

    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "config", "--get", key],
            check=False,
            capture_output=True,
            text=True,
            timeout=2,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    value = (proc.stdout or "").strip()
    if not value and proc.returncode != 0:
        return ""
    return value


def _read_gh_cli_user() -> str:
    """Read cached GitHub username from gh CLI config if available."""

    host_file = Path.home() / ".config" / "gh" / "hosts.yml"
    if not host_file.exists() or not host_file.is_file():
        return ""
    try:
        lines = host_file.read_text(encoding="utf-8").splitlines()
    except OSError:
        return ""

    in_github_host = False
    for raw_line in lines:
        line = raw_line.rstrip()
        header = re.match(r"^([A-Za-z0-9._-]+):\s*$", line)
        if header and not raw_line.startswith(" "):
            in_github_host = header.group(1).strip() == "github.com"
            continue
        if not in_github_host:
            continue
        match = re.match(r"^\s*user:\s*\"?\'?([^\"\'\\n]+)\"?\'?\s*$", line)
        if match:
            return match.group(1).strip()
    return ""


def detect_reviewer_username(explicit_user: str | None, env_vars: list[str]) -> str:
    """Choose the best available reviewer username with sensible fallbacks."""

    user = (explicit_user or "").strip()
    if user:
        return user

    for env_var in env_vars:
        env_user = os.environ.get(env_var)
        if env_user and env_user.strip():
            return env_user.strip()

    cached = _read_gh_cli_user()
    if cached:
        return cached

    for key in ("github.user", "user.name", "user.username"):
        git_user = _read_git_config_value(key)
        if git_user:
            return git_user.strip()

    return getpass.getuser()


@dataclass
class ReviewItem:
    name: str
    kind: str
    lean_statement: str
    paper_statement: str
    agent_statement: str
    paper_statement_image_url: str = ""
    line_number: int = 0
    slice_id: str = "all"
    slice_title: str = "All statements"


def find_review_source_file(folder: Path) -> Path | None:
    """Return the paper's curated human-review Lean surface, if present."""

    candidate = folder / REVIEW_SOURCE_FILENAME
    if candidate.exists() and candidate.is_file():
        return candidate
    return None


def review_source_file(folder: Path) -> Path:
    """Return the paper's review source or raise a readable error."""

    source = find_review_source_file(folder)
    if source is None:
        raise FileNotFoundError(
            f"no canonical human review Lean surface ({REVIEW_SOURCE_FILENAME}) "
            f"for paper: {folder.name}"
        )
    return source


def review_source_module(folder: Path, source_file: Path) -> str:
    """Return the Lean import module for a paper-local review source."""

    return f"{folder.name}.{source_file.stem}"


def find_paper_pdf(folder: Path) -> Path | None:
    """Find the most likely paper pdf in a folder."""

    for rel in PAPER_PDF_PRIORITY:
        candidate = folder / rel.format(name=folder.name)
        if candidate.exists() and candidate.is_file():
            return candidate

    for candidate in sorted(
        p
        for p in folder.glob("*.pdf")
        if p.is_file() and p.name.lower() not in {"dependencydag.pdf", "dependency_dag.pdf"}
    ):
        return candidate
    return None


def find_paper_text(folder: Path) -> Path | None:
    """Find a compact text fallback for paper-source viewing."""

    for rel in PAPER_TXT_PRIORITY:
        candidate = folder / rel
        if candidate.exists() and candidate.is_file():
            return candidate

    for candidate in sorted(
        p
        for p in folder.glob("*.txt")
        if p.is_file() and p.name.lower() != "readme.txt"
    ):
        return candidate
    return None


def paper_asset_url(paper: str, path: Path) -> str:
    """Build a safe route path for a paper-local asset."""

    return f"/paper-assets/{urllib.parse.quote(paper)}/{urllib.parse.quote(path.name)}"


def paper_rendered_statement_url(paper: str, path: Path) -> str:
    """Build a safe route path for a generated statement image."""

    return f"/rendered-statements/{urllib.parse.quote(paper)}/{urllib.parse.quote(path.name)}"


def _file_sha256(path: Path | None) -> str:
    """Return a stable binary digest for a source file."""

    if path is None or not path.exists() or not path.is_file():
        return ""
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError:
        return ""
    return digest.hexdigest()


def parse_block_comment(lines: list[str], start: int) -> tuple[str, int]:
    """Collect a block comment from `start`; return text and first line after it."""

    collected = [lines[start]]
    j = start
    if "-/" in lines[start]:
        return "\n".join(collected), start + 1
    while j + 1 < len(lines):
        j += 1
        collected.append(lines[j])
        if "-/" in lines[j]:
            return "\n".join(collected), j + 1
    return "\n".join(collected), len(lines)


def clean_comment(raw: str) -> str:
    """Strip Lean block comment markers and clean a docstring for display."""

    text = raw.strip()
    if text.startswith("/-!"):
        text = text[3:]
    elif text.startswith("/-"):
        text = text[2:]
    if text.endswith("-/"):
        text = text[:-2]
    text = text.strip()
    lines = [line.lstrip(" *") for line in text.splitlines()]
    return "\n".join(line.strip() for line in lines).strip()


def normalize_statement(text: str) -> str:
    """Normalize statement text for drift comparisons."""

    return re.sub(r"\s+", " ", text.strip())


def statement_digest(text: str) -> str:
    """Generate a stable digest for a statement snapshot."""

    return hashlib.sha256(normalize_statement(text).encode("utf-8")).hexdigest()


def strip_qualified_identifiers(value: str) -> str:
    """Drop long qualified Lean identifiers (`A.B.C`) while preserving base names."""

    return re.sub(
        r"\b([A-Za-z_][A-Za-z0-9_']*\.)+([A-Za-z_][A-Za-z0-9_']*)",
        r"\2",
        value,
    )


def _apply_latex_token_mapping(raw: str) -> str:
    """Apply a compact symbol-to-LaTeX mapping."""

    value = raw.strip().replace("\n", " ")
    value = re.sub(r"\s+", " ", value).strip()
    if not value:
        return ""
    for old, new in LEAN_TO_TEX_TOKENS:
        value = value.replace(old, new)
    for symbol in ("->", "=>", "<->", "<=>"):
        if symbol in value:
            value = value.replace(symbol, " " + symbol + " ")
    return value[:AGENT_PREVIEW_MAX_LEN]


def lean_to_latex_statement(raw: str) -> str:
    """Generate a compact, heuristic TeX-like draft from a Lean declaration signature."""

    if not raw:
        return ""
    value = raw.strip().replace("\n", " ")
    value = re.sub(r"\s+", " ", value).strip()
    if not value:
        return ""
    if ":=" in value:
        value = value.split(":=", 1)[0].rstrip()
    value = AGENT_PREVIEW_TOKEN_RE.sub("", value, count=1)
    value = value.strip().strip(",")
    return _apply_latex_token_mapping(value)


def lean_check_to_latex_statement(raw: str) -> str:
    """Map Lean #check output type text to compact TeX-like form."""

    if not raw:
        return ""
    value = strip_qualified_identifiers(raw)
    return _apply_latex_token_mapping(value)


def _parse_lean_check_previews(output: str, theorem_names: list[str]) -> dict[str, str]:
    """Parse Lean `#check` output into declaration-name to type-text map."""

    names_sorted = sorted(theorem_names, key=len, reverse=True)
    captured: dict[str, list[str]] = {}
    active: str | None = None
    for raw_line in output.splitlines():
        if active is not None and (raw_line.startswith(" ") or raw_line.startswith("\t")):
            captured[active].append(raw_line.strip())
            continue
        active = None
        line = raw_line.rstrip()
        for name in names_sorted:
            pattern = rf"^@?{re.escape(name)}\s*:\s*(.*)$"
            match = re.match(pattern, line)
            if not match:
                continue
            body = match.group(1).strip()
            captured[name] = []
            if body:
                captured[name].append(body)
            active = name
            break

    result: dict[str, str] = {}
    for name, parts in captured.items():
        text = " ".join(parts).strip()
        if text:
            result[name] = text
    return result


def run_lean_check_previews(
    paper_folder: Path,
    theorem_names: list[str],
    timeout_seconds: int = AGENT_PREVIEW_CHECK_TIMEOUT,
    source_file: Path | None = None,
) -> dict[str, str]:
    """Ask Lean for #check output on Lean declarations, with fallback on failure."""

    if not theorem_names:
        return {}
    canonical_names = sorted(set(theorem_names))
    module_file = source_file or find_review_source_file(paper_folder)
    if module_file is None or not module_file.exists():
        return {}
    cache_key = f"{paper_folder.resolve()}::{module_file.name}::{'|'.join(canonical_names)}"
    if cache_key in AGENT_PREVIEW_CACHE:
        return AGENT_PREVIEW_CACHE[cache_key]

    import_module = review_source_module(paper_folder, module_file)
    lines = [
        f"import {import_module}",
        "set_option pp.universes false",
        "",
    ]
    for name in canonical_names:
        lines.append(f"#check (@{name})")
    script = "\n".join(lines) + "\n"

    with tempfile.TemporaryDirectory() as tmpdir:
        script_path = Path(tmpdir) / "review_agent_preview.lean"
        script_path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(script_path)],
                cwd=str(ROOT),
                check=False,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
            )
        except (OSError, subprocess.TimeoutExpired):
            AGENT_PREVIEW_CACHE[cache_key] = {}
            return {}

    if proc.returncode != 0 and not proc.stdout.strip():
        AGENT_PREVIEW_CACHE[cache_key] = {}
        return {}

    checked = _parse_lean_check_previews(proc.stdout, canonical_names)
    AGENT_PREVIEW_CACHE[cache_key] = checked
    return checked


def agent_preview_comment(
    comment: str | None, raw_statement: str, check_statement: str | None = None
) -> str:
    """Prefer Lean #check output, then signature heuristic, then doc-comment fallback."""

    if check_statement:
        translated = lean_check_to_latex_statement(check_statement)
        if translated:
            return translated
    translated = lean_to_latex_statement(raw_statement)
    if translated:
        return translated
    if comment:
        text = re.sub(r"\s+", " ", comment).strip()
        return text[:AGENT_PREVIEW_MAX_LEN]
    return "(no auto-generated preview available)"



def parse_report_texts(report_path: Path) -> dict[str, str]:
    """Extract theorem-level paper statement summaries from final report bullets."""

    statements: dict[str, str] = {}
    lines = report_path.read_text(encoding="utf-8").splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        match = REPORT_CLAUSE_RE.match(line)
        if not match:
            i += 1
            continue

        name = match.group("name")
        text = match.group("text").strip()
        i += 1
        extras: list[str] = []
        while i < len(lines):
            nxt = lines[i]
            if not nxt.strip():
                i += 1
                continue
            if nxt.lstrip().startswith("- "):
                break
            if re.match(r"^\s{2,}\S", nxt):
                extras.append(nxt.strip())
                i += 1
                continue
            break
        if extras:
            text = " ".join([text] + extras).strip()
        if text:
            _add_statement_variant(statements, name, text)
        else:
            _add_statement_variant(statements, name, "(No extracted paper statement text found.)")
    return statements


def find_paper_tex_source(folder: Path) -> Path | None:
    """Find the likely paper TeX source used for display text extraction."""

    for rel in PAPER_TEX_PRIORITY:
        candidate = folder / rel.format(name=folder.name)
        if candidate.exists() and candidate.is_file():
            return candidate

    for candidate in sorted(
        p
        for p in folder.glob("*.tex")
        if p.is_file()
    ):
        if candidate.name.lower() in {"dependencydag.tex", "dependency_dag.tex", "paperinterface.tex"}:
            continue
        return candidate
    return None


def parse_paper_tex_statements(folder: Path) -> dict[str, str]:
    """Extract labeled theorem-like statements from a LaTeX source file."""

    source = find_paper_tex_source(folder)
    if source is None:
        return {}

    try:
        lines = source.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {}

    statements: dict[str, str] = {}
    in_env = False
    active_label: str | None = None
    active_kind: str | None = None
    active_lines: list[str] = []

    for raw_line in lines:
        line = raw_line.strip()

        if not in_env:
            open_match = THEOREM_ENV_OPEN_RE.match(line)
            if open_match:
                in_env = True
                active_kind = open_match.group(1)
                active_label = None
                active_lines = [raw_line]
                continue
            else:
                continue

        if in_env and active_kind is not None:
            active_lines.append(raw_line)
            label_match = THEOREM_LABEL_RE.search(raw_line)
            if label_match and not active_label:
                active_label = label_match.group(1).strip()

            close_match = THEOREM_ENV_CLOSE_RE.match(line)
            if close_match:
                if close_match.group(1) == active_kind:
                    if active_label:
                        text = " ".join(active_lines)
                        text = re.sub(r"%.*$", "", text)
                        text = THEOREM_ENV_OPEN_RE.sub("", text)
                        text = THEOREM_ENV_CLOSE_RE.sub("", text)
                        text = THEOREM_LABEL_RE.sub("", text)
                        text = re.sub(r"\s+", " ", text).strip()
                        if text:
                            _add_statement_variant(statements, active_label, text)
                in_env = False
                active_label = None
                active_kind = None
                active_lines = []

    return statements


def _clean_paper_text_statement(lines: list[str]) -> str:
    """Clean a statement block extracted from a PDF text dump."""

    cleaned: list[str] = []
    blank_pending = False
    for raw_line in lines:
        line = raw_line.replace("\f", "").rstrip()
        if not line.strip():
            blank_pending = bool(cleaned)
            continue
        if line.strip().isdigit():
            continue
        if blank_pending and cleaned:
            cleaned.append("")
        cleaned.append(line)
        blank_pending = False
    return "\n".join(cleaned).strip()


def parse_paper_text_statements(folder: Path) -> dict[str, str]:
    """Extract numbered paper statements from `source.txt` when no TeX is present."""

    source = find_paper_text(folder)
    if source is None:
        return {}

    try:
        lines = source.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {}

    statements: dict[str, str] = {}
    active_key: str | None = None
    active_kind: str | None = None
    active_number: str | None = None
    active_lines: list[str] = []

    def flush() -> None:
        nonlocal active_key, active_kind, active_number, active_lines
        if active_key:
            text = _clean_paper_text_statement(active_lines)
            if text:
                _add_statement_variant(statements, active_key, text)
                if active_kind and active_number:
                    _add_statement_variant(
                        statements,
                        f"{active_kind.lower()}_{active_number.replace('.', '_').lower()}",
                        text,
                    )
        active_key = None
        active_kind = None
        active_number = None
        active_lines = []

    for raw_line in lines:
        stripped = raw_line.strip()
        label_match = PAPER_TEXT_STATEMENT_LABEL_RE.match(stripped)
        if label_match:
            flush()
            active_kind = label_match.group("kind")
            active_number = label_match.group("number")
            active_key = _paper_statement_key(active_kind, active_number)
            active_lines = [raw_line]
            continue

        if active_key is not None and PAPER_TEXT_STATEMENT_STOP_RE.match(stripped):
            flush()
            continue

        if active_key is not None:
            active_lines.append(raw_line)

    flush()
    return statements


def parse_paper_text_statement_locations(folder: Path) -> list[dict[str, Any]]:
    """Extract first source-text locations for numbered paper statements."""

    source = find_paper_text(folder)
    if source is None:
        return []
    try:
        lines = source.read_text(encoding="utf-8").split("\n")
    except OSError:
        return []

    page = 1
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    for line_number, raw_line in enumerate(lines, start=1):
        line = raw_line
        if "\f" in line:
            page += line.count("\f")
            line = line.rsplit("\f", 1)[-1]
        stripped = line.strip()
        label_match = PAPER_TEXT_STATEMENT_LABEL_RE.match(stripped)
        if not label_match:
            continue
        kind = label_match.group("kind")
        number = label_match.group("number")
        key = _paper_statement_key(kind, number)
        if key in seen:
            continue
        seen.add(key)
        out.append(
            {
                "key": key,
                "kind": kind,
                "number": number,
                "page": page,
                "line_number": line_number,
            }
        )
    return out


def load_llm_lean_to_tex_drafts(folder: Path) -> dict[str, str]:
    """Load optional context-free LLM TeX drafts for expanded Lean statements."""

    path = folder / ".review_traces" / DEFAULT_LLM_LEAN_TO_TEX_FILE
    if not path.exists() or not path.is_file():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, str] = {}
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        value = str(raw_value).strip()
        if name and value:
            out[name] = value
    return out


def _run_pdftotext_bbox(pdf_path: Path, page: int) -> str:
    """Return pdftotext bbox-layout XML for one page, or empty on failure."""

    try:
        proc = subprocess.run(
            [
                "pdftotext",
                "-bbox-layout",
                "-f",
                str(page),
                "-l",
                str(page),
                str(pdf_path),
                "-",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    if proc.returncode != 0:
        return ""
    return proc.stdout


def _parse_pdf_bbox_words(xml_text: str) -> tuple[float, float, list[dict[str, Any]]]:
    """Parse pdftotext bbox XML into page dimensions and word boxes."""

    if not xml_text.strip():
        return 0.0, 0.0, []
    try:
        root = ElementTree.fromstring(xml_text)
    except ElementTree.ParseError:
        return _parse_pdf_bbox_words_with_regex(xml_text)
    page_node = next((node for node in root.iter() if node.tag.endswith("page")), None)
    if page_node is None:
        return 0.0, 0.0, []
    try:
        page_width = float(page_node.attrib.get("width", "0"))
        page_height = float(page_node.attrib.get("height", "0"))
    except ValueError:
        page_width = 0.0
        page_height = 0.0
    words: list[dict[str, Any]] = []
    for word_node in root.iter():
        if not word_node.tag.endswith("word"):
            continue
        text = "".join(word_node.itertext()).strip()
        if not text:
            continue
        try:
            words.append(
                {
                    "text": text,
                    "x_min": float(word_node.attrib["xMin"]),
                    "y_min": float(word_node.attrib["yMin"]),
                    "x_max": float(word_node.attrib["xMax"]),
                    "y_max": float(word_node.attrib["yMax"]),
                }
            )
        except (KeyError, ValueError):
            continue
    return page_width, page_height, words


def _parse_pdf_bbox_words_with_regex(xml_text: str) -> tuple[float, float, list[dict[str, Any]]]:
    """Fallback bbox parser for PDFs whose extracted XHTML has invalid glyph bytes."""

    page_match = re.search(
        r"<page\b[^>]*\bwidth=\"([0-9.]+)\"[^>]*\bheight=\"([0-9.]+)\"",
        xml_text,
    )
    if not page_match:
        return 0.0, 0.0, []
    try:
        page_width = float(page_match.group(1))
        page_height = float(page_match.group(2))
    except ValueError:
        return 0.0, 0.0, []

    word_re = re.compile(
        r"<word\b[^>]*\bxMin=\"([0-9.]+)\"[^>]*\byMin=\"([0-9.]+)\""
        r"[^>]*\bxMax=\"([0-9.]+)\"[^>]*\byMax=\"([0-9.]+)\"[^>]*>(.*?)</word>",
        flags=re.DOTALL,
    )
    words: list[dict[str, Any]] = []
    for match in word_re.finditer(xml_text):
        text = re.sub(r"<[^>]+>", "", match.group(5))
        text = html.unescape(text).strip()
        if not text:
            continue
        try:
            words.append(
                {
                    "text": text,
                    "x_min": float(match.group(1)),
                    "y_min": float(match.group(2)),
                    "x_max": float(match.group(3)),
                    "y_max": float(match.group(4)),
                }
            )
        except ValueError:
            continue
    return page_width, page_height, words


def _find_statement_start_y(words: list[dict[str, Any]], kind: str, number: str) -> float | None:
    """Locate a statement heading in bbox word output."""

    for index, word in enumerate(words[:-1]):
        if word["text"].strip(".,") != kind:
            continue
        nxt = words[index + 1]
        if nxt["text"].strip(".,") != number:
            continue
        if abs(float(nxt["y_min"]) - float(word["y_min"])) > 6.0:
            continue
        return float(word["y_min"])
    return None


def _find_statement_stop_y(words: list[dict[str, Any]], top_y: float, current_bottom: float) -> float:
    """Find an earlier paper-proof/section boundary inside a candidate crop."""

    stop_sequences = [
        ("Proof",),
        ("Proof.",),
        ("To", "prove"),
        ("The", "proof"),
        ("What", "does"),
    ]
    for index, word in enumerate(words):
        y_min = float(word["y_min"])
        if y_min <= top_y + 18.0 or y_min >= current_bottom:
            continue
        if float(word["x_min"]) > 115.0:
            continue
        row_words = [
            str(candidate["text"]).strip(".,:;")
            for candidate in words[index : index + 4]
            if abs(float(candidate["y_min"]) - y_min) <= 3.0
        ]
        if any(row_words[: len(sequence)] == list(sequence) for sequence in stop_sequences):
            return y_min - 10.0
    return current_bottom


def _render_pdf_page_to_png(pdf_path: Path, page: int, output_dir: Path, digest: str) -> Path | None:
    """Render a single PDF page to a PNG cache file."""

    page_path = output_dir / f"page-{page}-{digest[:12]}.png"
    if page_path.exists():
        return page_path
    prefix = output_dir / f"page-{page}-{digest[:12]}"
    try:
        proc = subprocess.run(
            [
                "pdftoppm",
                "-f",
                str(page),
                "-l",
                str(page),
                "-r",
                "180",
                "-png",
                str(pdf_path),
                str(prefix),
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=20,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    rendered = sorted(output_dir.glob(f"{prefix.name}-*.png"))
    if not rendered:
        return None
    try:
        rendered[0].replace(page_path)
    except OSError:
        return None
    for stale in rendered[1:]:
        try:
            stale.unlink()
        except OSError:
            pass
    return page_path


def attach_rendered_statement_images(folder: Path, items: list[ReviewItem]) -> None:
    """Attach cropped PDF-rendered statement images when a source PDF is available."""

    pdf_path = find_paper_pdf(folder)
    if pdf_path is None:
        return
    locations = parse_paper_text_statement_locations(folder)
    if not locations:
        return

    location_by_key = {str(location["key"]): location for location in locations}
    next_on_same_page: dict[str, dict[str, Any]] = {}
    for index, location in enumerate(locations):
        for later in locations[index + 1 :]:
            if later.get("page") == location.get("page"):
                next_on_same_page[str(location["key"])] = later
                break
            if int(later.get("page") or 0) > int(location.get("page") or 0):
                break

    digest = _file_sha256(pdf_path) or statement_digest(str(pdf_path))
    output_dir = folder / ".review_traces" / PAPER_RENDERED_STATEMENT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)
    bbox_cache: dict[int, tuple[float, float, list[dict[str, Any]]]] = {}

    try:
        from PIL import Image
    except Exception:  # noqa: BLE001 - optional runtime rendering dependency
        Image = None  # type: ignore[assignment]

    for item in items:
        keys = paper_statement_candidate_keys(item.name, item.name)
        location = next((location_by_key[key] for key in keys if key in location_by_key), None)
        if location is None:
            continue
        page = int(location.get("page") or 0)
        if page <= 0:
            continue
        key = str(location["key"])
        crop_path = output_dir / f"{key}-{digest[:12]}.png"
        if crop_path.exists():
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, crop_path)
            continue
        page_png = _render_pdf_page_to_png(pdf_path, page, output_dir, digest)
        if page_png is None:
            continue
        if Image is None:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        if page not in bbox_cache:
            bbox_cache[page] = _parse_pdf_bbox_words(_run_pdftotext_bbox(pdf_path, page))
        page_width, page_height, words = bbox_cache[page]
        if not page_width or not page_height:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        top_y = _find_statement_start_y(
            words, str(location.get("kind") or ""), str(location.get("number") or "")
        )
        if top_y is None:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        next_location = next_on_same_page.get(key)
        bottom_y = page_height - 48.0
        if next_location is not None:
            next_top = _find_statement_start_y(
                words,
                str(next_location.get("kind") or ""),
                str(next_location.get("number") or ""),
            )
            if next_top is not None and next_top > top_y + 20.0:
                bottom_y = next_top - 10.0
        bottom_y = _find_statement_stop_y(words, top_y, bottom_y)
        try:
            with Image.open(page_png) as image:
                scale_x = image.width / page_width
                scale_y = image.height / page_height
                left = max(0, int(54.0 * scale_x))
                upper = max(0, int((top_y - 14.0) * scale_y))
                right = min(image.width, int((page_width - 54.0) * scale_x))
                lower = min(image.height, int((bottom_y + 4.0) * scale_y))
                if lower <= upper + 20 or right <= left + 20:
                    item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
                    continue
                cropped = image.crop((left, upper, right, lower))
                cropped.save(crop_path)
        except OSError:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        item.paper_statement_image_url = paper_rendered_statement_url(folder.name, crop_path)


def paper_statement_candidate_keys(name: str, full_name: str) -> list[str]:
    """Return paper-statement keys likely to correspond to a Lean declaration."""

    raw_candidates = [
        name,
        full_name,
        name.split(".")[-1],
        full_name.split(".")[-1],
        _normalize_name_key(name),
        _normalize_name_key(full_name),
    ]
    for base in [name, full_name.split(".")[-1]]:
        for kind in ("definition", "theorem", "lemma", "proposition", "corollary", "claim"):
            match = re.search(rf"(?:^|_){kind}([A-Za-z]?\d+(?:_\d+)*)", base, flags=re.IGNORECASE)
            if match:
                raw_candidates.append(f"{kind}{match.group(1).lower()}")
                raw_candidates.append(f"{kind}_{match.group(1).lower()}")
    out: list[str] = []
    for candidate in raw_candidates:
        if not candidate:
            continue
        for variant in {candidate, _normalize_name_key(candidate), candidate.lower(), _normalize_name_key(candidate).lower()}:
            if variant and variant not in out:
                out.append(variant)
    return out


def _safe_slice_id(value: str) -> str:
    """Normalize a dashboard slice identifier for local filtering."""

    cleaned = re.sub(r"[^A-Za-z0-9_.-]+", "-", value.strip()).strip("-")
    return cleaned or "all"


def load_review_slice_payload(folder: Path) -> dict[str, Any]:
    """Load optional paper-local review slice metadata."""

    path = folder / DEFAULT_REVIEW_SLICES_FILE
    if not path.exists() or not path.is_file():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(payload, dict):
        return {}
    if payload.get("schema") not in {None, REVIEW_SLICES_SCHEMA}:
        return {}
    return payload


def review_slice_rules(folder: Path) -> list[dict[str, Any]]:
    """Return validated slice rules for a paper folder."""

    payload = load_review_slice_payload(folder)
    raw_slices = payload.get("slices", [])
    if not isinstance(raw_slices, list):
        return []
    out: list[dict[str, Any]] = []
    for index, raw_slice in enumerate(raw_slices, start=1):
        if not isinstance(raw_slice, dict):
            continue
        title = str(raw_slice.get("title") or raw_slice.get("id") or f"Slice {index}").strip()
        if not title:
            title = f"Slice {index}"
        rule = dict(raw_slice)
        rule["id"] = _safe_slice_id(str(raw_slice.get("id") or title))
        rule["title"] = title
        out.append(rule)
    return out


def review_item_matches_slice_rule(item: ReviewItem, rule: dict[str, Any]) -> bool:
    """Check whether an item belongs to one review slice rule."""

    names = rule.get("names")
    if isinstance(names, list) and item.name in {str(name) for name in names}:
        return True

    prefixes = rule.get("prefixes")
    if isinstance(prefixes, list) and any(item.name.startswith(str(prefix)) for prefix in prefixes):
        return True

    pattern = rule.get("name_regex")
    if isinstance(pattern, str) and pattern.strip():
        try:
            if re.search(pattern, item.name):
                return True
        except re.error:
            pass

    line_start = rule.get("line_start")
    line_end = rule.get("line_end")
    if isinstance(line_start, int) or isinstance(line_end, int):
        start_ok = not isinstance(line_start, int) or item.line_number >= line_start
        end_ok = not isinstance(line_end, int) or item.line_number <= line_end
        if start_ok and end_ok:
            return True

    return False


def apply_review_slices(folder: Path, items: list[ReviewItem]) -> list[ReviewItem]:
    """Attach paper-local review slice labels to parsed dashboard rows."""

    rules = review_slice_rules(folder)
    if not rules:
        for item in items:
            item.slice_id = "all"
            item.slice_title = "All statements"
        return items

    payload = load_review_slice_payload(folder)
    fallback_title = str(payload.get("fallback_title") or "Other statements")
    fallback_id = _safe_slice_id(str(payload.get("fallback_id") or "other"))
    for item in items:
        for rule in rules:
            if review_item_matches_slice_rule(item, rule):
                item.slice_id = str(rule["id"])
                item.slice_title = str(rule["title"])
                break
        else:
            item.slice_id = fallback_id
            item.slice_title = fallback_title
    return items


def summarize_review_slices(items: list[ReviewItem]) -> list[dict[str, Any]]:
    """Summarize slices present in a paper's current dashboard rows."""

    order: list[str] = []
    by_id: dict[str, dict[str, Any]] = {}
    for item in items:
        slice_id = item.slice_id or "all"
        if slice_id not in by_id:
            order.append(slice_id)
            by_id[slice_id] = {
                "id": slice_id,
                "title": item.slice_title or slice_id,
                "count": 0,
                "first_line": item.line_number or None,
                "last_line": item.line_number or None,
            }
        row = by_id[slice_id]
        row["count"] += 1
        if item.line_number:
            first_line = row.get("first_line")
            last_line = row.get("last_line")
            row["first_line"] = item.line_number if first_line is None else min(first_line, item.line_number)
            row["last_line"] = item.line_number if last_line is None else max(last_line, item.line_number)
    return [by_id[slice_id] for slice_id in order]


def filter_items_by_slice(
    items: list[ReviewItem], paper_name: str, slice_filter: str | None
) -> list[ReviewItem]:
    """Filter dashboard rows to one slice id or paper-qualified slice id."""

    if not slice_filter:
        return items
    normalized = slice_filter.strip()
    if not normalized:
        return items
    paper_part = ""
    slice_part = normalized
    if "::" in normalized:
        paper_part, slice_part = normalized.split("::", 1)
        if paper_part and paper_part != paper_name:
            return []
    slice_part = _safe_slice_id(slice_part)
    filtered = [item for item in items if item.slice_id == slice_part]
    if filtered:
        return filtered
    if items and {item.slice_id for item in items} == {"all"}:
        return items
    return filtered


def parse_interface_items(
    interface_path: Path, report_path: Path | None, paper_folder: Path | None = None
) -> list[ReviewItem]:
    """Combine declaration signatures and paper statements for one paper folder."""

    rows = interface_path.read_text(encoding="utf-8").splitlines()
    paper_statements = parse_report_texts(report_path) if report_path and report_path.exists() else {}
    if paper_folder is None:
        paper_folder = interface_path.parent
    source_statements = parse_paper_tex_statements(paper_folder)
    if not source_statements:
        source_statements = parse_paper_text_statements(paper_folder)
    paper_statements.update(source_statements)
    llm_tex_drafts = load_llm_lean_to_tex_drafts(paper_folder)

    # Keep declaration names first.
    parsed: list[tuple[str, str, str, str, str | None, int]] = []
    lines = rows
    namespace_stack: list[str] = []
    section_depth = 0
    pending_comment: str | None = None
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        namespace_match = NAMESPACE_OPEN_RE.match(stripped)
        if namespace_match:
            namespace_stack.extend(namespace_match.group(1).split("."))
            i += 1
            continue

        section_match = SECTION_OPEN_RE.match(stripped)
        if section_match:
            section_depth += 1
            i += 1
            continue

        end_match = END_SCOPE_RE.match(stripped)
        if end_match:
            end_name = end_match.group(1)
            if end_name and namespace_stack and namespace_stack[-1] == end_name:
                namespace_stack.pop()
            elif end_name:
                if section_depth > 0:
                    section_depth -= 1
            else:
                if section_depth > 0:
                    section_depth -= 1
                elif namespace_stack:
                    namespace_stack.pop()
            i += 1
            continue

        if COMMENT_START_RE.match(line):
            comment, after = parse_block_comment(lines, i)
            if "/-!" in line or line.lstrip().startswith("/-"):
                pending_comment = clean_comment(comment)
            i = after
            continue

        if stripped.startswith("@[") and stripped.endswith("]"):
            i += 1
            continue

        m = DECL_RE.match(line)
        if m:
            name = m.group("name")
            kind = m.group("kind")
            full_name = ".".join(namespace_stack + [name]) if namespace_stack else name
            sig_lines: list[str] = []
            j = i
            saw_sig = False
            while j < len(lines):
                sig_line = lines[j]
                sig_lines.append(sig_line)
                if ":=" in sig_line:
                    idx = sig_line.find(":=")
                    sig_lines[-1] = sig_line[:idx]
                    saw_sig = True
                    break
                j += 1
            if saw_sig:
                raw_sig = "\n".join(sig_lines).strip()
                parsed.append((kind, name, full_name, raw_sig, pending_comment, i + 1))
            pending_comment = None
            i = j + 1
            continue

        if stripped and not stripped.startswith("--") and not stripped.startswith("/-"):
            pending_comment = None
        i += 1

    check_map = run_lean_check_previews(
        paper_folder,
        [
            full_name
            for kind, _name, full_name, _raw_sig, _comment, _line_number in parsed
            if kind in REVIEW_DECL_KINDS
        ],
        source_file=interface_path,
    )

    out: list[ReviewItem] = []
    for kind, name, full_name, raw_sig, doc_comment, line_number in parsed:
        if kind not in REVIEW_DECL_KINDS:
            continue
        check_statement = check_map.get(full_name) or check_map.get(name)
        lean_statement = f"@{full_name} :\n{check_statement}" if check_statement else raw_sig
        candidates = paper_statement_candidate_keys(name, full_name)
        paper_text = ""
        for candidate in candidates:
            if candidate and candidate in paper_statements:
                paper_text = paper_statements[candidate]
                break
        out.append(
            ReviewItem(
                name=name,
                kind=kind,
                lean_statement=lean_statement,
                paper_statement=paper_text
                if paper_text
                else (doc_comment if doc_comment else ""),
                agent_statement=llm_tex_drafts.get(name)
                or llm_tex_drafts.get(full_name)
                or agent_preview_comment(doc_comment, lean_statement, check_statement),
                line_number=line_number,
            )
        )
    return apply_review_slices(paper_folder, out)


def paper_title(folder: Path) -> str:
    readme = folder / "README.md"
    if readme.exists():
        for line in readme.read_text(encoding="utf-8").splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    return folder.name


def iter_paper_folders(paper_filter: str | None = None) -> list[Path]:
    """Return paper directories that have a human-review Lean surface."""

    folders: list[Path] = []
    for folder in sorted(PAPERS_DIR.iterdir()):
        if not folder.is_dir():
            continue
        if folder.name == "TEMPLATE":
            continue
        if paper_filter and folder.name != paper_filter:
            continue
        if find_review_source_file(folder) is None:
            continue
        folders.append(folder)
    return folders


def paper_review_log_file(paper: str | Path) -> Path:
    """Return the default per-paper trace file path for a paper."""

    folder = PAPERS_DIR / str(paper)
    if not folder.exists() or not folder.is_dir():
        raise ValueError(f"unknown paper folder: {paper}")
    if find_review_source_file(folder) is None:
        raise ValueError(f"no human review Lean surface for paper: {paper}")
    return folder / ".review_traces" / DEFAULT_PAPER_LOG_FILE


def paper_interface_cache_file(paper: str | Path) -> Path:
    """Return the local sidecar file for cached declaration and statement rows."""

    folder = PAPERS_DIR / str(paper)
    if not folder.exists() or not folder.is_dir():
        raise ValueError(f"unknown paper folder: {paper}")
    if find_review_source_file(folder) is None:
        raise ValueError(f"no human review Lean surface for paper: {paper}")
    return folder / ".review_traces" / DEFAULT_PAPER_INTERFACE_CACHE_FILE


def _cache_source_hashes(folder: Path) -> dict[str, str]:
    interface_path = review_source_file(folder)
    report_path = folder / "FINAL_VALIDATION_REPORT.md"
    tex_path = find_paper_tex_source(folder)
    text_path = find_paper_text(folder)
    pdf_path = find_paper_pdf(folder)
    llm_tex_path = folder / ".review_traces" / DEFAULT_LLM_LEAN_TO_TEX_FILE
    slice_path = folder / DEFAULT_REVIEW_SLICES_FILE

    interface_source = interface_path.read_text(encoding="utf-8") if interface_path.exists() else ""
    report_source = report_path.read_text(encoding="utf-8") if report_path.exists() else ""
    tex_source = tex_path.read_text(encoding="utf-8") if tex_path and tex_path.exists() else ""
    text_source = text_path.read_text(encoding="utf-8") if text_path and text_path.exists() else ""
    llm_tex_source = llm_tex_path.read_text(encoding="utf-8") if llm_tex_path.exists() else ""
    slice_source = slice_path.read_text(encoding="utf-8") if slice_path.exists() else ""

    return {
        "review_source_file": interface_path.name,
        "interface_sha256": statement_digest(interface_source),
        "report_sha256": statement_digest(report_source),
        "tex_sha256": statement_digest(tex_source),
        "text_sha256": statement_digest(text_source),
        "pdf_sha256": _file_sha256(pdf_path),
        "llm_tex_sha256": statement_digest(llm_tex_source),
        "review_slices_sha256": statement_digest(slice_source),
    }


def load_cached_review_rows(folder: Path) -> list[ReviewItem] | None:
    """Load cached dashboard rows if they are still aligned with paper sources."""

    cache_path = paper_interface_cache_file(folder)
    if not cache_path.exists() or not cache_path.is_file():
        return None

    try:
        payload = json.loads(cache_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None

    if payload.get("schema") != PAPER_INTERFACE_CACHE_SCHEMA:
        return None
    if payload.get("paper") != folder.name:
        return None

    hashes = _cache_source_hashes(folder)
    if payload.get("hashes", {}).get("review_source_file") != hashes["review_source_file"]:
        return None
    if payload.get("hashes", {}).get("interface_sha256") != hashes["interface_sha256"]:
        return None
    if payload.get("hashes", {}).get("report_sha256") != hashes["report_sha256"]:
        return None
    if payload.get("hashes", {}).get("tex_sha256") != hashes["tex_sha256"]:
        return None
    if payload.get("hashes", {}).get("text_sha256") != hashes["text_sha256"]:
        return None
    if payload.get("hashes", {}).get("pdf_sha256") != hashes["pdf_sha256"]:
        return None
    if payload.get("hashes", {}).get("llm_tex_sha256") != hashes["llm_tex_sha256"]:
        return None
    if payload.get("hashes", {}).get("review_slices_sha256") != hashes["review_slices_sha256"]:
        return None

    rows = payload.get("rows")
    if not isinstance(rows, list):
        return None

    out: list[ReviewItem] = []
    for raw_row in rows:
        if not isinstance(raw_row, dict):
            continue
        name = str(raw_row.get("name") or "").strip()
        kind = str(raw_row.get("kind") or "").strip()
        lean_statement = str(raw_row.get("lean_statement") or "").strip()
        paper_statement = str(raw_row.get("paper_statement") or "").strip()
        agent_statement = str(raw_row.get("agent_statement") or "").strip()
        paper_statement_image_url = str(raw_row.get("paper_statement_image_url") or "").strip()
        line_number = int(raw_row.get("line_number") or 0)
        slice_id = _safe_slice_id(str(raw_row.get("slice_id") or "all"))
        slice_title = str(raw_row.get("slice_title") or "All statements").strip()
        if not name or not kind or not lean_statement:
            continue
        out.append(
            ReviewItem(
                name=name,
                kind=kind,
                lean_statement=lean_statement,
                paper_statement=paper_statement,
                agent_statement=agent_statement,
                paper_statement_image_url=paper_statement_image_url,
                line_number=line_number,
                slice_id=slice_id,
                slice_title=slice_title or slice_id,
            )
        )
    return out or None


def write_cached_review_rows(folder: Path, items: list[ReviewItem]) -> None:
    """Persist dashboard rows with source hashes for future reloads."""

    cache_path = paper_interface_cache_file(folder)
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": PAPER_INTERFACE_CACHE_SCHEMA,
        "paper": folder.name,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
            "+00:00", "Z"
        ),
        "hashes": _cache_source_hashes(folder),
        "rows": [item.__dict__ for item in items],
    }
    cache_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def review_items_for_paper(folder: Path, use_cache: bool = True) -> list[ReviewItem]:
    """Read cached items if possible, else compute from source files."""

    if use_cache:
        cached = load_cached_review_rows(folder)
        if cached is not None:
            attach_rendered_statement_images(folder, cached)
            return cached

    interface = review_source_file(folder)
    report = folder / "FINAL_VALIDATION_REPORT.md"
    items = parse_interface_items(interface, report if report.exists() else None, folder)
    attach_rendered_statement_images(folder, items)
    return items


def refresh_cached_review_rows(folder: Path) -> None:
    """Force cache regeneration for one paper folder."""

    items = review_items_for_paper(folder, use_cache=False)
    write_cached_review_rows(folder, items)


def describe_log_target(log_file: Path | None, paper: str | None = None) -> str:
    """User-visible label for where logs are persisted/read."""

    if log_file is not None:
        return str(log_file)
    if paper:
        try:
            return str(paper_review_log_file(paper))
        except ValueError:
            pass
    return "per-paper traces in each folder at <Paper>/.review_traces/paper_theorem_validations.jsonl"


def read_all_log_entries(
    paper_filter: str | None, log_file: Path | None
) -> list[dict[str, Any]]:
    """Collect review logs across selected papers or from an override log file."""

    if log_file is not None:
        entries = read_log_entries(log_file)
        if paper_filter:
            entries = [entry for entry in entries if entry.get("paper") == paper_filter]
        return entries

    entries: list[dict[str, Any]] = []
    for folder in iter_paper_folders(paper_filter):
        entries.extend(read_log_entries(paper_review_log_file(folder.name)))
    entries.sort(key=lambda row: row.get("timestamp", ""))
    return entries


def gather_paper_data(
    paper_filter: str | None = None, slice_filter: str | None = None
) -> list[dict[str, Any]]:
    papers = []
    for folder in iter_paper_folders(paper_filter):
        all_items = review_items_for_paper(folder, use_cache=True)
        items = filter_items_by_slice(all_items, folder.name, slice_filter)
        assets = {}
        paper_pdf = find_paper_pdf(folder)
        if paper_pdf:
            assets["pdf"] = {
                "name": paper_pdf.name,
                "url": paper_asset_url(folder.name, paper_pdf),
            }
        paper_text = find_paper_text(folder)
        if paper_text:
            assets["text"] = {
                "name": paper_text.name,
                "url": paper_asset_url(folder.name, paper_text),
                "extension": paper_text.suffix.lower(),
            }
        papers.append(
            {
                "name": folder.name,
                "title": paper_title(folder),
                "items": [item.__dict__ for item in items],
                "slices": summarize_review_slices(all_items),
                "active_slice": slice_filter or "",
                "assets": assets,
            }
        )
    return papers


def get_item_statements(paper: str, theorem: str) -> tuple[str, str, str]:
    """Lookup the current Lean, paper, and agent preview statements for one theorem."""

    for paper_data in gather_paper_data(paper):
        if paper_data.get("name") != paper:
            continue
        for item in paper_data.get("items", []):
            if item.get("name") == theorem:
                return (
                    str(item.get("lean_statement") or ""),
                    str(item.get("paper_statement") or ""),
                    str(item.get("agent_statement") or ""),
                )
    return "", "", ""


def read_log_entries(log_file: Path, paper: str | None = None) -> list[dict[str, Any]]:
    if not log_file.exists():
        return []
    entries: list[dict[str, Any]] = []
    for raw in log_file.read_text(encoding="utf-8").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            entry = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if paper and entry.get("paper") != paper:
            continue
        entries.append(entry)
    entries.sort(key=lambda row: row.get("timestamp", ""))
    return entries


def item_digest(item: dict[str, Any], key: str) -> str:
    """Get current or fall-backed digest for an item key."""

    value = str(item.get(key) or "")
    return statement_digest(value)


def review_is_stale(
    entry: dict[str, Any], item: dict[str, Any]
) -> tuple[bool, bool]:
    """Return `(lean_stale, paper_stale)` relative to current item snapshot."""

    if not item:
        return False, False

    current_lean = item_digest(item, "lean_statement")
    current_paper = item_digest(item, "paper_statement")
    reviewed_lean = str(entry.get("lean_statement_sha256") or statement_digest(str(entry.get("lean_statement", "")))).strip()
    reviewed_paper = str(entry.get("paper_statement_sha256") or statement_digest(str(entry.get("paper_statement", "")))).strip()

    return current_lean != reviewed_lean and bool(current_lean), current_paper != reviewed_paper and bool(current_paper)


def build_review_status(papers: list[dict[str, Any]], reviews: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Build compact theorem-level review status rows."""

    by_key: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for entry in reviews:
        paper = str(entry.get("paper") or "").strip()
        theorem = str(entry.get("theorem") or "").strip()
        if not paper or not theorem:
            continue
        by_key.setdefault((paper, theorem), []).append(entry)

    rows: list[dict[str, Any]] = []
    for paper in papers:
        paper_name = paper["name"]
        for item in paper["items"]:
            theorem = item["name"]
            key = (paper_name, theorem)
            history = sorted(by_key.get(key, []), key=lambda row: row.get("timestamp", ""))
            latest = history[-1] if history else None
            stale_lean = False
            stale_paper = False
            if latest:
                stale_lean, stale_paper = review_is_stale(latest, item)

            latest_user = latest.get("user") if latest else ""
            latest_ts = latest.get("timestamp") if latest else ""
            latest_matches = latest.get("matches") if latest else None
            rows.append(
                {
                    "paper": paper_name,
                    "theorem": theorem,
                    "kind": item["kind"],
                    "line_number": item.get("line_number", 0),
                    "slice_id": item.get("slice_id", "all"),
                    "slice_title": item.get("slice_title", "All statements"),
                    "has_review": latest is not None,
                    "review_count": len(history),
                    "needs_attention": latest is None
                    or stale_lean
                    or stale_paper
                    or latest_matches is False,
                    "latest_user": latest_user,
                    "latest_timestamp": latest_ts,
                    "latest_matches": latest_matches,
                    "latest_notes": latest.get("notes") if latest else "",
                    "lean_stale": stale_lean,
                    "paper_stale": stale_paper,
                }
            )
    rows.sort(key=lambda row: (row["paper"], row["theorem"]))
    return rows


def filter_review_rows(
    rows: list[dict[str, Any]], user_filter: str | None = None, stale_only: bool = False
) -> list[dict[str, Any]]:
    if user_filter:
        user_filter = user_filter.strip()
    if not user_filter and not stale_only:
        return rows
    out: list[dict[str, Any]] = []
    for row in rows:
        if stale_only and not row.get("needs_attention"):
            continue
        if user_filter and row.get("latest_user") != user_filter:
            continue
        out.append(row)
    return out


def render_csv_summary(rows: list[dict[str, Any]]) -> str:
    header = [
        "paper",
        "slice",
        "theorem",
        "kind",
        "line_number",
        "has_review",
        "review_count",
        "needs_attention",
        "latest_user",
        "latest_timestamp",
        "latest_matches",
        "lean_stale",
        "paper_stale",
    ]
    out = io.StringIO()
    writer = csv.writer(out)
    writer.writerow(header)
    for row in rows:
        writer.writerow(
            [
                row["paper"],
                row.get("slice_title", row.get("slice_id", "")),
                row["theorem"],
                row["kind"],
                str(row.get("line_number") or ""),
                "true" if row["has_review"] else "false",
                str(row["review_count"]),
                "true" if row["needs_attention"] else "false",
                row.get("latest_user", ""),
                row.get("latest_timestamp", ""),
                "true" if row.get("latest_matches") else "false",
                "true" if row.get("lean_stale") else "false",
                "true" if row.get("paper_stale") else "false",
            ]
        )
    rendered = out.getvalue()
    out.close()
    return rendered


def _escape_md(value: Any) -> str:
    return str(value).replace("|", "\\|").replace("\n", "<br/>")


def render_markdown_summary(rows: list[dict[str, Any]]) -> str:
    lines = [
        "| Paper | Slice | Theorem | Kind | Line | Reviewed | Reviews | Needs attention | Latest | Latest timestamp | Matches | Lean stale | Paper stale | Notes |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            "| " + " | ".join(
                [
                    _escape_md(row["paper"]),
                    _escape_md(row.get("slice_title") or row.get("slice_id") or ""),
                    _escape_md(row["theorem"]),
                    _escape_md(row["kind"]),
                    str(row.get("line_number") or ""),
                    "yes" if row["has_review"] else "no",
                    str(row["review_count"]),
                    "yes" if row["needs_attention"] else "no",
                    _escape_md(row.get("latest_user") or "—"),
                    _escape_md(row.get("latest_timestamp", "")),
                    "yes" if row.get("latest_matches") else "no",
                    "yes" if row.get("lean_stale") else "no",
                    "yes" if row.get("paper_stale") else "no",
                    _escape_md(row.get("latest_notes", "")),
                ]
            )
            + " |"
        )
    return "\n".join(lines) + "\n"


def status_totals(rows: list[dict[str, Any]]) -> dict[str, Any]:
    total = len(rows)
    reviewed = sum(1 for row in rows if row.get("has_review"))
    stale = sum(1 for row in rows if row.get("needs_attention"))
    lean_stale = sum(1 for row in rows if row.get("lean_stale"))
    paper_stale = sum(1 for row in rows if row.get("paper_stale"))
    no_review = total - reviewed
    return {
        "total_items": total,
        "reviewed_items": reviewed,
        "unreviewed_items": no_review,
        "needs_attention_items": stale,
        "lean_stale_items": lean_stale,
        "paper_stale_items": paper_stale,
    }


def stale_review_rows(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    """Partition rows into stale and unreviewed buckets for launch-time diagnostics."""

    stale = [row for row in rows if row.get("has_review") and (row.get("lean_stale") or row.get("paper_stale"))]
    unreviewed = [row for row in rows if not row.get("has_review")]
    mismatch = [
        row
        for row in rows
        if row.get("has_review")
        and not row.get("lean_stale")
        and not row.get("paper_stale")
        and row.get("latest_matches") is False
    ]
    return {"stale": stale, "unreviewed": unreviewed, "mismatch": mismatch}


def parse_bool_flag(value: str | None) -> bool:
    if not value:
        return False
    return value.lower() in {"1", "true", "t", "yes", "y", "on"}


def append_review(log_file: Path, payload: dict[str, Any], default_user: str) -> dict[str, Any]:
    log_file.parent.mkdir(parents=True, exist_ok=True)

    paper = str(payload.get("paper") or "").strip()
    theorem = str(payload.get("theorem") or "").strip()
    user = str(payload.get("user") or default_user).strip() or default_user
    notes = str(payload.get("notes", "")).strip()
    matches = bool(payload.get("matches", False))
    lean_statement = str(payload.get("lean_statement") or "").strip()
    paper_statement = str(payload.get("paper_statement") or "").strip()
    agent_statement = str(payload.get("agent_statement") or "").strip()
    if not paper or not theorem:
        raise ValueError("missing paper/theorem")
    if not lean_statement or not paper_statement or not agent_statement:
        current_lean_statement, current_paper_statement, current_agent_statement = get_item_statements(
            paper, theorem
        )
        if not lean_statement:
            lean_statement = current_lean_statement
        if not paper_statement:
            paper_statement = current_paper_statement
        if not agent_statement:
            agent_statement = current_agent_statement

    entry = {
        "paper": paper,
        "theorem": theorem,
        "user": user,
        "paper_statement": paper_statement,
        "lean_statement": lean_statement,
        "agent_statement": agent_statement,
        "lean_statement_sha256": statement_digest(lean_statement),
        "paper_statement_sha256": statement_digest(paper_statement),
        "agent_statement_sha256": statement_digest(agent_statement),
        "matches": matches,
        "notes": notes,
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
    }
    with log_file.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry))
        handle.write("\n")
    return entry


HTML_PAGE = """
<!doctype html>
<html lang='en'>
<head>
  <meta charset='utf-8' />
  <meta name='viewport' content='width=device-width, initial-scale=1' />
  <title>Paper Interface Review Dashboard</title>
    <style>
    :root {
      --bg: #f5f7fb;
      --panel: #ffffff;
      --line: #e5e8ee;
      --line-strong: #ccd4e0;
      --muted: #5d6678;
      --text: #172039;
      --accent: #1f6feb;
      --accent-soft: #e8f1ff;
      --ok: #0b8043;
      --ok-soft: #e7f4ed;
      --bad: #aa2e2e;
      --bad-soft: #fae8e8;
      --warn: #a35f00;
      --warn-soft: #fff3dd;
      --neutral-soft: #f2f5f9;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      background: var(--bg);
      color: var(--text);
      font-family: "Inter", "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      -webkit-font-smoothing: antialiased;
      line-height: 1.35;
    }
    .page {
      width: min(1800px, calc(100% - 16px));
      margin: 0 auto;
      padding: 18px 0 30px;
    }
    h1 {
      margin: 0 0 8px;
      font-size: 28px;
      letter-spacing: 0;
    }
    .subtitle { color: var(--muted); margin: 0 0 14px; }
    .toolbar {
      margin: 14px 0 16px;
      display: flex;
      gap: 12px;
      align-items: center;
      flex-wrap: wrap;
      background: var(--panel);
      padding: 10px 12px;
      border-radius: 8px;
      border: 1px solid var(--line);
      box-shadow: 0 1px 2px rgba(25, 33, 58, 0.06);
    }
    .toolbar label { font-size: 13px; color: #334155; }
    .toolbar input, .toolbar select {
      margin-left: 8px;
      border: 1px solid var(--line);
      border-radius: 7px;
      padding: 8px 10px;
      min-width: 170px;
      font: inherit;
      background: #fff;
    }
    .toolbar select { min-width: 150px; }
    .toolbar-toggle {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      color: #334155;
      font-size: 13px;
    }
    .toolbar-toggle input {
      min-width: 0;
      margin-left: 0;
    }
    .summary-grid {
      display: grid;
      grid-template-columns: repeat(4, minmax(120px, 1fr));
      gap: 10px;
      margin: 0 0 12px;
    }
    .summary-card {
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 10px 12px;
      box-shadow: 0 1px 2px rgba(25, 33, 58, 0.04);
    }
    .summary-card .label {
      color: var(--muted);
      font-size: 12px;
      margin-bottom: 2px;
    }
    .summary-card .value {
      color: var(--text);
      font-weight: 700;
      font-size: 20px;
    }
    .muted { color: var(--muted); }
    .small { font-size: 12px; }
    .paper-block {
      margin: 16px 0;
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 12px;
      background: var(--panel);
      box-shadow: 0 1px 2px rgba(25, 33, 58, 0.04);
    }
    .paper-header {
      display: flex;
      justify-content: space-between;
      gap: 12px;
      align-items: flex-start;
      margin-bottom: 10px;
    }
    .paper-block h2 { margin: 0; font-size: 22px; }
    .paper-progress {
      color: var(--muted);
      font-size: 12px;
      text-align: right;
      min-width: 180px;
    }
    .paper-source-panel {
      border: 1px solid #e5ecff;
      border-radius: 8px;
      padding: 7px 10px;
      background: #f7faff;
      margin-bottom: 10px;
    }
    .paper-source-heading { margin: 0 0 8px; font-size: 14px; }
    .paper-source-subtle {
      color: #334155;
      margin-bottom: 6px;
      font-size: 12px;
      line-height: 1.35;
    }
    .source-actions {
      display: flex;
      gap: 8px;
      flex-wrap: wrap;
      margin: 8px 0 4px;
    }
    .source-link {
      border: 1px solid #cad3e5;
      border-radius: 7px;
      padding: 6px 9px;
      text-decoration: none;
      color: #1e293b;
      background: #fff;
      font-size: 12px;
      transition: border-color 0.15s ease;
    }
    .source-link:hover {
      border-color: #9fb0d8;
      background: #fbfdff;
    }
    .table-wrap { overflow-x: auto; }
    .paper-details {
      border: 0;
    }
    .paper-details > summary {
      list-style: none;
      cursor: pointer;
    }
    .paper-details > summary::-webkit-details-marker { display: none; }
    table {
      width: 100%;
      border-collapse: collapse;
      margin-top: 0;
      min-width: 0;
      table-layout: auto;
    }
    th, td { border: 1px solid var(--line); padding: 10px; vertical-align: top; }
    thead th {
      background: #f8f9fc;
      text-align: left;
      position: sticky;
      top: 0;
      z-index: 1;
    }
    tbody tr { background: #ffffff; }
    tbody tr:hover { background: #fbfcff; }
    tbody tr:nth-child(odd) { background: #fcfdff; }
    tbody tr.is-hidden { display: none; }
    body.hide-agent .agent-column { display: none; }
    .review-item {
      display: grid;
      grid-template-columns: minmax(0, 1fr) minmax(220px, 280px);
      gap: 12px;
      align-items: start;
    }
    .review-main {
      min-width: 0;
      display: grid;
      gap: 10px;
    }
    .review-controls {
      min-width: 0;
      border-left: 1px solid var(--line);
      padding-left: 12px;
    }
    .review-section {
      min-width: 0;
    }
    .review-section-label {
      font-size: 12px;
      color: var(--muted);
      margin-bottom: 5px;
      font-family: "Inter", "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
    }
    .col-paper, .col-lean, .col-agent { white-space: pre-wrap; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 13px; line-height: 1.35; }
    .col-agent { white-space: normal; }
    .col-paper, .col-lean, .col-agent { width: 100%; }
    .statement-box {
      border: 1px solid var(--line);
      border-radius: 7px;
      background: #fff;
    }
    .statement-box[open] {
      background: #fcfdff;
    }
    .statement-box summary {
      cursor: pointer;
      color: #334155;
      background: #f8f9fc;
      padding: 7px 9px;
      border-radius: 7px;
      font-family: "Inter", "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      font-size: 12px;
    }
    .statement-box[open] summary {
      border-bottom: 1px solid var(--line);
      border-radius: 7px 7px 0 0;
    }
    .statement-body {
      padding: 9px;
      max-height: 520px;
      overflow: auto;
      white-space: pre-wrap;
      word-break: break-word;
    }
    .col-lean .statement-body {
      white-space: pre-wrap;
      overflow-x: hidden;
      overflow-wrap: anywhere;
      word-break: break-word;
    }
    .col-lean .statement-body code {
      display: block;
      max-width: 100%;
      white-space: pre-wrap;
      overflow-wrap: anywhere;
      word-break: break-word;
    }
    .statement-body code {
      white-space: pre-wrap;
      word-break: break-word;
    }
    .paper-statement-image {
      display: block;
      width: 100%;
      max-width: none;
      height: auto;
      background: #fff;
      border: 1px solid #d8e0ec;
      border-radius: 6px;
      margin-bottom: 8px;
    }
    .statement-preview {
      display: block;
      margin-top: 4px;
      color: var(--muted);
      overflow: hidden;
      text-overflow: ellipsis;
      white-space: nowrap;
      max-width: 100%;
    }
    .agent-statement {
      white-space: pre-wrap;
      word-break: break-word;
    }
    .agent-statement code {
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      white-space: pre-wrap;
      word-break: break-word;
    }
    .col-review { width: 18%; min-width: 220px; }
    .paper-title { font-weight: 600; margin-bottom: 8px; }
    .slice-meta {
      margin: -4px 0 8px;
      color: var(--muted);
      font-size: 12px;
      line-height: 1.3;
    }
    .row-note {
      width: 100%;
      min-height: 72px;
      border: 1px solid var(--line);
      border-radius: 7px;
      padding: 8px;
      font: inherit;
      resize: vertical;
    }
    .history { margin-top: 10px; font-size: 12px; color: #334155; }
    .history-entry { border-top: 1px dashed #d6dce6; padding-top: 8px; margin-top: 8px; }
    .history-entry + .history-entry { border-top: 1px dashed #d6dce6; }
    .ok { color: var(--ok); }
    .bad { color: var(--bad); }
    .warn { color: var(--warn); }
    .btn {
      margin-top: 8px;
      border: 1px solid #2f3d5f;
      border-radius: 7px;
      background: var(--accent);
      color: #fff;
      padding: 8px 10px;
      cursor: pointer;
      font-weight: 600;
      transition: filter 0.12s ease;
    }
    .btn:hover { filter: brightness(0.96); }
    .btn:active { transform: translateY(1px); }
    .btn[disabled] {
      cursor: wait;
      opacity: 0.72;
    }
    .status-pill {
      display: inline-block;
      border: 1px solid var(--line-strong);
      border-radius: 999px;
      padding: 3px 8px;
      font-size: 12px;
      background: var(--neutral-soft);
      color: #334155;
      line-height: 1.2;
    }
    .status-pill.ok {
      background: var(--ok-soft);
      border-color: #b8dec8;
      color: var(--ok);
    }
    .status-pill.warn {
      background: var(--warn-soft);
      border-color: #f0cf91;
      color: var(--warn);
    }
    .status-pill.bad {
      background: var(--bad-soft);
      border-color: #efb6b6;
      color: var(--bad);
    }
    .status-line {
      display: flex;
      flex-wrap: wrap;
      gap: 6px;
      align-items: center;
      margin: 0 0 8px;
    }
    .save-status {
      display: inline-block;
      min-height: 16px;
      margin-left: 8px;
    }
    .summary-pill { margin-left: 8px; }
    .summary { margin-left: auto; display: inline-flex; gap: 10px; }
    .empty-filter {
      display: none;
      background: var(--panel);
      border: 1px dashed var(--line-strong);
      border-radius: 8px;
      padding: 16px;
      color: var(--muted);
      text-align: center;
    }
    @media (max-width: 860px) {
      .summary-grid { grid-template-columns: repeat(2, minmax(120px, 1fr)); }
      .paper-header { display: block; }
      .paper-progress { text-align: left; margin-top: 4px; }
      .toolbar input, .toolbar select { min-width: 130px; }
      .review-item { grid-template-columns: 1fr; }
      .review-controls {
        border-left: 0;
        border-top: 1px solid var(--line);
        padding-left: 0;
        padding-top: 10px;
      }
    }

  </style>
  <script>
    window.MathJax = {
      tex: {
        inlineMath: [["\\\\(", "\\\\)"], ["$", "$"]],
        processEscapes: true,
        tags: "none",
      },
      startup: {
        typeset: false,
      },
    };
  </script>
  <script async id="mathjax-script" src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
</head>
<body>
  <div class='page'>
    <h1>Paper Interface Review Dashboard</h1>
    <p class='subtitle'>Trace-backed validator for Lean paper-interface theorem statements.</p>
    <div id='summaryCards' class='summary-grid' aria-live='polite'>
      <div class='summary-card'><div class='label'>Reviewed</div><div class='value' id='cardReviewed'>0/0</div></div>
      <div class='summary-card'><div class='label'>Need Action</div><div class='value' id='cardAttention'>0</div></div>
      <div class='summary-card'><div class='label'>Stale</div><div class='value' id='cardStale'>0</div></div>
      <div class='summary-card'><div class='label'>Mismatch</div><div class='value' id='cardMismatch'>0</div></div>
    </div>
    <div class='toolbar'>
      <label>
        GitHub/user handle:
        <input id='userHandle' type='text' value='{user}' />
      </label>
      <label>
        Search:
        <input id='searchBox' type='search' placeholder='Paper or theorem' />
      </label>
      <label>
        View:
        <select id='statusFilter'>
          <option value='all'>All rows</option>
          <option value='attention'>Needs action</option>
          <option value='unreviewed'>Unreviewed</option>
          <option value='stale'>Stale</option>
          <option value='mismatch'>Marked mismatch</option>
          <option value='reviewed'>Reviewed</option>
        </select>
      </label>
      <label>
        Slice:
        <select id='sliceFilter'>
          <option value='all'>All slices</option>
        </select>
      </label>
      <label class='toolbar-toggle'>
        <input id='hideAgentDraft' type='checkbox' />
        Hide Lean draft
      </label>
      <span id='summary' class='summary small muted'></span>
      <span id='count' class='small muted'></span>
      <span id='logPath' class='small muted'></span>
    </div>
    <div id='emptyFilter' class='empty-filter'>No rows match the current filters.</div>
    <div id='containers'>Loading…</div>
  </div>

  <script>
    window.addEventListener("error", (event) => {
      const container = document.getElementById("containers");
      if (container) {
        container.textContent = `Dashboard render error: ${event.message || "unknown error"}`;
      }
    });
    window.addEventListener("unhandledrejection", (event) => {
      const container = document.getElementById("containers");
      if (container) {
        container.textContent = `Dashboard render error: ${event.reason || "unknown promise rejection"}`;
      }
    });
    const state = {
      papers: __PAPERS__,
      logPath: __LOG_PATH__,
      user: __USER__,
      reviews: [],
      statusRows: [],
    };

    function byLatest(entries) {
      entries.sort((a, b) => (a.timestamp < b.timestamp ? 1 : -1));
    }

    function safeId(value) {
      return String(value).replace(/[^a-zA-Z0-9_-]/g, "_");
    }

    function normalizeStatement(value) {
      return String(value || "").replace(/\s+/g, " ").trim();
    }

    function escapeHtml(value) {
      const span = document.createElement("span");
      span.textContent = String(value);
      return span.innerHTML;
    }

    function isLongProse(value) {
      const text = value.replace(/[^A-Za-z]/g, " ").trim();
      if (!text) {
        return false;
      }
      const words = text.split(/\s+/);
      const longWords = words.filter((word) => word.length >= 4);
      return longWords.length > 12;
    }

    function looksLikeLatex(value) {
      return /\\\\[a-zA-Z]+/.test(value)
        || /[∀∃→↔≤≥≠∞∈∉∑∏ℝℕ]/.test(value)
        || /\\\\/.test(value);
    }

    function isFormulaValue(value) {
      if (!value) {
        return false;
      }
      if (isLongProse(value)) {
        return false;
      }
      if (/[`$]/.test(value)) {
        return false;
      }
      return looksLikeLatex(value) && value.length < 1800;
    }

    function renderPaperStatement(value) {
      const text = escapeHtml(value || "No paper-facing summary found.");
      if (!value || !String(value).trim()) {
        return text;
      }

      if (isFormulaValue(String(value))) {
        return `\\\\(${text}\\\\)`;
      }

      const marked = text.replace(/`([^`]+)`/g, (match, content) => {
        const body = content.trim();
        return looksLikeLatex(body) ? `\\(${body}\\)` : `<code>${body}</code>`;
      });
      return marked.replace(/\\n/g, "<br/>");
    }

    function renderTexDraft(value) {
      const text = escapeHtml(value || "No auto-generated preview available.");
      return text.replace(/\\n/g, "<br/>");
    }

    function softWrapLeanSegment(segment) {
      if (segment.length < 24) {
        return segment;
      }
      return segment.replace(/_/g, "_\\u200b");
    }

    function prettyLeanIdentifier(identifier, indent = "      ") {
      const softDot = ".\\u200b";
      const parts = identifier.split(".");
      if (parts.length <= 1) {
        return softWrapLeanSegment(identifier);
      }

      const wrappedParts = parts.map(softWrapLeanSegment);
      const softWrapped = wrappedParts.join(softDot);
      if (identifier.length <= 54) {
        return softWrapped;
      }

      const namespace = wrappedParts.slice(0, -1).join(softDot);
      const last = wrappedParts[wrappedParts.length - 1];
      if (namespace.length <= 64) {
        return `${namespace}.${softDot}\\n${indent}${last}`;
      }

      return wrappedParts
        .map((part, index) => (index < wrappedParts.length - 1 ? `${part}.` : part))
        .join(`\\n${indent}`);
    }

    function prettyLeanIdentifiers(text) {
      return text.replace(
        /[A-Za-z_][A-Za-z0-9_']*(?:\\.[A-Za-z_][A-Za-z0-9_']*)+/g,
        (identifier) => prettyLeanIdentifier(identifier)
      );
    }

    function wrapLeanLine(line, maxWidth = 98) {
      if (line.length <= maxWidth) {
        return line;
      }
      const indent = (line.match(/^\\s*/) || [""])[0];
      const continuation = `${indent}  `;
      const out = [];
      let rest = line.trimEnd();

      while (rest.length > maxWidth) {
        const windowText = rest.slice(0, maxWidth);
        const breakpoints = [" (", " {", " [", "), ", ", ", " "]
          .map((marker) => windowText.lastIndexOf(marker))
          .filter((index) => index > indent.length + 18);
        const breakAt = breakpoints.length ? Math.max(...breakpoints) : -1;
        if (breakAt <= 0) {
          break;
        }
        out.push(rest.slice(0, breakAt).trimEnd());
        rest = continuation + rest.slice(breakAt).trimStart();
      }
      out.push(rest);
      return out.join("\\n");
    }

    function wrapLeanLines(text) {
      return text
        .split("\\n")
        .map((line) => wrapLeanLine(line))
        .join("\\n");
    }

    function prettyLeanStatement(value) {
      let text = String(value || "No statement text.").replace(/\\r\\n/g, "\\n");
      text = text.replace(/ :\\n\\s*/g, " :\\n  ");
      text = text.replace(/\\} \\{/g, "}\\n  {");
      text = text.replace(/\\} \\(/g, "}\\n  (");
      text = text.replace(/\\] \\[/g, "]\\n  [");
      text = text.replace(/\\] \\(/g, "]\\n  (");
      text = text.replace(/\\) \\[/g, ")\\n  [");
      text = text.replace(/\\), /g, "),\\n  ");
      text = text.replace(/, ∀ /g, ",\\n  ∀ ");
      text = text.replace(/, \\(/g, ",\\n  (");
      text = text.replace(/, ([A-Za-z_][A-Za-z0-9_']* : Type u_[0-9]+)/g, ",\\n  $1");
      text = text.replace(/, ([A-Za-z_][A-Za-z0-9_']* : Type\\*)/g, ",\\n  $1");
      text = text.replace(/, (\\[[^\\]]+\\] : [^,]+)/g, ",\\n  $1");
      text = text.replace(/ → /g, "\\n    → ");
      text = text.replace(/ ↔ /g, "\\n    ↔ ");
      text = text.replace(/ ∧ /g, "\\n    ∧ ");
      text = text.replace(/\\) \\(/g, ")\\n  (");
      return wrapLeanLines(prettyLeanIdentifiers(text));
    }

    function compactPreview(value, maxLength = 150) {
      const text = normalizeStatement(value || "");
      if (!text) {
        return "No statement text.";
      }
      if (text.length <= maxLength) {
        return text;
      }
      return `${text.slice(0, maxLength - 1)}…`;
    }

    function makeStatementBox(label, value, options = {}) {
      const details = document.createElement("details");
      details.className = "statement-box";
      if (options.open) {
        details.open = true;
      }
      const summary = document.createElement("summary");
      summary.textContent = label;
      const preview = document.createElement("span");
      preview.className = "statement-preview";
      preview.textContent = compactPreview(value, options.previewLength || 150);
      summary.appendChild(preview);
      const body = document.createElement("div");
      body.className = "statement-body";
      if (options.html) {
        body.innerHTML = options.html;
      } else {
        body.textContent = value || "No statement text.";
      }
      details.appendChild(summary);
      details.appendChild(body);
      return details;
    }

    function typesetMath() {
      if (typeof window.MathJax === "undefined") {
        return;
      }
      if (window.MathJax.typesetPromise) {
        window.MathJax.typesetPromise().catch(() => {});
        return;
      }
      if (window.MathJax.Hub && window.MathJax.Hub.Queue) {
        window.MathJax.Hub.Queue(["Typeset", window.MathJax.Hub]);
      }
    }

    function findCurrentItem(paper, theorem) {
      for (const p of state.papers) {
        if (p.name !== paper) continue;
        for (const item of p.items) {
          if (item.name === theorem) return item;
        }
      }
      return null;
    }

    function statusKey(paper, theorem) {
      return `${paper}::${theorem}`;
    }

    function allItemsCount() {
      return state.papers.reduce((acc, paper) => acc + paper.items.length, 0);
    }

    function sliceKey(paper, sliceId) {
      return `${paper}::${sliceId || "all"}`;
    }

    function populateSliceFilter() {
      const select = document.getElementById("sliceFilter");
      const current = select.value || "all";
      select.textContent = "";
      const allOption = document.createElement("option");
      allOption.value = "all";
      allOption.textContent = "All slices";
      select.appendChild(allOption);
      for (const paper of state.papers) {
        const slices = paper.slices || [];
        if (slices.length <= 1 && slices[0] && slices[0].id === "all") {
          continue;
        }
        for (const slice of slices) {
          const option = document.createElement("option");
          option.value = sliceKey(paper.name, slice.id);
          const count = typeof slice.count === "number" ? ` (${slice.count})` : "";
          option.textContent = `${paper.name}: ${slice.title}${count}`;
          select.appendChild(option);
        }
      }
      select.value = Array.from(select.options).some((option) => option.value === current)
        ? current
        : "all";
    }

    function buildStatusMap(rows) {
      const out = new Map();
      for (const row of rows || []) {
        out.set(statusKey(row.paper, row.theorem), row);
      }
      return out;
    }

    function statusFor(paper, theorem) {
      return buildStatusMap(state.statusRows).get(statusKey(paper, theorem)) || null;
    }

    function statusLabel(row) {
      if (!row || !row.has_review) {
        return "Unreviewed";
      }
      if (row.lean_stale || row.paper_stale) {
        return "Stale";
      }
      if (row.latest_matches === false) {
        return "Mismatch";
      }
      return "Reviewed";
    }

    function statusClass(row) {
      const label = statusLabel(row);
      if (label === "Reviewed") {
        return "ok";
      }
      if (label === "Mismatch") {
        return "bad";
      }
      if (label === "Stale") {
        return "warn";
      }
      return "";
    }

    function staleReason(row) {
      if (!row) {
        return "";
      }
      const reasons = [];
      if (row.lean_stale) reasons.push("Lean changed");
      if (row.paper_stale) reasons.push("paper text changed");
      return reasons.join(", ");
    }

    function isOutdated(entry, paper, theorem) {
      const current = findCurrentItem(paper, theorem);
      if (!current) {
        return false;
      }
      const reviewed = normalizeStatement(entry.lean_statement || "");
      const currentLean = normalizeStatement(current.lean_statement || "");
      const reviewedPaper = normalizeStatement(entry.paper_statement || "");
      const currentPaper = normalizeStatement(current.paper_statement || "");
      const leanOutdated = reviewed && currentLean && reviewed !== currentLean;
      const paperOutdated = reviewedPaper && currentPaper && reviewedPaper !== currentPaper;
      return leanOutdated || paperOutdated;
    }

    function latestEntryForItem(entries, paper, theorem) {
      const related = entries.filter((entry) => entry.paper === paper && entry.theorem === theorem);
      if (!related.length) {
        return null;
      }
      byLatest(related);
      return related[0];
    }

    function sourceFileButtons(assets) {
      if (!assets || !Object.keys(assets).length) {
        return null;
      }
      const list = document.createElement("div");
      list.className = "source-actions";
      for (const key of ["pdf", "text"]) {
        const asset = assets[key];
        if (!asset || !asset.url || !asset.name) {
          continue;
        }
        const a = document.createElement("a");
        a.className = "source-link";
        a.href = asset.url;
        a.target = "_blank";
        a.rel = "noopener noreferrer";
        a.textContent = `${key === "pdf" ? "Open PDF" : "Open text"}: ${asset.name}`;
        list.appendChild(a);
      }
      return list;
    }

    function makeSourcePanel(paper) {
      const assets = paper.assets || {};
      const links = sourceFileButtons(assets);
      if (!links) {
        const empty = document.createElement("div");
        empty.style.display = "none";
        return empty;
      }
      const panel = document.createElement("section");
      panel.className = "paper-source-panel";

      const heading = document.createElement("h3");
      heading.className = "paper-source-heading";
      heading.textContent = "Paper source";
      panel.appendChild(heading);

      const hint = document.createElement("div");
      hint.className = "paper-source-subtle";
      hint.textContent = "Open source:";
      panel.appendChild(hint);
      panel.appendChild(links);
      return panel;
    }

    function refreshSummary(entries, statusRows) {
      const summary = document.getElementById("summary");
      if (!state.papers.length) {
        summary.textContent = "No theorem rows.";
        return;
      }

      const allItems = allItemsCount();
      let reviewed = 0;
      let stale = 0;
      let mismatch = 0;
      let needsAttention = 0;

      if (statusRows && statusRows.length) {
        reviewed = statusRows.filter((row) => row.has_review).length;
        stale = statusRows.filter((row) => row.lean_stale || row.paper_stale).length;
        mismatch = statusRows.filter((row) => row.has_review && row.latest_matches === false).length;
        needsAttention = statusRows.filter((row) => row.needs_attention || row.latest_matches === false).length;
      } else {
        for (const paper of state.papers) {
          for (const item of paper.items) {
            const latest = latestEntryForItem(entries, paper.name, item.name);
            if (!latest) {
              continue;
            }
            reviewed++;
            if (isOutdated(latest, paper.name, item.name)) {
              stale++;
            }
            if (latest.matches === false) {
              mismatch++;
            }
          }
        }
        const unreviewed = allItems - reviewed;
        needsAttention = stale + unreviewed + mismatch;
      }

      const unreviewed = allItems - reviewed;
      summary.textContent = `${reviewed}/${allItems} items reviewed · ${stale} stale snapshot · ${needsAttention} need action`;
      document.getElementById("cardReviewed").textContent = `${reviewed}/${allItems}`;
      document.getElementById("cardAttention").textContent = String(needsAttention);
      document.getElementById("cardStale").textContent = String(stale);
      document.getElementById("cardMismatch").textContent = String(mismatch);
    }

    function reviewHistory(entries, paper, theorem) {
      const related = entries.filter((entry) => entry.paper === paper && entry.theorem === theorem);
      if (!related.length) return "<div class='small muted'>No reviews yet.</div>";
      byLatest(related);
      const lines = [];
      for (const e of related.slice(0, 5)) {
        const cls = e.matches ? "ok" : "bad";
        const status = e.matches ? "matches" : "does not match";
        const outdated = isOutdated(e, paper, theorem);
        const outdatedMark = outdated
          ? " <span class='warn'>(statement snapshot is out of date)</span>"
          : "";
        const note = e.notes ? ` — ${escapeHtml(e.notes)}` : "";
        lines.push(
          `<div class='history-entry'><span class='small'><span class='${cls}'>${status}</span> by ${escapeHtml(e.user || "")} (${escapeHtml(e.timestamp || "")})${outdatedMark}${note}</span></div>`
        );
      }
      return `<div class='history'><div class='small'><strong>Latest checks</strong></div>${lines.join("")}</div>`;
    }

    function makeRow(paper, item) {
      const row = document.createElement("tr");
      row.dataset.paper = paper;
      row.dataset.theorem = item.name;
      row.dataset.kind = item.kind || "";
      row.dataset.sliceKey = sliceKey(paper, item.slice_id || "all");
      row.dataset.sliceId = item.slice_id || "all";
      row.dataset.sliceTitle = item.slice_title || "All statements";
      row.dataset.searchText = `${paper} ${item.kind || ""} ${item.name} ${item.paper_statement || ""} ${item.lean_statement || ""}`.toLowerCase();
      const itemCell = document.createElement("td");
      const itemShell = document.createElement("div");
      itemShell.className = "review-item";
      const mainCell = document.createElement("div");
      mainCell.className = "review-main";

      const paperCell = document.createElement("section");
      paperCell.className = "review-section col-paper";
      const paperHtml = renderPaperStatement(item.paper_statement);
      if (item.paper_statement_image_url) {
        const image = document.createElement("img");
        image.className = "paper-statement-image";
        image.src = item.paper_statement_image_url;
        image.alt = `Rendered source statement for ${paper}.${item.name}`;
        image.loading = "lazy";
        paperCell.appendChild(image);
        paperCell.appendChild(
          makeStatementBox("Extracted text fallback", item.paper_statement || "", {
            html: paperHtml,
            previewLength: 160,
          })
        );
      } else if ((item.paper_statement || "").length > 650) {
        paperCell.appendChild(
          makeStatementBox("Paper source statement", item.paper_statement, {
            html: paperHtml,
            previewLength: 180,
          })
        );
      } else {
        paperCell.innerHTML = paperHtml;
      }

      const leanCell = document.createElement("section");
      leanCell.className = "review-section col-lean";
      leanCell.appendChild(
        makeStatementBox("Expanded Lean statement", item.lean_statement, {
          html: `<code>${escapeHtml(prettyLeanStatement(item.lean_statement))}</code>`,
          previewLength: 170,
          open: true,
        })
      );

      const agentCell = document.createElement("section");
      agentCell.className = "review-section col-agent agent-column";
      const agentHeader = document.createElement("div");
      agentHeader.className = "small muted";
      agentHeader.textContent =
        "Context-free Lean-to-TeX draft";
      const agentText = document.createElement("div");
      agentText.className = "agent-statement";
      agentText.appendChild(
        makeStatementBox("Lean-to-TeX draft", item.agent_statement || "", {
          html: renderTexDraft(item.agent_statement || ""),
          previewLength: 130,
          open: true,
        })
      );
      agentText.style.margin = "0";
      agentCell.appendChild(agentHeader);
      agentCell.appendChild(agentText);

      const reviewCell = document.createElement("aside");
      reviewCell.className = "review-controls col-review";
      const rowId = `${safeId(paper)}_${safeId(item.name)}`;

      const statusLine = document.createElement("div");
      statusLine.className = "status-line";
      const statusBadge = document.createElement("span");
      statusBadge.className = "status-pill";
      statusBadge.id = `status-${rowId}`;
      statusBadge.textContent = "Unreviewed";
      const staleBadge = document.createElement("span");
      staleBadge.className = "status-pill warn";
      staleBadge.id = `stale-${rowId}`;
      staleBadge.style.display = "none";
      statusLine.appendChild(statusBadge);
      statusLine.appendChild(staleBadge);

      const label = document.createElement("label");
      const checkbox = document.createElement("input");
      checkbox.type = "checkbox";
      checkbox.dataset.paper = paper;
      checkbox.dataset.theorem = item.name;
      checkbox.id = `match-${rowId}`;
      label.appendChild(checkbox);
      label.appendChild(document.createTextNode(" matches paper statement"));
      label.className = "small";

      const text = document.createElement("textarea");
      text.className = "row-note";
      text.placeholder = "Reviewer notes";
      text.dataset.paper = paper;
      text.dataset.theorem = item.name;
      text.id = `note-${rowId}`;

      const btn = document.createElement("button");
      btn.className = "btn";
      btn.type = "button";
      btn.textContent = "Save review";
      const saveStatus = document.createElement("span");
      saveStatus.className = "save-status small muted";
      btn.addEventListener("click", async () => {
        const user = document.getElementById("userHandle").value.trim() || state.user;
        const payload = {
          paper: paper,
          theorem: item.name,
          user: user,
          matches: checkbox.checked,
          notes: text.value.trim(),
          lean_statement: item.lean_statement,
          paper_statement: item.paper_statement,
          agent_statement: item.agent_statement,
        };
        btn.disabled = true;
        btn.textContent = "Saving...";
        saveStatus.textContent = "";
        try {
          const response = await fetch("/api/reviews", {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify(payload),
          });
          const data = await response.json();
          if (!response.ok) {
            saveStatus.textContent = data.error || "Failed to save.";
            saveStatus.className = "save-status small bad";
            return;
          }
          saveStatus.textContent = "Saved";
          saveStatus.className = "save-status small ok";
          await refreshReviews();
        } catch (_err) {
          saveStatus.textContent = "Save failed";
          saveStatus.className = "save-status small bad";
        } finally {
          btn.disabled = false;
          btn.textContent = "Save review";
        }
      });

      const status = document.createElement("div");
      status.className = "history";
      status.dataset.paper = paper;
      status.dataset.theorem = item.name;

      const header = document.createElement("div");
      header.className = "paper-title";
      header.textContent = `${item.kind} ${item.name}`;
      const sliceMeta = document.createElement("div");
      sliceMeta.className = "slice-meta";
      const lineText = item.line_number ? `line ${item.line_number}` : "line unavailable";
      sliceMeta.textContent = `${item.slice_title || "All statements"} · ${lineText}`;

      reviewCell.appendChild(header);
      reviewCell.appendChild(sliceMeta);
      reviewCell.appendChild(statusLine);
      reviewCell.appendChild(label);
      reviewCell.appendChild(text);
      reviewCell.appendChild(document.createElement("br"));
      reviewCell.appendChild(btn);
      reviewCell.appendChild(saveStatus);
      reviewCell.appendChild(status);

      // Populate with existing review history
      mainCell.appendChild(paperCell);
      mainCell.appendChild(leanCell);
      mainCell.appendChild(agentCell);
      itemShell.appendChild(mainCell);
      itemShell.appendChild(reviewCell);
      itemCell.appendChild(itemShell);
      row.appendChild(itemCell);
      return { row, status };
    }

    function updateStatusBadges() {
      for (const row of document.querySelectorAll("tr[data-paper][data-theorem]")) {
        const paper = row.dataset.paper;
        const theorem = row.dataset.theorem;
        const rowStatus = statusFor(paper, theorem);
        const rowId = `${safeId(paper)}_${safeId(theorem)}`;
        const badge = document.getElementById(`status-${rowId}`);
        const stale = document.getElementById(`stale-${rowId}`);
        const label = statusLabel(rowStatus);
        row.dataset.status = label.toLowerCase();
        row.dataset.needsAttention = rowStatus && rowStatus.needs_attention ? "true" : "false";
        row.dataset.latestMatches = rowStatus && rowStatus.latest_matches === false ? "false" : "true";
        row.dataset.hasReview = rowStatus && rowStatus.has_review ? "true" : "false";
        row.dataset.isStale = rowStatus && (rowStatus.lean_stale || rowStatus.paper_stale) ? "true" : "false";
        if (badge) {
          badge.textContent = label;
          badge.className = `status-pill ${statusClass(rowStatus)}`.trim();
        }
        if (stale) {
          const reason = staleReason(rowStatus);
          stale.textContent = reason;
          stale.style.display = reason ? "" : "none";
        }
      }
    }

    function updatePaperProgress() {
      const statusRows = state.statusRows || [];
      for (const paper of state.papers) {
        const paperRows = statusRows.filter((row) => row.paper === paper.name);
        const total = paper.items.length;
        const reviewed = paperRows.filter((row) => row.has_review).length;
        const attention = paperRows.filter((row) => row.needs_attention || row.latest_matches === false).length;
        const node = document.querySelector(`[data-paper-progress="${paper.name}"]`);
        if (node) {
          node.textContent = `${reviewed}/${total} reviewed; ${attention} need action`;
        }
      }
    }

    function applyFilters() {
      const query = (document.getElementById("searchBox").value || "").trim().toLowerCase();
      const statusFilter = document.getElementById("statusFilter").value;
      const sliceFilter = document.getElementById("sliceFilter").value || "all";
      let visibleRows = 0;
      for (const block of document.querySelectorAll(".paper-block")) {
        let visibleInBlock = 0;
        for (const row of block.querySelectorAll("tr[data-paper][data-theorem]")) {
          const matchesSearch = !query || (row.dataset.searchText || "").includes(query);
          const matchesSlice = sliceFilter === "all" || row.dataset.sliceKey === sliceFilter;
          let matchesStatus = true;
          if (statusFilter === "attention") {
            matchesStatus = row.dataset.needsAttention === "true" || row.dataset.latestMatches === "false";
          } else if (statusFilter === "unreviewed") {
            matchesStatus = row.dataset.hasReview !== "true";
          } else if (statusFilter === "stale") {
            matchesStatus = row.dataset.isStale === "true";
          } else if (statusFilter === "mismatch") {
            matchesStatus = row.dataset.latestMatches === "false";
          } else if (statusFilter === "reviewed") {
            matchesStatus = row.dataset.hasReview === "true";
          }
          const visible = matchesSearch && matchesSlice && matchesStatus;
          row.classList.toggle("is-hidden", !visible);
          if (visible) {
            visibleInBlock++;
            visibleRows++;
          }
        }
        block.style.display = visibleInBlock ? "" : "none";
      }
      document.getElementById("emptyFilter").style.display = visibleRows ? "none" : "block";
    }

    async function refreshReviews() {
      let entries = [];
      let statusRows = [];
      try {
        const [reviewResponse, statusResponse] = await Promise.all([
          fetch("/api/reviews"),
          fetch("/api/status"),
        ]);
        if (reviewResponse.ok) {
          const payload = await reviewResponse.json();
          entries = payload.reviews || [];
        }
        if (statusResponse.ok) {
          const statusPayload = await statusResponse.json();
          statusRows = statusPayload.status || [];
        }
      } catch (_err) {
        entries = state.reviews || [];
        statusRows = state.statusRows || [];
      }
      state.reviews = entries;
      state.statusRows = statusRows;
      refreshSummary(entries, statusRows);
      const total = entries.length;
      document.getElementById("count").textContent = `Reviews logged: ${total}`;
      updateStatusBadges();
      updatePaperProgress();

      const statusNodes = document.querySelectorAll(".history[data-paper][data-theorem]");
      for (const node of statusNodes) {
        const theorem = node.dataset.theorem;
        const paper = node.dataset.paper;
        node.innerHTML = reviewHistory(entries, paper, theorem);
        // Prefill for current user if there is a latest entry
        const user = document.getElementById("userHandle").value.trim() || state.user;
        const mine = entries.filter(
          (entry) => entry.paper === paper && entry.theorem === theorem && entry.user === user
        );
        if (mine.length) {
          mine.sort((a, b) => (a.timestamp < b.timestamp ? 1 : -1));
          const latest = mine[0];
          const rowId = `${safeId(paper)}_${safeId(theorem)}`;
          const cb = document.getElementById(`match-${rowId}`);
          const ta = document.getElementById(`note-${rowId}`);
          if (cb) {
            cb.checked = !!latest.matches;
          }
          if (ta) {
            ta.value = latest.notes || "";
          }
        }
      }
      applyFilters();
    }

    function render() {
      const container = document.getElementById("containers");
      document.getElementById("logPath").textContent = `Log file: ${state.logPath}`;
      container.textContent = "";
      const data = state.papers;
      if (!data.length) {
        container.textContent = "No paper interfaces found.";
        return;
      }
      populateSliceFilter();
      for (const paper of data) {
        const block = document.createElement("details");
        block.className = "paper-block";
        block.open = data.length === 1 || paper.items.length <= 80;
        block.classList.add("paper-details");
        const summary = document.createElement("summary");
        const header = document.createElement("div");
        header.className = "paper-header";
        const heading = document.createElement("h2");
        heading.textContent = `${paper.name} — ${paper.title}`;
        const progress = document.createElement("div");
        progress.className = "paper-progress";
        progress.dataset.paperProgress = paper.name;
        progress.textContent = `0/${paper.items.length} reviewed; ${paper.items.length} rows`;
        header.appendChild(heading);
        header.appendChild(progress);
        summary.appendChild(header);
        block.appendChild(summary);
        block.appendChild(makeSourcePanel(paper));
        const table = document.createElement("table");
        const head = document.createElement("thead");
        head.innerHTML =
          "<tr><th>Paper statement, expanded Lean statement, and review</th></tr>";
        table.appendChild(head);
        const body = document.createElement("tbody");
        for (const item of paper.items) {
          const rowInfo = makeRow(paper.name, item);
          body.appendChild(rowInfo.row);
        }
        table.appendChild(body);
        const tableWrap = document.createElement("div");
        tableWrap.className = "table-wrap";
        tableWrap.appendChild(table);
        block.appendChild(tableWrap);
        container.appendChild(block);
      }
      refreshReviews();
      typesetMath();
    }

    document.getElementById("userHandle").addEventListener("change", refreshReviews);
    document.getElementById("searchBox").addEventListener("input", applyFilters);
    document.getElementById("statusFilter").addEventListener("change", applyFilters);
    document.getElementById("sliceFilter").addEventListener("change", applyFilters);
    document.getElementById("hideAgentDraft").addEventListener("change", (event) => {
      document.body.classList.toggle("hide-agent", event.target.checked);
    });
    const mathjaxTag = document.getElementById("mathjax-script");
    if (mathjaxTag) {
      mathjaxTag.addEventListener("load", typesetMath);
    }
    document.addEventListener("DOMContentLoaded", render);
  </script>
</body>
</html>
""".strip()


def render_static_html(papers: list[dict[str, Any]], user: str, log_path: str) -> str:
    payload = json.dumps(papers)
    return (
        HTML_PAGE.replace("__USER__", json.dumps(user))
        .replace("__LOG_PATH__", json.dumps(log_path))
        .replace("__PAPERS__", payload)
        .replace("{user}", html.escape(user, quote=True))
    )


def stale_review_summary(
    paper: str | None, log_file: Path | None, slice_filter: str | None = None
) -> dict[str, list[dict[str, Any]] | dict[str, Any]]:
    """Return stale/unreviewed buckets plus overall status for quick checks."""

    papers = gather_paper_data(paper, slice_filter)
    if log_file is not None:
        reviews = read_log_entries(log_file, paper)
    elif paper:
        reviews = read_all_log_entries(paper, None)
    else:
        reviews = read_all_log_entries(None, None)
    rows = build_review_status(papers, reviews)
    buckets = stale_review_rows(rows)
    return {
        "rows": rows,
        "totals": status_totals(rows),
        "stale": buckets["stale"],
        "unreviewed": buckets["unreviewed"],
        "mismatch": buckets["mismatch"],
    }


def print_stale_review_warning(
    paper: str | None, log_file: Path | None, slice_filter: str | None = None
) -> bool:
    """Print a lightweight launch-time check summary and return whether stale data exists."""

    summary = stale_review_summary(paper, log_file, slice_filter)
    stale_rows = summary["stale"]
    unreviewed_rows = summary["unreviewed"]
    mismatch_rows = summary["mismatch"]
    totals = summary["totals"]
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    total_items = int(totals.get("total_items") or 0)
    reviewed_items = int(totals.get("reviewed_items") or 0)
    needs_attention = int(totals.get("needs_attention_items") or 0)
    print(
        f"Review status for {label}: {reviewed_items}/{total_items} reviewed, "
        f"{needs_attention} need attention ({len(stale_rows)} stale, "
        f"{len(unreviewed_rows)} unreviewed, {len(mismatch_rows)} mismatch)."
    )

    if not stale_rows:
        if not unreviewed_rows and not mismatch_rows:
            print(f"Review checks for {label} are currently up to date.")
            return False
        else:
            print(
                f"Review checks for {label}: no stale checks, but "
                f"{len(unreviewed_rows)} item(s) have no review entry yet and "
                f"{len(mismatch_rows)} item(s) are marked as not matching."
            )
            return True

    print(f"\nReview check: found {len(stale_rows)} stale check(s) in {label}.")
    print("The dashboard loads current Lean/Paper statements on launch, but these")
    print("previously logged entries were checked against an earlier interface snapshot:")
    for row in stale_rows[:12]:
        reasons = []
        if row.get("lean_stale"):
            reasons.append("Lean signature changed")
        if row.get("paper_stale"):
            reasons.append("paper-facing text changed")
        print(
            f" - {row['paper']}.{row['theorem']} "
            f"({' / '.join(reasons) if reasons else 'statement changed'})"
        )
    if len(stale_rows) > 12:
        print(f" - ... {len(stale_rows) - 12} more")
    if unreviewed_rows:
        print(f"{len(unreviewed_rows)} additional item(s) currently need an initial review.")
    if mismatch_rows:
        print(f"{len(mismatch_rows)} additional reviewed item(s) are marked as not matching.")
    print("Open the dashboard and resave checks for these items to refresh the trace.")
    print("The agent Lean drafts are regenerated from the current declarations automatically.")
    return True


class ReusableThreadingHTTPServer(ThreadingHTTPServer):
    allow_reuse_address = True


class ReviewHTTPHandler(BaseHTTPRequestHandler):
    papers: list[dict[str, Any]] = []
    log_file: Path | None = None
    default_user: str = getpass.getuser()
    paper_filter: str | None = None
    slice_filter: str | None = None

    def log_message(self, *_args: Any) -> None:  # silence noisy HTTP logs
        return

    def _json_response(self, status: int, payload: dict[str, Any]) -> None:
        data = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _collect_path(self) -> tuple[str, dict[str, str]]:
        parsed = urllib.parse.urlsplit(self.path)
        query = urllib.parse.parse_qs(parsed.query)
        clean_query = {k: v[0] for k, v in query.items()}
        return parsed.path, clean_query

    def _send_file(self, path: Path) -> None:
        """Serve a single local file."""

        data = path.read_bytes()
        content_type, _ = mimetypes.guess_type(str(path))
        if path.suffix.lower() == ".txt":
            content_type = "text/plain; charset=utf-8"
        self.send_response(200)
        self.send_header("Content-Type", content_type or "application/octet-stream")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Content-Disposition", "inline")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(data)

    def _send_asset(self, paper: str, filename: str) -> None:
        """Serve a validated paper asset if it belongs to the selected paper."""

        target_paper_dir = None
        for folder in iter_paper_folders(self.paper_filter):
            if folder.name == paper:
                target_paper_dir = folder
                break
        if target_paper_dir is None:
            self.send_error(404, "paper not found")
            return
        if not filename or "/" in filename or "\\" in filename or ".." in filename:
            self.send_error(404, "invalid asset")
            return
        if not filename.lower().endswith(tuple(PAPER_ASSET_EXTENSIONS)):
            self.send_error(404, "unsupported paper asset")
            return
        candidate = target_paper_dir / filename
        if not candidate.exists() or not candidate.is_file():
            self.send_error(404, "asset not found")
            return
        self._send_file(candidate)

    def _send_rendered_statement(self, paper: str, filename: str) -> None:
        """Serve a generated statement-render PNG if it belongs to the paper cache."""

        target_paper_dir = None
        for folder in iter_paper_folders(self.paper_filter):
            if folder.name == paper:
                target_paper_dir = folder
                break
        if target_paper_dir is None:
            self.send_error(404, "paper not found")
            return
        if not filename or "/" in filename or "\\" in filename or ".." in filename:
            self.send_error(404, "invalid rendered statement")
            return
        if not filename.lower().endswith(tuple(PAPER_RENDERED_IMAGE_EXTENSIONS)):
            self.send_error(404, "unsupported rendered statement")
            return
        candidate = target_paper_dir / ".review_traces" / PAPER_RENDERED_STATEMENT_DIR / filename
        if not candidate.exists() or not candidate.is_file():
            self.send_error(404, "rendered statement not found")
            return
        self._send_file(candidate)

    def do_GET(self) -> None:
        path, query = self._collect_path()
        if path == "/":
            papers = gather_paper_data(self.paper_filter, self.slice_filter)
            html = render_static_html(
                papers,
                self.default_user,
                describe_log_target(self.log_file, self.paper_filter),
            )
            body = html.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if path.startswith("/paper-assets/"):
            pieces = [segment for segment in path.split("/") if segment]
            if len(pieces) != 3:
                self.send_error(404, "invalid asset request")
                return
            paper = urllib.parse.unquote(pieces[1])
            filename = urllib.parse.unquote(pieces[2])
            self._send_asset(paper, filename)
            return
        if path.startswith("/rendered-statements/"):
            pieces = [segment for segment in path.split("/") if segment]
            if len(pieces) != 3:
                self.send_error(404, "invalid rendered statement request")
                return
            paper = urllib.parse.unquote(pieces[1])
            filename = urllib.parse.unquote(pieces[2])
            self._send_rendered_statement(paper, filename)
            return
        if path == "/api/papers":
            papers = gather_paper_data(self.paper_filter, self.slice_filter)
            self._json_response(200, {"papers": papers})
            return
        if path == "/api/reviews":
            paper = query.get("paper")
            if paper and self.log_file is None:
                try:
                    reviews = read_log_entries(paper_review_log_file(paper))
                except ValueError:
                    reviews = []
            elif paper:
                reviews = read_log_entries(self.log_file, paper)
            else:
                reviews = read_all_log_entries(self.paper_filter, self.log_file)
            self._json_response(200, {"reviews": reviews})
            return
        if path == "/api/status":
            requested_paper = query.get("paper")
            user_filter = query.get("user")
            stale_only = parse_bool_flag(query.get("stale_only"))
            papers = gather_paper_data(requested_paper or self.paper_filter, self.slice_filter)
            if self.log_file is not None:
                if requested_paper:
                    reviews = read_log_entries(self.log_file, requested_paper)
                else:
                    reviews = read_log_entries(self.log_file)
            elif requested_paper:
                try:
                    reviews = read_log_entries(paper_review_log_file(requested_paper))
                except ValueError:
                    reviews = []
            else:
                reviews = read_all_log_entries(self.paper_filter, None)
            rows = build_review_status(papers, reviews)
            rows = filter_review_rows(rows, user_filter=user_filter, stale_only=stale_only)
            self._json_response(200, {"status": rows, "totals": status_totals(rows)})
            return
        self.send_error(404, "not found")

    def do_POST(self) -> None:
        path, _ = self._collect_path()
        if path != "/api/reviews":
            self.send_error(404, "not found")
            return
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length).decode("utf-8")
        try:
            payload = json.loads(raw or "{}")
        except json.JSONDecodeError:
            self._json_response(400, {"error": "invalid json body"})
            return
        try:
            paper_name = str(payload.get("paper") or "").strip()
            if self.log_file is None:
                log_file = paper_review_log_file(paper_name)
            else:
                log_file = self.log_file
            entry = append_review(log_file, payload, self.default_user)
        except Exception as exc:  # noqa: BLE001 - user input surface
            self._json_response(400, {"error": str(exc)})
            return
        self._json_response(200, {"entry": entry})


def main() -> None:
    parser = argparse.ArgumentParser(description="Review dashboard for paper interface statements.")
    parser.add_argument("--paper", help="Optional paper folder name to limit the dashboard.")
    parser.add_argument(
        "--slice",
        dest="slice_filter",
        default="",
        help="Optional review slice id, or PAPER::slice id, to limit dashboard rows.",
    )
    parser.add_argument(
        "--log-file",
        default="",
        help="Optional single JSONL trace path that overrides per-paper storage.",
    )
    parser.add_argument(
        "--user",
        default="",
        help="Reviewer handle (fallback used in saved entries).",
    )
    parser.add_argument(
        "--user-var",
        action="append",
        dest="user_vars",
        help="Environment variable(s) to check for default username (default GitHub variables).",
    )
    parser.add_argument(
        "--export-format",
        choices=("json", "csv", "md"),
        help="Generate a review status export instead of static HTML when not in server mode.",
    )
    parser.add_argument("--export-file", default="", help="Optional path for exported report output.")
    parser.add_argument("--status-user", default="", help="Filter status rows by reviewer handle.")
    parser.add_argument(
        "--stale-only",
        action="store_true",
        help="Filter status export to rows that need attention.",
    )
    parser.add_argument(
        "--precheck",
        action="store_true",
        help="Print stale review diagnostics for the selected paper and exit.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Like --precheck, but return non-zero if any item needs review or is stale.",
    )
    parser.add_argument(
        "--refresh-cache",
        action="store_true",
        help="Regenerate cached paper-interface rows and exit.",
    )
    parser.add_argument("--serve", action="store_true", help="Start a local review web server.")
    parser.add_argument("--host", default="127.0.0.1", help="Server host when --serve is set.")
    parser.add_argument("--port", type=int, default=8765, help="Server port when --serve is set.")
    args = parser.parse_args()

    if args.user_vars is None:
        args.user_vars = DEFAULT_USER_ENV_VARS.copy()
    user = detect_reviewer_username(args.user, args.user_vars)

    log_file = Path(args.log_file) if args.log_file else None

    if args.precheck or args.check:
        has_attention = print_stale_review_warning(args.paper, log_file, args.slice_filter)
        if args.check and has_attention:
            sys.exit(1)
        return

    if args.refresh_cache:
        papers = iter_paper_folders(args.paper)
        if not papers:
            if args.paper:
                raise SystemExit(
                    f"no canonical human-review PaperInterface.lean found for paper '{args.paper}'"
                )
            raise SystemExit("no papers with canonical human-review PaperInterface.lean found")
        for folder in papers:
            refresh_cached_review_rows(folder)
            print(f"refreshed dashboard cache for {folder.name}")
        return

    if args.serve:
        handler = ReviewHTTPHandler
        handler.papers = gather_paper_data(args.paper, args.slice_filter)
        handler.log_file = log_file
        handler.default_user = user
        handler.paper_filter = args.paper
        handler.slice_filter = args.slice_filter
        print_stale_review_warning(args.paper, log_file, args.slice_filter)
        try:
            server = ReusableThreadingHTTPServer((args.host, args.port), handler)
        except OSError as exc:
            print(
                f"Failed to start dashboard server on {args.host}:{args.port}: {exc}"
            )
            if args.host == "0.0.0.0":
                print(
                    "Hint: in WSL2, you may retry with --host 127.0.0.1 or use "
                    "localhost in Windows."
                )
            else:
                print(
                    "Hint: check if another process is already using this port, "
                    "or try a different --port value."
                )
            sys.exit(1)
        print(f"Review dashboard: http://{args.host}:{args.port}/")
        print(f"Log target: {describe_log_target(log_file, args.paper)}")
        print("Press Ctrl-C to stop.")
        server.serve_forever()

    if args.export_format:
        papers = gather_paper_data(args.paper, args.slice_filter)
        if log_file is not None:
            if args.paper:
                reviews = read_log_entries(log_file, args.paper)
            else:
                reviews = read_log_entries(log_file)
        elif args.paper:
            reviews = read_all_log_entries(args.paper, None)
        else:
            reviews = read_all_log_entries(None, None)
        rows = build_review_status(papers, reviews)
        rows = filter_review_rows(rows, user_filter=(args.status_user or "").strip() or None, stale_only=args.stale_only)
        if args.export_format == "json":
            payload = json.dumps(
                {"status": rows, "totals": status_totals(rows)},
                indent=2,
            )
        elif args.export_format == "csv":
            payload = render_csv_summary(rows)
        else:
            payload = render_markdown_summary(rows)
        if args.export_file:
            out = Path(args.export_file)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(payload, encoding="utf-8")
            print(f"Wrote report to {out}")
        else:
            if args.export_format == "json":
                print(payload)
            else:
                sys.stdout.write(payload)
        return

    else:
        papers = gather_paper_data(args.paper, args.slice_filter)
        html = render_static_html(papers, user, describe_log_target(log_file, args.paper))
        if log_file is not None:
            out = log_file.parent / "review_dashboard.html"
        elif args.paper:
            out = paper_review_log_file(args.paper).parent / "review_dashboard.html"
        else:
            out = ROOT / ".review_traces" / "review_dashboard.html"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(html, encoding="utf-8")
        print(f"Wrote dashboard HTML to {out}")
        print("Run with --serve to allow interactive saving to the local review log.")


if __name__ == "__main__":
    main()
