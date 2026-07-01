#!/usr/bin/env python3
"""Generate a Lean-backed recursive source-record audit payload.

This helper is intentionally conservative. It does not decide that a paper is
closed. It finds paper-facing rows that mention structure/source-model types,
recursively expands those structures' fields by source text, asks Lean to
`#check` the rows and field projections, and writes a JSON payload for the
LLM-as-judge pass.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any


DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b"
)
STRUCTURE_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:structure|class)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
TOP_LEVEL_RE = re.compile(
    r"^(?:@[^\n]*\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|opaque|constant|structure|class|inductive|"
    r"instance|namespace|section|end)\b"
)
FIELD_RE = re.compile(r"^\s{2,}([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(.*)$")
BINDER_RE = re.compile(r"[\(\{]([^()\{\}\[\]]+?)\s*:\s*([^()\{\}\[\]]+?)[\)\}]")
BOUNDARY_INPUT_RE = re.compile(
    r"(certificate|replay|process|bridge|trace|path|transfer|preservation|"
    r"source[_ -]?(?:row|rows|table|model|family)|"
    r"row[_ -]?package|oracle|external|boundary|assumption|hypothesis|premise|regularity|"
    r"witness|bounds?|package)",
    re.I,
)

STRUCTURE_NAME_RE = re.compile(
    r"(Record|Certificate|Semantics|Source|Model|Bridge|Package|Consequences|"
    r"Inputs|Carrier|Trace|Skeleton|Boundary|Witness|Data|Law|Functions|Kernel|"
    r"Replay|Process)$"
)
NON_SOURCE_RECORD_TYPE_NAMES = {
    # Enum/base carrier names that match STRUCTURE_NAME_RE by suffix but are not
    # source records with recursively auditable fields.
    "HasLaw",
    "VoterResponseModel",
}
RISK_TERMS = {
    "axiom",
    "bridge",
    "certificate",
    "conditions",
    "continuity",
    "continuous",
    "convergence",
    "convex",
    "directionalField",
    "equilibrium",
    "field",
    "formula",
    "gradient",
    "isMax",
    "maximizer",
    "median",
    "model",
    "optimal",
    "process",
    "projection",
    "response",
    "replay",
    "semantics",
    "source",
    "trace",
    "trajectory",
    "update",
}

SOURCE_RECORD_PROMPT_VERSION = "source-record-v2-semantic-boundary-inputs"


@dataclass
class FieldInfo:
    structure: str
    field: str
    type: str
    path: str
    line: int
    source_file: str
    nested_structures: list[str]
    risk_terms: list[str]


@dataclass
class StructureInfo:
    name: str
    source_file: str
    line: int
    fields: list[FieldInfo]


@dataclass
class RecursionFailure:
    kind: str
    structure: str
    path: str
    message: str


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def mask_block_comments(text: str) -> str:
    """Replace Lean block comments with spaces while preserving line numbers."""
    output: list[str] = []
    index = 0
    depth = 0
    while index < len(text):
        if text.startswith("/-", index):
            depth += 1
            output.extend("  ")
            index += 2
            continue
        if depth and text.startswith("-/", index):
            depth -= 1
            output.extend("  ")
            index += 2
            continue
        char = text[index]
        if depth:
            output.append("\n" if char == "\n" else " ")
        else:
            output.append(char)
        index += 1
    return "".join(output)


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def stable_digest(payload: object) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def binder_names(raw_names: str) -> list[str]:
    return [
        name
        for name in re.split(r"\s+", raw_names.strip())
        if name and name not in {"_", "inst"} and not name.startswith("[") and not name.endswith("]")
    ]


def declaration_header(declaration: str) -> str:
    """Return the declaration signature before the proof/body."""

    body_start = top_level_token_index(declaration, ":=")
    head = declaration[:body_start] if body_start is not None else declaration
    where_start = top_level_word_index(head, "where")
    if where_start is not None:
        head = head[:where_start]
    return head.strip()


def top_level_token_index(text: str, token: str) -> int | None:
    """Return the first top-level occurrence of `token`, ignoring binder interiors."""

    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in "([{⦃":
            depth += 1
            index += 1
            continue
        if char in ")]}⦄" and depth > 0:
            depth -= 1
            index += 1
            continue
        if depth == 0 and text.startswith(token, index):
            return index
        index += 1
    return None


def top_level_word_index(text: str, word: str) -> int | None:
    """Return the first top-level occurrence of a standalone Lean keyword."""

    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in "([{⦃":
            depth += 1
            index += 1
            continue
        if char in ")]}⦄" and depth > 0:
            depth -= 1
            index += 1
            continue
        if depth == 0 and text.startswith(word, index):
            before = text[index - 1] if index else " "
            after_index = index + len(word)
            after = text[after_index] if after_index < len(text) else " "
            if not (before.isalnum() or before == "_") and not (
                after.isalnum() or after == "_"
            ):
                return index
        index += 1
    return None


def split_top_level_colon(text: str) -> tuple[str, str] | None:
    depth = 0
    for index, char in enumerate(text):
        if char in "([{⦃":
            depth += 1
        elif char in ")]}⦄" and depth > 0:
            depth -= 1
        elif char == ":" and depth == 0:
            return text[:index].strip(), text[index + 1 :].strip()
    return None


def balanced_binder_spans(text: str) -> list[str]:
    """Return top-level Lean binder contents from a declaration header."""

    spans: list[str] = []
    pairs = {"(": ")", "{": "}", "[": "]"}
    index = 0
    while index < len(text):
        opener = text[index]
        closer = pairs.get(opener)
        if closer is None:
            index += 1
            continue
        depth = 1
        cursor = index + 1
        while cursor < len(text) and depth > 0:
            char = text[cursor]
            if char == opener:
                depth += 1
            elif char == closer:
                depth -= 1
            cursor += 1
        if depth == 0:
            spans.append(text[index + 1 : cursor - 1])
            index = cursor
        else:
            index += 1
    return spans


def visible_inputs_from_declaration(declaration: str) -> list[dict[str, str]]:
    """Best-effort visible binder extraction from a paper-facing declaration."""

    inputs: list[dict[str, str]] = []
    header = declaration_header(declaration)
    type_split = split_top_level_colon(header)
    binder_prefix = type_split[0] if type_split is not None else header
    for span in balanced_binder_spans(binder_prefix):
        split = split_top_level_colon(span)
        if split is None:
            continue
        raw_names, raw_type = split
        names = binder_names(raw_names)
        type_text = normalize_ws(raw_type)
        if not names or not type_text:
            continue
        inputs.append({"names": " ".join(names), "type": type_text})
    return inputs


def boundary_input_kind(row: str, visible_input: dict[str, str]) -> str:
    _ = row
    haystack = f"{visible_input.get('names', '')} {visible_input.get('type', '')}"
    if BOUNDARY_INPUT_RE.search(haystack):
        return "boundary_premise"
    return ""


def boundary_input_judgment_key(row: str, visible_input: dict[str, str]) -> str:
    names = normalize_ws(visible_input.get("names", ""))
    type_text = normalize_ws(visible_input.get("type", ""))
    return f"{row}.{names} : {type_text}"


def parse_status_rows(status_path: Path) -> list[str]:
    if not status_path.exists():
        return []
    payload = json.loads(read_text(status_path))
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return []
    names: list[str] = []
    for key in ("include_names", "assumption_names"):
        raw = review_surface.get(key)
        if isinstance(raw, list):
            names.extend(str(item) for item in raw if isinstance(item, str) and item.strip())
    return list(dict.fromkeys(names))


def parse_declarations(interface_path: Path) -> dict[str, str]:
    lines = mask_block_comments(read_text(interface_path)).splitlines()
    decls: dict[str, str] = {}
    index = 0
    while index < len(lines):
        match = DECL_RE.match(lines[index])
        if not match:
            index += 1
            continue
        name = match.group(2)
        start = index
        index += 1
        while index < len(lines) and not TOP_LEVEL_RE.match(lines[index]):
            index += 1
        decls[name] = "\n".join(lines[start:index]).strip()
    return decls


def first_declaration_namespace(interface_path: Path) -> str:
    """Return the namespace prefix active at the first paper-interface declaration."""

    namespace_stack: list[str] = []
    for line in mask_block_comments(read_text(interface_path)).splitlines():
        stripped = line.strip()
        if stripped.startswith("namespace "):
            raw = stripped.removeprefix("namespace ").strip()
            namespace_stack.extend(part for part in raw.split(".") if part)
            continue
        if stripped.startswith("end"):
            parts = stripped.split()
            if len(parts) == 1:
                if namespace_stack:
                    namespace_stack.pop()
            elif len(parts) == 2 and namespace_stack:
                end_parts = [part for part in parts[1].split(".") if part]
                if end_parts and namespace_stack[-len(end_parts) :] == end_parts:
                    del namespace_stack[-len(end_parts) :]
                else:
                    namespace_stack.pop()
            continue
        if DECL_RE.match(line):
            return ".".join(namespace_stack)
    return ""


def parse_structures(root: Path, lean_files: list[Path]) -> dict[str, StructureInfo]:
    structures: dict[str, StructureInfo] = {}
    for lean_file in lean_files:
        try:
            rel_file = str(lean_file.resolve().relative_to(root))
        except ValueError:
            rel_file = str(lean_file)
        lines = mask_block_comments(read_text(lean_file)).splitlines()
        index = 0
        while index < len(lines):
            match = STRUCTURE_RE.match(lines[index])
            if not match:
                index += 1
                continue
            name = match.group(1)
            start_line = index + 1
            index += 1
            fields: list[FieldInfo] = []
            current_name: str | None = None
            current_start_line = 0
            current_type_parts: list[str] = []

            def flush_current() -> None:
                nonlocal current_name, current_start_line, current_type_parts
                if current_name is None:
                    return
                field_type = normalize_ws(" ".join(current_type_parts))
                fields.append(
                    FieldInfo(
                        structure=name,
                        field=current_name,
                        type=field_type,
                        path=f"{name}.{current_name}",
                        line=current_start_line,
                        source_file=rel_file,
                        nested_structures=[],
                        risk_terms=[],
                    )
                )
                current_name = None
                current_start_line = 0
                current_type_parts = []

            while index < len(lines):
                line = lines[index]
                if TOP_LEVEL_RE.match(line):
                    break
                field_match = FIELD_RE.match(line)
                if field_match:
                    flush_current()
                    current_name = field_match.group(1)
                    current_start_line = index + 1
                    current_type_parts = [field_match.group(2).strip()]
                elif current_name is not None:
                    stripped = line.strip()
                    if stripped and not stripped.startswith("--"):
                        current_type_parts.append(stripped)
                index += 1
            flush_current()
            structures[name] = StructureInfo(name=name, source_file=rel_file, line=start_line, fields=fields)
    return structures


def source_model_structures(structures: dict[str, StructureInfo]) -> set[str]:
    return {name for name in structures if STRUCTURE_NAME_RE.search(name)}


def mentioned_structures(text: str, candidates: set[str]) -> list[str]:
    found = []
    for name in sorted(candidates, key=lambda item: (-len(item), item)):
        if re.search(rf"\b{re.escape(name)}\b", text):
            found.append(name)
    return found


def source_like_type_names(text: str) -> list[str]:
    """Return source-record-shaped type names mentioned in a field type."""

    names: set[str] = set()
    for match in re.finditer(r"\b[A-Z][A-Za-z0-9_']*(?:\.[A-Z][A-Za-z0-9_']*)*\b", text):
        base = match.group(0).split(".")[-1]
        if base in NON_SOURCE_RECORD_TYPE_NAMES:
            continue
        if STRUCTURE_NAME_RE.search(base):
            names.add(base)
    return sorted(names)


def field_risk_terms(field: FieldInfo) -> list[str]:
    haystack = f"{field.structure} {field.field} {field.type}"
    return sorted(term for term in RISK_TERMS if term in haystack)


def recursively_collect_fields(
    root_structure: str,
    structures: dict[str, StructureInfo],
    candidate_structures: set[str],
    max_depth: int,
) -> tuple[list[FieldInfo], list[RecursionFailure]]:
    collected: list[FieldInfo] = []
    failures: list[RecursionFailure] = []
    seen: set[tuple[str, str]] = set()
    expanded: set[str] = set()

    def walk(structure_name: str, prefix: list[str], stack: list[str], depth: int) -> None:
        if depth > max_depth:
            failures.append(
                RecursionFailure(
                    kind="max_depth",
                    structure=structure_name,
                    path=" -> ".join(prefix),
                    message=f"recursive source-record expansion exceeded max depth {max_depth}",
                )
            )
            return
        structure = structures.get(structure_name)
        if structure is None:
            failures.append(
                RecursionFailure(
                    kind="missing_structure",
                    structure=structure_name,
                    path=" -> ".join(prefix),
                    message="source-shaped nested structure was mentioned but not parsed from paper-local or selected library Lean files",
                )
            )
            return
        if not structure.fields:
            failures.append(
                RecursionFailure(
                    kind="empty_structure",
                    structure=structure_name,
                    path=" -> ".join(prefix),
                    message="source-shaped nested structure has no parsed fields, so recursion cannot reach primitive source assumptions",
                )
            )
            return
        if structure_name in expanded:
            return
        expanded.add(structure_name)
        for raw_field in structure.fields:
            nested = mentioned_structures(raw_field.type, candidate_structures)
            missing_nested = [
                name for name in source_like_type_names(raw_field.type)
                if name not in structures
            ]
            for missing in missing_nested:
                failures.append(
                    RecursionFailure(
                        kind="missing_nested_source_type",
                        structure=missing,
                        path=" -> ".join(prefix + [raw_field.path]),
                        message="field type mentions a source-shaped type that is not available as a parsed paper-local or selected library structure",
                    )
                )
            field = FieldInfo(
                structure=raw_field.structure,
                field=raw_field.field,
                type=raw_field.type,
                path=" -> ".join(prefix + [raw_field.path]),
                line=raw_field.line,
                source_file=raw_field.source_file,
                nested_structures=nested,
                risk_terms=field_risk_terms(raw_field),
            )
            key = (field.structure, field.field)
            if key not in seen:
                seen.add(key)
                collected.append(field)
            for nested_structure in nested:
                if nested_structure == structure_name:
                    continue
                if nested_structure in stack:
                    failures.append(
                        RecursionFailure(
                            kind="cycle",
                            structure=nested_structure,
                            path=" -> ".join(prefix + [raw_field.path, nested_structure]),
                            message="recursive source-record expansion found a cycle before reaching primitive source assumptions",
                        )
                    )
                    continue
                walk(nested_structure, prefix + [raw_field.path], stack + [nested_structure], depth + 1)

    walk(root_structure, [root_structure], [root_structure], 0)
    return collected, failures


def lean_check(
    root: Path,
    paper_id: str,
    row_namespace: str,
    row_names: list[str],
    assumption_row_names: set[str],
    qualified_row_refs: dict[str, str],
    fields: list[FieldInfo],
    max_output_chars: int,
) -> dict[str, Any]:
    if not row_names and not fields:
        return {
            "command": "skipped Lean check: no source-record rows or fields",
            "returncode": 0,
            "truncated": False,
            "output": "",
        }

    build_target = f"{paper_id}.PaperInterface"
    build_proc = subprocess.run(
        ["lake", "build", build_target],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if build_proc.returncode != 0:
        output = build_proc.stdout
        truncated = len(output) > max_output_chars
        if truncated:
            output = output[:max_output_chars] + "\n[truncated]\n"
        return {
            "command": f"lake build {build_target}",
            "returncode": build_proc.returncode,
            "truncated": truncated,
            "output": output,
        }

    lines = [f"import {paper_id}.PaperInterface", ""]
    if row_namespace:
        root_namespace = row_namespace.split(".")[0]
        lines.append(f"open {root_namespace}")
        lines.append("")

    def row_ref(name: str) -> str:
        qualified = qualified_row_refs.get(name)
        if qualified:
            return qualified
        return f"{row_namespace}.{name}" if row_namespace else name

    for name in row_names:
        lines.append(f"#check {row_ref(name)}")
        lines.append(f"#print axioms {row_ref(name)}")
    # Field declarations are parsed directly from Lean source.  Standalone
    # projection constants are brittle under namespace aliases even when the
    # paper-facing row elaborates dot projections successfully.
    script = "\n".join(lines) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", encoding="utf-8", delete=False) as handle:
        handle.write(script)
        script_path = Path(handle.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(script_path)],
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
    finally:
        try:
            script_path.unlink()
        except FileNotFoundError:
            pass
    output = proc.stdout
    truncated = len(output) > max_output_chars
    if truncated:
        output = output[:max_output_chars] + "\n[truncated]\n"
    return {
        "command": f"lake build {build_target} && lake env lean <generated-source-record-audit-script>",
        "returncode": proc.returncode,
        "truncated": truncated,
        "output": output,
    }


def judge_prompt(paper_id: str, items: list[dict[str, Any]]) -> str:
    return (
        "You are auditing Lean formalization provenance, not just theorem text.\n"
        f"Paper: {paper_id}\n\n"
        "For each item below, compare the original paper source statement/proof text "
        "with the Lean-checked statement and the dependency path. Scrutinize every "
        "visible theorem input semantically: names and source-looking type suffixes "
        "are only routing hints, not evidence. Do not approve by theorem label, "
        "phrase overlap, or source-looking Lean name. Each input must correspond "
        "to a specific paper primitive/source assumption, be derived by a "
        "Lean-checked constructor from paper primitives, be an approved external "
        "boundary, or remain an unresolved conditional/partial boundary. In "
        "particular, any Certificate, Replay, Process, or Bridge input needs a "
        "specific source statement or an instantiation path from the paper's "
        "primitive model; do not accept it merely because the final theorem name "
        "resembles the paper claim.\n\n"
        "Classify the item as "
        "one of: proved_from_primitives, validated_source_assumption, approved_external_boundary, "
        "container_recursively_audited, derived_consequence_record, "
        "nonpropositional_witness_data, or unresolved_assumed_math. Use "
        "container_recursively_audited only for a field whose type is another audited "
        "record/source/certificate and whose nested fields are separately judged; do not use "
        "it for a field whose type is a mathematical proposition or formula. Use "
        "derived_consequence_record only for fields of a theorem-output/consequence record "
        "whose constructor proof is separately checked and whose premise records are separately "
        "audited. Use nonpropositional_witness_data only for bare data witnesses "
        "(for example a chosen stream, cost function, gradient/noise/bias function, or "
        "projection function) whose type is not proposition-valued and does not itself state "
        "an equality, recurrence, optimality, measurability, convergence, continuity, or "
        "response/trajectory semantics. The proposition-valued fields that constrain that "
        "witness must still be classified separately. Mark "
        "unresolved_assumed_math if the Lean row merely "
        "takes a record/certificate/replay/process/bridge/source-model field that "
        "states convexity, response semantics, trace/replay validity, transfer "
        "preservation, trajectory generation, continuity, convergence, equilibrium, "
        "or a displayed formula that should be derived. Do not mark a field as "
        "proved just because Lean typechecks a projection from a structure premise.\n\n"
        + json.dumps(items, indent=2, sort_keys=True)
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper folder id, e.g. GKGMM19IterativeLocalVoting")
    parser.add_argument("--root", default=".", help="repository root containing papers/")
    parser.add_argument("--out", help="optional JSON output path")
    parser.add_argument("--no-lean", action="store_true", help="skip Lean #check subprocess")
    parser.add_argument("--max-depth", type=int, default=4, help="maximum recursive structure depth")
    parser.add_argument("--max-lean-output-chars", type=int, default=120000)
    args = parser.parse_args()

    root = Path(args.root).resolve()
    paper_dir = root / "papers" / args.paper
    interface_path = paper_dir / "PaperInterface.lean"
    status_path = paper_dir / "status.json"
    if not interface_path.exists():
        raise SystemExit(f"missing PaperInterface.lean at {interface_path}")

    row_namespace = first_declaration_namespace(interface_path)
    configured_rows = parse_status_rows(status_path)
    configured_row_set = set(configured_rows)
    declarations = parse_declarations(interface_path)
    qualified_row_refs: dict[str, str] = {}
    assumptions_path = paper_dir / "Assumptions.lean"
    if assumptions_path.exists():
        assumption_namespace = first_declaration_namespace(assumptions_path)
        for name, declaration in parse_declarations(assumptions_path).items():
            if name in configured_row_set or name.startswith(("assumption", "source_assumption")):
                declarations[name] = declaration
                if assumption_namespace:
                    qualified_row_refs[name] = f"{assumption_namespace}.{name}"
    configured_present = [name for name in configured_rows if name in declarations]
    configured_set = set(configured_present)
    unconfigured_rows = [name for name in sorted(declarations) if name not in configured_set]

    # The enforceable source-record lane is the curated paper-facing review
    # surface.  Keep unconfigured declarations visible in the payload so a
    # closeout audit can notice dashboard drift, but do not require source
    # provenance judgments for generic helper lemmas that are not presented as
    # paper claims.
    row_names = configured_present
    assumption_row_names: set[str] = set()
    if assumptions_path.exists():
        assumption_declarations = parse_declarations(assumptions_path)
        assumption_row_names = {
            name
            for name in row_names
            if name in assumption_declarations
        }

    lean_files = list(paper_dir.glob("*.lean"))
    poisson_library = root / "EconCSLib" / "Foundations" / "Probability" / "PoissonProcess.lean"
    if poisson_library.exists():
        lean_files.append(poisson_library)
    structures = parse_structures(root, sorted(set(lean_files)))
    candidate_structures = source_model_structures(structures)
    row_records: dict[str, list[str]] = {
        row: mentioned_structures(declarations[row], candidate_structures) for row in row_names
    }
    row_records = {row: records for row, records in row_records.items() if records}
    row_inputs: dict[str, list[dict[str, str]]] = {
        row: visible_inputs_from_declaration(declarations[row]) for row in row_names
    }

    recursive_fields: list[FieldInfo] = []
    recursion_failures: list[RecursionFailure] = []
    seen_fields: set[tuple[str, str]] = set()
    for records in row_records.values():
        for record in records:
            fields, failures = recursively_collect_fields(
                record, structures, candidate_structures, args.max_depth
            )
            recursion_failures.extend(failures)
            for field in fields:
                key = (field.structure, field.field)
                if key not in seen_fields:
                    seen_fields.add(key)
                    recursive_fields.append(field)

    semantic_row_items = [
        {
            "row": row,
            "visible_inputs": row_inputs.get(row, []),
            "record_premises": row_records.get(row, []),
            "lean_source_declaration": declarations[row],
            "required_check": "Every visible input must be semantically matched to the paper source "
            "model, not accepted by name. Every record/certificate/replay/process/bridge premise "
            "below must be recursively proved from primitives, validated as an explicit paper "
            "source assumption, approved as an external boundary, or marked unresolved proof debt.",
        }
        for row in row_names
        if row_inputs.get(row) or row_records.get(row)
    ]
    boundary_input_items = [
        {
            "row": row,
            "input": visible_input,
            "kind": kind,
            "judgment_key": boundary_input_judgment_key(row, visible_input),
            "lean_source_declaration": declarations[row],
            "required_check": "This visible theorem input is boundary-shaped. It needs a specific "
            "source statement/primitive or a Lean-checked constructor from paper primitives; "
            "the source-looking predicate name is not evidence.",
        }
        for row in row_names
        for visible_input in row_inputs.get(row, [])
        for kind in [boundary_input_kind(row, visible_input)]
        if kind
    ]
    judge_items = [
        item for item in semantic_row_items if item.get("record_premises")
    ]
    field_items = [
        {
            **asdict(field),
            "judgment_key": f"{field.structure}.{field.field}",
            "required_check": "Judge whether this field is proved from more primitive Lean facts or is "
            "an assumed source-model statement. If it carries paper math rather than a derived theorem, "
            "it is not a completed formalization item. If this field points to another record/source "
            "container, classify it as container_recursively_audited only after every nested field has "
            "its own approved judgment.",
        }
        for field in recursive_fields
    ]
    audit_surface = {
        "boundary_input_items": boundary_input_items,
        "rows_with_record_premises": judge_items,
        "rows_with_semantic_inputs": semantic_row_items,
        "row_visible_inputs": row_inputs,
        "recursive_field_items": field_items,
        "recursion_failures": [asdict(failure) for failure in recursion_failures],
    }

    payload: dict[str, Any] = {
        "paper": args.paper,
        "paper_dir": str(paper_dir),
        "import_module": f"{args.paper}.PaperInterface",
        "prompt_version": SOURCE_RECORD_PROMPT_VERSION,
        "source_record_audit_sha256": stable_digest(audit_surface),
        "source_record_judgment_file": "audit/source_record_match_llm.json",
        "expected_input_judgment_keys": sorted(
            {str(item["judgment_key"]) for item in boundary_input_items}
        ),
        "expected_field_judgment_keys": sorted(
            {str(item["judgment_key"]) for item in field_items}
        ),
        "review_row_count": len(row_names),
        "configured_review_row_count": len(configured_present),
        "unconfigured_paper_interface_rows": unconfigured_rows,
        "boundary_input_count": len(boundary_input_items),
        "boundary_input_items": boundary_input_items,
        "rows_with_record_premises": judge_items,
        "rows_with_semantic_inputs": semantic_row_items,
        "row_visible_inputs": row_inputs,
        "recursive_field_count": len(field_items),
        "recursive_field_items": field_items,
        "recursion_failure_count": len(recursion_failures),
        "recursion_failures": [asdict(failure) for failure in recursion_failures],
        "llm_judge_prompt": judge_prompt(args.paper, boundary_input_items + semantic_row_items + field_items),
    }
    if not args.no_lean:
        payload["lean_check"] = lean_check(
            root=root,
            paper_id=args.paper,
            row_namespace=row_namespace,
            row_names=[str(item["row"]) for item in semantic_row_items],
            assumption_row_names=assumption_row_names,
            qualified_row_refs=qualified_row_refs,
            fields=recursive_fields,
            max_output_chars=args.max_lean_output_chars,
        )

    encoded = json.dumps(payload, indent=2, sort_keys=True)
    if args.out:
        Path(args.out).write_text(encoded + "\n", encoding="utf-8")
    else:
        print(encoded)
    if payload.get("lean_check", {}).get("returncode", 0) != 0:
        return 2
    if recursion_failures:
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
