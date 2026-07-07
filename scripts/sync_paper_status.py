#!/usr/bin/env python3
"""Synchronize aggregate paper status from paper-local status JSON files."""

from __future__ import annotations

import argparse
import html
import json
import os
import subprocess
from pathlib import Path
from typing import Any

try:
    from root_readme_policy import assert_no_root_readme_outputs, assert_root_readme_locked
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports
    from scripts.root_readme_policy import assert_no_root_readme_outputs, assert_root_readme_locked


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
AGGREGATE_STATUS = PAPERS / "status.json"
HUMAN_STATUS = PAPERS / "human_status.json"
DOCS_PAPER_STATUS = ROOT / "docs" / "PAPER_STATUS.md"
SITE_INDEX = ROOT / "site" / "index.html"
TEMPLATE = PAPERS / "TEMPLATE"
SITE_LIBRARY_BEGIN = "<!-- BEGIN GENERATED LIBRARY COMPONENT ROWS -->"
SITE_LIBRARY_END = "<!-- END GENERATED LIBRARY COMPONENT ROWS -->"
SITE_STATS_BEGIN = "<!-- BEGIN GENERATED PROJECT STATS -->"
SITE_STATS_END = "<!-- END GENERATED PROJECT STATS -->"
SITE_STATUS_BEGIN = "<!-- BEGIN GENERATED PAPER STATUS ROWS -->"
SITE_STATUS_END = "<!-- END GENERATED PAPER STATUS ROWS -->"
SITE_REQUIRED_STATIC_COPY = {
    "maintainer footer": "EconCSLib is maintained by",
    "companion paper link": "https://arxiv.org/abs/2606.16144",
    "companion Lean project link": "https://github.com/gametheoryinlean/EconCSLib",
    "Slack workspace link": "https://join.slack.com/t/appliedmodelinglib/shared_invite/zt-42slirzxx-rEO8eEns7~4~i3Lbu7N~lA",
    "hero vision line": "Our vision is to enable researchers who don't know Lean",
}
PAPER_README_BEGIN = "<!-- BEGIN GENERATED PAPER FOLDER README -->"
PAPER_README_END = "<!-- END GENERATED PAPER FOLDER README -->"
LEGACY_README_NOTES = "docs/FORMALIZATION_NOTES.md"
GITHUB_MAIN = "https://github.com/nikhgarg/EconCSLib/blob/main/"
CATALOG = PAPERS / "catalog.json"

STATUS_LABELS = {
    "formalized": "Formalized",
    "formalized with caveat": "Formalized with caveat",
    "partially formalized": "Partially formalized",
    "conditional": "Partially formalized",
    "paper draft": "Paper draft",
    "scaffold": "Scaffold",
    "not started": "Not started",
    "not formalized": "Not formalized",
}

STATUS_GROUPS = {
    "formalized": 0,
    "formalized with caveat": 0,
    "partially formalized": 1,
    "conditional": 1,
    "paper draft": 2,
}

def load_catalog() -> dict[str, Any]:
    if not CATALOG.exists():
        return {}
    payload = json.loads(CATALOG.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{CATALOG.relative_to(ROOT)} should contain a JSON object")
    if payload.get("schema") != 1:
        raise ValueError(f"{CATALOG.relative_to(ROOT)} should use schema 1")
    return payload


def publication_overrides(catalog: dict[str, Any]) -> dict[str, tuple[str, int]]:
    raw = catalog.get("publication_overrides", {})
    if not isinstance(raw, dict):
        raise ValueError("publication_overrides should be an object")
    out: dict[str, tuple[str, int]] = {}
    for paper_id, value in raw.items():
        if not isinstance(value, dict):
            continue
        publication = value.get("publication")
        year = value.get("year")
        if isinstance(publication, str) and isinstance(year, int):
            out[str(paper_id)] = (publication, year)
    return out


def string_map(catalog: dict[str, Any], key: str) -> dict[str, str]:
    raw = catalog.get(key, {})
    if not isinstance(raw, dict):
        raise ValueError(f"{key} should be an object")
    return {
        str(name): value.strip()
        for name, value in raw.items()
        if isinstance(value, str) and value.strip()
    }


def library_components(catalog: dict[str, Any]) -> list[dict[str, Any]]:
    raw = catalog.get("library_components", [])
    if not isinstance(raw, list):
        raise ValueError("library_components should be a list")
    components: list[dict[str, Any]] = []
    for item in raw:
        if not isinstance(item, dict):
            continue
        title = item.get("title")
        examples = item.get("examples")
        raw_paths = item.get("paths", [])
        if not isinstance(title, str) or not isinstance(examples, str):
            continue
        if not isinstance(raw_paths, list):
            continue
        paths = [str(path) for path in raw_paths if str(path).strip()]
        components.append(
            {
                "title": title.strip(),
                "paths": paths,
                "examples": " ".join(examples.split()),
            }
        )
    return components


CATALOG_PAYLOAD = load_catalog()
PUBLICATION_OVERRIDES = publication_overrides(CATALOG_PAYLOAD)
SOURCE_URL_OVERRIDES = string_map(CATALOG_PAYLOAD, "source_url_overrides")
README_TITLE_OVERRIDES = string_map(CATALOG_PAYLOAD, "readme_title_overrides")
LIBRARY_COMPONENTS = library_components(CATALOG_PAYLOAD)


def note_citation(payload: dict[str, Any]) -> dict[str, str] | None:
    raw = payload.get("human_summary_citation")
    if not isinstance(raw, dict):
        return None
    label = raw.get("label")
    url = raw.get("url")
    if not isinstance(label, str) or not isinstance(url, str):
        return None
    label = label.strip()
    url = url.strip()
    if not label or not url:
        return None
    return {"label": label, "url": url}


def all_paper_dirs() -> list[Path]:
    return sorted(
        folder
        for folder in PAPERS.iterdir()
        if folder.is_dir() and folder.name != TEMPLATE.name and (folder / "status.json").exists()
    )


def tracked_paper_dirs() -> list[Path]:
    """Return paper folders whose status files are tracked in git.

    Defaulting to tracked files keeps local draft paper scaffolds from changing
    generated aggregate status files and matches CI behavior in a clean checkout.
    """

    try:
        result = subprocess.run(
            ["git", "ls-files", "--", "papers/*/status.json"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return all_paper_dirs()

    folders: set[Path] = set()
    for raw in result.stdout.splitlines():
        path = (ROOT / raw.strip()).resolve()
        if path.name == "status.json" and path.exists() and path.parent.parent == PAPERS:
            if path.parent.name != TEMPLATE.name:
                folders.add(path.parent)
    if not folders:
        return all_paper_dirs()
    return sorted(folders)


def paper_dirs(*, include_untracked: bool = False) -> list[Path]:
    if include_untracked:
        return all_paper_dirs()
    return tracked_paper_dirs()


def load_paper_status(folder: Path) -> dict[str, Any]:
    path = folder / "status.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path} should contain a JSON object")
    if payload.get("schema") != 1:
        raise ValueError(f"{path} should use schema 1")
    if payload.get("id") != folder.name:
        raise ValueError(f"{path} id should be {folder.name!r}")
    return payload


def paper_records(*, include_untracked: bool = False) -> list[tuple[Path, dict[str, Any]]]:
    return [
        (folder, load_paper_status(folder))
        for folder in paper_dirs(include_untracked=include_untracked)
    ]


def aggregate_payload(records: list[tuple[Path, dict[str, Any]]]) -> dict[str, Any]:
    papers = [payload for _folder, payload in records]
    return {
        "schema": 1,
        "description": (
            "Aggregate index generated from papers/<PaperName>/status.json. "
            "Paper-local status files are the source of truth for status, "
            "human summaries, review rows, and PaperInterface metadata."
        ),
        "review_count_policy": (
            "reviewed_rows counts saved human dashboard rows tracked in the public repository. "
            "total_rows counts the current dashboard review surface from each paper-local status.json. "
            "Agent source audits are not counted as human review."
        ),
        "paper_interface_maintenance_policy": (
            "PaperInterface.lean should stay compact and source-facing. Broad proof aliases belong "
            "in ProofInterface.lean or implementation modules. If row-level dashboard or "
            "LLM audit coverage needs a larger surface, put it in AuditInterface.lean and "
            "point review_surface.source_file there."
        ),
        "papers": papers,
    }


def status_label(status: str) -> str:
    return STATUS_LABELS.get(status, status.capitalize())


def publication_for(payload: dict[str, Any]) -> tuple[str, int]:
    publication = PUBLICATION_OVERRIDES.get(payload["id"])
    if publication is not None:
        return publication
    return str(payload.get("source_version", "")), 9999


def source_url_for(payload: dict[str, Any]) -> str:
    return SOURCE_URL_OVERRIDES.get(payload["id"], str(payload.get("source_url", "")))


def human_review_label(payload: dict[str, Any]) -> str:
    review = payload.get("human_review", {})
    return f"{int(review.get('reviewed_rows', 0))}/{int(review.get('total_rows', 0))}"


def human_translation_label(payload: dict[str, Any]) -> str:
    review = payload.get("human_review", {})
    reviewed = int(review.get("reviewed_rows", 0))
    total = int(review.get("total_rows", 0))
    stale = int(review.get("stale_rows", 0))
    mismatch = int(review.get("mismatch_rows", 0))
    uncertain = int(review.get("uncertain_rows", 0))
    parts = [f"{reviewed}/{total} reviewed"]
    if mismatch:
        parts.append(f"{mismatch} mismatch")
    if uncertain:
        parts.append(f"{uncertain} uncertain")
    if stale:
        parts.append(f"{stale} needs refresh")
    return "; ".join(parts)


def llm_statement_judgments_file(folder: Path) -> Path | None:
    tracked = folder / "audit" / "statement_match_llm.json"
    if tracked.exists() and tracked.is_file():
        return tracked
    tracked = folder / "statement_match_llm.json"
    if tracked.exists() and tracked.is_file():
        return tracked
    traced = folder / ".review_traces" / "statement_match_llm.json"
    if traced.exists() and traced.is_file():
        return traced
    return None


def normalize_llm_judgment(raw: Any) -> str:
    if isinstance(raw, bool):
        return "matches" if raw else "mismatch"
    value = str(raw or "").strip().lower()
    if value in {"match", "matches", "yes", "true", "equivalent", "same"}:
        return "matches"
    if value in {"mismatch", "does_not_match", "does not match", "no", "false", "different"}:
        return "mismatch"
    if value in {"uncertain", "unknown", "unsure", "partial", "needs_review"}:
        return "uncertain"
    return value


def load_llm_statement_judgments(folder: Path) -> dict[str, dict[str, Any]]:
    path = llm_statement_judgments_file(folder)
    if path is None:
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if not name:
            continue
        if isinstance(raw_value, dict):
            out[name] = dict(raw_value)
        else:
            out[name] = {"judgment": raw_value}
    return out


def load_json_object(path: Path) -> dict[str, Any]:
    if not path.exists() or not path.is_file():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, dict) else {}


def source_condition_rows_for_payload(payload: dict[str, Any], statement_total: int) -> int:
    review_surface = payload.get("review_surface", {})
    assumption_names = review_surface.get("assumption_names") if isinstance(review_surface, dict) else None
    assumption_count = (
        len([str(name).strip() for name in assumption_names if str(name).strip()])
        if isinstance(assumption_names, list)
        else 0
    )
    human_total = int(payload.get("human_review", {}).get("total_rows", 0))
    return max(0, min(assumption_count, human_total - statement_total))


def llm_translation_label_from_counts(
    *,
    total: int,
    matches: int,
    mismatch: int = 0,
    formalization_boundary: int = 0,
    source_condition_rows: int = 0,
    uncertain: int = 0,
    unknown: int = 0,
    missing: int = 0,
    stale: int = 0,
) -> str:
    if total <= 0:
        if source_condition_rows:
            label = "source-condition row" if source_condition_rows == 1 else "source-condition rows"
            return f"{source_condition_rows} {label}"
        return "not run"
    if (
        not any([matches, mismatch, formalization_boundary, source_condition_rows, uncertain, unknown, stale])
        and missing >= total
    ):
        return "not run"
    if source_condition_rows:
        parts = [f"{matches}/{total} statement rows match"]
    else:
        parts = [f"{matches}/{total} match"]
    if mismatch:
        parts.append(f"{mismatch} mismatch")
    if formalization_boundary:
        label = "formalization-boundary statement row" if formalization_boundary == 1 else "formalization-boundary statement rows"
        parts.append(f"{formalization_boundary} {label}")
    if source_condition_rows:
        label = "source-condition row" if source_condition_rows == 1 else "source-condition rows"
        parts.append(f"{source_condition_rows} {label}")
    if uncertain:
        parts.append(f"{uncertain} uncertain")
    if unknown:
        parts.append(f"{unknown} unknown")
    if missing:
        parts.append(f"{missing} missing")
    if stale:
        parts.append(f"{stale} stale")
    return "; ".join(parts)


def paper_coverage_label_from_counts(
    *,
    total: int,
    covered: int,
    conditional_boundary: int = 0,
    support_only: int = 0,
    support_only_required: int = 0,
    out_of_scope: int = 0,
    required_out_of_scope: int = 0,
    partial: int = 0,
    missing: int = 0,
    uncertain: int = 0,
    unknown: int = 0,
    stale: int = 0,
) -> str:
    if total <= 0:
        return "not run"
    if not any(
        [covered, conditional_boundary, support_only, out_of_scope, partial, uncertain, unknown, stale]
    ) and missing >= total:
        return "not run"
    parts = [f"{covered}/{total} covered"]
    if conditional_boundary:
        parts.append(f"{conditional_boundary} conditional boundaries")
    if support_only:
        parts.append(f"{support_only} support-only")
    if support_only_required:
        parts.append(f"{support_only_required} required support-only")
    if out_of_scope:
        parts.append(f"{out_of_scope} out of scope")
    if required_out_of_scope:
        parts.append(f"{required_out_of_scope} required scoped out")
    if partial:
        parts.append(f"{partial} partial")
    if missing:
        parts.append(f"{missing} missing")
    if uncertain:
        parts.append(f"{uncertain} uncertain")
    if unknown:
        parts.append(f"{unknown} unknown")
    if stale:
        parts.append(f"{stale} stale")
    return "; ".join(parts)


def llm_translation_label(
    folder: Path,
    payload: dict[str, Any],
    *,
    use_dashboard_audit: bool = False,
) -> str:
    review_surface = payload.get("review_surface", {})
    if use_dashboard_audit:
        try:
            import review_dashboard

            items = review_dashboard.review_items_for_paper(folder, use_cache=True)
            summary = review_dashboard.statement_translation_audit_summary(folder, items)
            statement_total = int(summary.get("row_count", 0))
            return llm_translation_label_from_counts(
                total=statement_total,
                matches=int(summary.get("matches", 0)),
                mismatch=int(
                    summary.get(
                        "unresolved_mismatch_count",
                        summary.get("mismatch_count", 0),
                    )
                ),
                formalization_boundary=int(summary.get("conditional_boundary_count", 0)),
                source_condition_rows=source_condition_rows_for_payload(payload, statement_total),
                uncertain=int(summary.get("uncertain_count", 0)),
                unknown=int(summary.get("unknown_count", 0)),
                missing=int(summary.get("missing_judgment_count", 0)),
                stale=int(summary.get("stale_judgment_count", 0)),
            )
        except Exception:
            pass

    include_names = review_surface.get("include_names") if isinstance(review_surface, dict) else None
    names = [str(name).strip() for name in include_names if str(name).strip()] if isinstance(include_names, list) else []
    judgments = load_llm_statement_judgments(folder)
    if not names:
        total = int(payload.get("human_review", {}).get("total_rows", 0))
        names = list(judgments)
    else:
        total = len(names)
    source_condition_rows = source_condition_rows_for_payload(payload, total)
    if not judgments:
        return llm_translation_label_from_counts(
            total=total,
            matches=0,
            missing=total,
            source_condition_rows=source_condition_rows,
        )

    matches = mismatch = formalization_boundary = uncertain = unknown = missing = 0
    for name in names:
        judgment = judgments.get(name)
        if judgment is None:
            missing += 1
            continue
        value = normalize_llm_judgment(judgment.get("judgment") or judgment.get("matches"))
        if value == "matches":
            matches += 1
        elif value == "mismatch":
            if judgment.get("resolution") == "conditional_boundary":
                formalization_boundary += 1
            else:
                mismatch += 1
        elif value == "uncertain":
            uncertain += 1
        else:
            unknown += 1

    return llm_translation_label_from_counts(
        total=total,
        matches=matches,
        mismatch=mismatch,
        formalization_boundary=formalization_boundary,
        source_condition_rows=source_condition_rows,
        uncertain=uncertain,
        unknown=unknown,
        missing=missing,
    )


def llm_paper_coverage_label(
    folder: Path,
    payload: dict[str, Any],
    *,
    use_dashboard_audit: bool = False,
) -> str:
    if use_dashboard_audit:
        try:
            import review_dashboard

            items = review_dashboard.review_items_for_paper(folder, use_cache=True)
            summary = review_dashboard.paper_coverage_audit_summary(folder, items)
            total = int(summary.get("inventory_count", 0))
            covered = int(summary.get("covered_count", 0))
            if (
                summary.get("inventory_is_scaffold")
                or summary.get("missing_source_grounded_audit")
                or int(summary.get("covered_with_seed_reason_count", 0))
                or int(summary.get("covered_without_source_evidence_count", 0))
            ):
                if total > 0:
                    return f"{covered}/{total} scaffold; needs source-grounded audit"
                return "needs source-grounded audit"
            return paper_coverage_label_from_counts(
                total=total,
                covered=covered,
                conditional_boundary=int(summary.get("conditional_boundary_count", 0)),
                support_only=int(summary.get("support_only_count", 0)),
                support_only_required=int(summary.get("support_only_required_source_item_count", 0)),
                out_of_scope=int(summary.get("out_of_scope_count", 0)),
                required_out_of_scope=int(summary.get("required_out_of_scope_count", 0)),
                partial=int(summary.get("partial_count", 0))
                + int(summary.get("missing_coverage_count", 0)),
                missing=int(summary.get("missing_count", 0)),
                uncertain=int(summary.get("uncertain_count", 0)),
                unknown=int(summary.get("unknown_count", 0)),
                stale=int(summary.get("stale_statement_count", 0))
                + (1 if summary.get("stale_inventory") else 0)
                + (1 if summary.get("stale_surface") else 0),
            )
        except Exception:
            pass

    statement_map = load_json_object(folder / "audit" / "paper_statement_map.json")
    inventory_kind = str(statement_map.get("source_inventory_kind") or "")
    inventory_scaffold = (
        statement_map.get("source_curated") is False
        or "dashboard_seeded" in inventory_kind
        or inventory_kind in {"exact_key_scaffold", "seeded_exact_key"}
    )
    map_items = statement_map.get("items")
    total = len(map_items) if isinstance(map_items, dict) else 0
    coverage = load_json_object(folder / "audit" / "paper_coverage_llm.json")
    if not coverage:
        coverage = load_json_object(folder / "paper_coverage_llm.json")
    audit_kind = str(coverage.get("audit_kind") or coverage.get("coverage_audit_kind") or "")
    coverage_scaffold = (
        coverage.get("source_grounded") is not True
        or coverage.get("seed_scaffold") is True
        or audit_kind in {"", "exact_key_scaffold", "dashboard_seeded_preliminary", "seeded_exact_key"}
    )
    coverage_items = coverage.get("items")
    if not isinstance(coverage_items, dict):
        return paper_coverage_label_from_counts(total=total, covered=0, missing=total)

    covered = conditional_boundary = support_only = out_of_scope = partial = missing = uncertain = unknown = 0
    seed_reason = missing_source_evidence = 0
    names = list(map_items) if isinstance(map_items, dict) else list(coverage_items)
    for name in names:
        item = coverage_items.get(name)
        if not isinstance(item, dict):
            missing += 1
            continue
        value = str(
            item.get("coverage") or item.get("judgment") or item.get("status") or ""
        ).strip().lower()
        if value in {"covered", "covered_by_rows"}:
            covered += 1
            reason = str(item.get("reason") or "").lower()
            if "exactly matches current dashboard row name" in reason or "exact source-key" in reason:
                seed_reason += 1
            if not str(item.get("source_evidence") or "").strip():
                missing_source_evidence += 1
        elif value in {"conditional_boundary", "covered_with_boundary"}:
            conditional_boundary += 1
            reason = str(item.get("reason") or "").lower()
            if "exactly matches current dashboard row name" in reason or "exact source-key" in reason:
                seed_reason += 1
            if not str(item.get("source_evidence") or "").strip():
                missing_source_evidence += 1
        elif value in {"covered_by_support", "support_only"}:
            support_only += 1
            reason = str(item.get("reason") or "").lower()
            if "exactly matches current dashboard row name" in reason or "exact source-key" in reason:
                seed_reason += 1
            if not str(item.get("source_evidence") or "").strip():
                missing_source_evidence += 1
        elif value in {"out_of_scope", "not_a_paper_target", "not_a_theorem_statement"}:
            out_of_scope += 1
        elif value == "partially_covered":
            partial += 1
        elif value == "missing":
            missing += 1
        elif value in {"uncertain", "unknown", "needs_review", ""}:
            uncertain += 1
        else:
            unknown += 1
    if inventory_scaffold or coverage_scaffold or seed_reason or missing_source_evidence:
        if total > 0:
            return f"{covered}/{total} scaffold; needs source-grounded audit"
        return "needs source-grounded audit"
    return paper_coverage_label_from_counts(
        total=total,
        covered=covered,
        conditional_boundary=conditional_boundary,
        support_only=support_only,
        out_of_scope=out_of_scope,
        partial=partial,
        missing=missing,
        uncertain=uncertain,
        unknown=unknown,
    )


def lean_loc(folder: Path) -> int:
    """Count all Lean lines in one paper folder, including proof modules."""

    total = 0
    for path in folder.rglob("*.lean"):
        with path.open(encoding="utf-8") as handle:
            total += sum(1 for _line in handle)
    return total


def component_loc(paths: list[str]) -> int:
    files: set[Path] = set()
    for raw_path in paths:
        path = ROOT / raw_path
        if path.is_dir():
            files.update(path.rglob("*.lean"))
        elif path.is_file() and path.suffix == ".lean":
            files.add(path)
    total = 0
    for path in sorted(files):
        with path.open(encoding="utf-8") as handle:
            total += sum(1 for _line in handle)
    return total


def human_note(payload: dict[str, Any]) -> str:
    note = payload.get("human_summary")
    if isinstance(note, str):
        return note
    if payload.get("status") == "formalized":
        return ""
    return str(payload.get("main_caveat", ""))


def human_summary_review(payload: dict[str, Any]) -> dict[str, str] | None:
    raw = payload.get("human_summary_review")
    if not isinstance(raw, dict):
        return None
    status = raw.get("status")
    if not isinstance(status, str) or not status.strip():
        return None
    review: dict[str, str] = {"status": status.strip()}
    note = raw.get("note")
    if isinstance(note, str) and note.strip():
        review["note"] = note.strip()
    return review


def human_status_rows(
    records: list[tuple[Path, dict[str, Any]]],
    *,
    use_dashboard_audit: bool = False,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for folder, payload in records:
        publication, year = publication_for(payload)
        row = {
            "id": payload["id"],
            "title": payload["title"],
            "authors": payload["authors"],
            "publication": publication,
            "publication_year": year,
            "source_url": source_url_for(payload),
            "paper_info": f"{payload['title']} by {payload['authors']}; {publication}.",
            "status": status_label(str(payload["status"])),
            "human_review": human_review_label(payload),
            "human_translation": human_translation_label(payload),
            "llm_as_judge_translation": llm_translation_label(
                folder,
                payload,
                use_dashboard_audit=use_dashboard_audit,
            ),
            "llm_as_judge_paper_coverage": llm_paper_coverage_label(
                folder,
                payload,
                use_dashboard_audit=use_dashboard_audit,
            ),
            "lean_loc": lean_loc(folder),
            "main_note": human_note(payload),
            "main_note_citation": note_citation(payload),
            "main_note_review": human_summary_review(payload),
            "paper_folder": str(folder.relative_to(ROOT)),
            "review_entrypoint": payload["review_entrypoint"],
            "artifacts": payload.get("artifacts", {}),
        }
        rows.append(row)

    rows.sort(
        key=lambda row: (
            STATUS_GROUPS.get(str(row["status"]).lower(), 2),
            int(row["publication_year"]),
            str(row["title"]).lower(),
        )
    )
    return rows


def human_payload(
    records: list[tuple[Path, dict[str, Any]]],
    *,
    use_dashboard_audit: bool = False,
) -> dict[str, Any]:
    return {
        "schema": 1,
        "description": (
            "Compact human-facing status generated from paper-local status.json files. "
            "Use papers/status.json for detailed machine/audit metadata."
        ),
        "generated_by": "python3 scripts/sync_paper_status.py",
        "sort_policy": (
            "Formalized papers first, including formalized-with-caveat rows, ordered by "
            "publication year; partially formalized papers follow in publication-year order."
        ),
        "note_policy": (
            "main_note is intentionally sparse. Fully formalized papers have a blank note unless "
            "a source-version or proof-route note is important for a public reader."
        ),
        "review_count_policy": (
            "human_review counts saved human dashboard rows as reviewed/total. Agent audits are "
            "not counted as human review."
        ),
        "translation_status_policy": (
            "human_translation reports saved human dashboard judgments. "
            "llm_as_judge_translation reports context-free Lean-to-TeX plus "
            "paper-vs-translation LLM-judge counts, including stale/missing/uncertain "
            "flags when available; accepted conditional-boundary mismatches are shown "
            "as formalization-boundary statement rows and explicit assumption/source "
            "conditions are shown as source-condition rows so totals reconcile with "
            "the human-review surface. llm_as_judge_paper_coverage reports the "
            "paper-level source-inventory-to-dashboard-row coverage audit."
        ),
        "lean_loc_policy": (
            "lean_loc sums all .lean files under each paper folder, including proof "
            "modules. It is not the PaperInterface.lean line count."
        ),
        "identifier_policy": (
            "Paper IDs and folder names are stable artifact identifiers and may track an arXiv, "
            "conference, or original working-paper year. Publication fields use the published "
            "citation title and year."
        ),
        "papers": human_status_rows(records, use_dashboard_audit=use_dashboard_audit),
    }


def md_escape(text: str) -> str:
    return " ".join(text.split()).replace("|", r"\|")


def md_note_with_citation(note: str, citation: dict[str, str] | None) -> str:
    note = md_escape(note)
    if not citation:
        return note
    label = md_escape(citation["label"])
    url = citation["url"]
    rendered_citation = f"[{label}]({url})"
    if note.endswith("."):
        return f"{note[:-1]} {rendered_citation}."
    return f"{note} {rendered_citation}"


def repo_relative_link(path: str) -> str:
    return f"../{path}"


def readme_note(payload: dict[str, Any]) -> str:
    return md_note_with_citation(human_note(payload), note_citation(payload))


def relative_markdown_path(from_dir: Path, repo_relative_path: str) -> str:
    target = (ROOT / repo_relative_path).resolve()
    return os.path.relpath(target, start=from_dir.resolve()).replace(os.sep, "/")


def markdown_file_link(from_dir: Path, repo_relative_path: str, label: str) -> str:
    return f"[{md_escape(label)}]({relative_markdown_path(from_dir, repo_relative_path)})"


def paper_file_if_present(folder: Path, repo_relative_path: str | None) -> str | None:
    if not isinstance(repo_relative_path, str) or not repo_relative_path.strip():
        return None
    candidate = ROOT / repo_relative_path.strip()
    if candidate.exists() and candidate.is_file():
        return repo_relative_path.strip()
    return None


def first_present_artifact(folder: Path, payload: dict[str, Any], *keys: str) -> str | None:
    artifacts = payload.get("artifacts", {})
    if isinstance(artifacts, dict):
        for key in keys:
            path = paper_file_if_present(folder, artifacts.get(key))
            if path:
                return path
    return None


def review_entrypoint_path(folder: Path, payload: dict[str, Any]) -> str | None:
    path = paper_file_if_present(folder, str(payload.get("review_entrypoint", "")))
    if path:
        return path
    return first_present_artifact(folder, payload, "final_validation_report")


def dependency_dag_path(folder: Path, payload: dict[str, Any]) -> str | None:
    return first_present_artifact(folder, payload, "dependency_dag_pdf", "dependency_dag_tex")


def paper_interface_path(folder: Path, payload: dict[str, Any]) -> str | None:
    interface = payload.get("paper_interface", {})
    if isinstance(interface, dict):
        path = paper_file_if_present(folder, interface.get("path"))
        if path:
            return path
    return first_present_artifact(folder, payload, "paper_interface")


def audit_surface_path(folder: Path, payload: dict[str, Any]) -> str | None:
    interface = payload.get("paper_interface", {})
    if isinstance(interface, dict):
        path = paper_file_if_present(folder, interface.get("audit_surface_path"))
        if path:
            return path
    review_surface = payload.get("review_surface", {})
    if isinstance(review_surface, dict):
        path = paper_file_if_present(folder, review_surface.get("source_file"))
        interface_path = paper_interface_path(folder, payload)
        if path and path != interface_path:
            return path
    return None


def json_surface_paths(folder: Path) -> list[tuple[str, str]]:
    candidates = [
        ("status.json", folder / "status.json"),
        ("paper statement map", folder / "audit" / "paper_statement_map.json"),
        ("paper coverage audit", folder / "audit" / "paper_coverage_llm.json"),
        ("paper coverage audit", folder / "paper_coverage_llm.json"),
        ("source-record audit", folder / "audit" / "source_record_audit.json"),
        ("source-record audit", folder / "source_record_audit.json"),
        ("statement match audit", folder / "audit" / "statement_match_llm.json"),
        ("statement match audit", folder / "statement_match_llm.json"),
    ]
    seen_labels: set[str] = set()
    out: list[tuple[str, str]] = []
    for label, path in candidates:
        if label in seen_labels:
            continue
        if path.exists() and path.is_file():
            seen_labels.add(label)
            out.append((label, str(path.relative_to(ROOT))))
    return out


def paper_reference_markdown(folder: Path, payload: dict[str, Any]) -> str:
    publication, _year = publication_for(payload)
    title = md_escape(str(payload.get("title", payload["id"])))
    source_url = source_url_for(payload)
    if source_url:
        title = f"[{title}]({source_url})"
    return f"{title} by {md_escape(str(payload.get('authors', '')))}; {md_escape(publication)}."


def generated_paper_readme_block(folder: Path, payload: dict[str, Any]) -> str:
    review_path = review_entrypoint_path(folder, payload)
    dag_path = dependency_dag_path(folder, payload)
    interface_path = paper_interface_path(folder, payload)
    audit_path = audit_surface_path(folder, payload)
    notes_path = str((folder / LEGACY_README_NOTES).relative_to(ROOT))
    include_notes = (ROOT / notes_path).exists() or legacy_readme_body(folder) is not None
    json_links = [
        markdown_file_link(folder, path, label)
        for label, path in json_surface_paths(folder)
    ]

    link_lines = []
    if review_path:
        review_label = (
            "Agent source audit"
            if str(payload.get("status", "")).strip().lower() == "paper draft"
            else "Final validation report"
        )
        link_lines.append(
            f"- {review_label}: {markdown_file_link(folder, review_path, Path(review_path).name)}"
        )
    else:
        review_label = (
            "Agent source audit"
            if str(payload.get("status", "")).strip().lower() == "paper draft"
            else "Final validation report"
        )
        link_lines.append(f"- {review_label}: not tracked in this folder.")
    if dag_path:
        link_lines.append(f"- Dependency DAG: {markdown_file_link(folder, dag_path, Path(dag_path).name)}")
    else:
        link_lines.append("- Dependency DAG: not tracked in this folder.")
    if interface_path:
        link_lines.append(
            f"- Compact Lean interface: {markdown_file_link(folder, interface_path, Path(interface_path).name)}"
        )
    else:
        link_lines.append("- Compact Lean interface: not tracked in this folder.")
    if audit_path:
        link_lines.append(
            f"- Audited review surface: {markdown_file_link(folder, audit_path, Path(audit_path).name)}"
        )
    link_lines.append("- Source/status JSON: " + "; ".join(json_links) + ".")
    if include_notes:
        link_lines.append(
            f"- Additional documentation: {markdown_file_link(folder, notes_path, Path(notes_path).name)}"
        )

    lines = [
        PAPER_README_BEGIN,
        f"# {str(payload.get('title', payload['id'])).strip()}",
        "",
        "| Field | Value |",
        "|---|---|",
        f"| Final status | {md_escape(status_label(str(payload['status'])))} |",
        f"| Paper reference | {paper_reference_markdown(folder, payload)} |",
        f"| Lines of Code | {lean_loc(folder):,} |",
        "",
        "## Key Links",
        "",
        *link_lines,
        PAPER_README_END,
        "",
    ]
    return "\n".join(lines)


def legacy_readme_body(folder: Path) -> str | None:
    current_path = folder / "README.md"
    if not current_path.exists():
        return None
    current = current_path.read_text(encoding="utf-8")
    start = current.find(PAPER_README_BEGIN)
    stop = current.find(PAPER_README_END)
    if start >= 0 or stop >= 0:
        if start < 0 or stop < 0 or stop < start:
            raise ValueError(
                f"{current_path.relative_to(ROOT)} has malformed generated README markers"
            )
        stop += len(PAPER_README_END)
        body = current[stop:].strip()
    else:
        body = current.strip()
    return body or None


def render_legacy_readme_notes(folder: Path) -> tuple[Path, str] | None:
    notes_path = folder / LEGACY_README_NOTES
    if notes_path.exists():
        return None
    body = legacy_readme_body(folder)
    if body is None:
        return None
    rendered = "\n".join(
        [
            "# Formalization Notes",
            "",
            "This file preserves the previous hand-written paper-folder README content.",
            "The paper-folder `README.md` is now a generated status overview.",
            "",
            body,
            "",
        ]
    )
    return notes_path, rendered


def render_paper_readme(folder: Path, payload: dict[str, Any]) -> str:
    return generated_paper_readme_block(folder, payload)


def render_paper_status_md(payload: dict[str, Any]) -> str:
    lines = [
        "# Paper Status",
        "",
        "This file is generated by `python3 scripts/sync_paper_status.py` from",
        "paper-local `papers/<PaperName>/status.json` files. Edit those sources",
        "rather than this table.",
        "",
        "The table is intentionally human-facing. `Note` is blank for",
        "formalized papers unless a source-version, proof-route, or remaining-boundary",
        "note is useful to a public reader. For detailed machine-readable metadata,",
        "see [`papers/status.json`](../papers/status.json); for the compact public",
        "JSON, see [`papers/human_status.json`](../papers/human_status.json).",
        "",
        "Human-review counts are dashboard rows saved by a human reviewer; agent",
        "source audits are not counted as human review.",
        "",
        "Paper IDs and folder names are stable artifact identifiers and may track",
        "an arXiv, conference, or original working-paper year. The table below uses",
        "the published citation title and year.",
        "",
        "| Paper, authors, publication | Status | Human review | Paper coverage | Lines of Code | Public note |",
        "|---|---|---:|---:|---:|---|",
    ]
    for row in payload["papers"]:
        paper_href = row["source_url"] or repo_relative_link(row["paper_folder"])
        paper_link = f"[{md_escape(row['title'])}]({paper_href})"
        paper_info = (
            f"{paper_link} by {md_escape(row['authors'])}; "
            f"{md_escape(row['publication'])}."
        )
        status_link = f"[{md_escape(row['status'])}]({repo_relative_link(row['review_entrypoint'])})"
        lines.append(
            "| "
            + " | ".join(
                [
                    paper_info,
                    status_link,
                    md_escape(row["human_review"]),
                    md_escape(row["llm_as_judge_paper_coverage"]),
                    f"{int(row['lean_loc']):,}",
                    md_note_with_citation(row["main_note"], row.get("main_note_citation")),
                ]
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "For status vocabulary, see [`docs/STATUS.md`](STATUS.md).",
            "",
        ]
    )
    return "\n".join(lines)


def html_escape(text: object) -> str:
    return html.escape(str(text), quote=True)


def github_link(path: str) -> str:
    return GITHUB_MAIN + path


def html_note_with_citation(note: str, citation: dict[str, str] | None) -> str:
    rendered = html_escape(note)
    if not citation:
        return rendered
    label = html_escape(citation["label"])
    url = html_escape(citation["url"])
    rendered_citation = f'<a href="{url}">{label}</a>'
    if rendered.endswith("."):
        return f"{rendered[:-1]} {rendered_citation}."
    return f"{rendered} {rendered_citation}"


def site_status_artifacts_cell(row: dict[str, Any]) -> str:
    status_href = html_escape(github_link(row["review_entrypoint"]))
    status = html_escape(row["status"])
    links = [
        f'<a href="{status_href}">{status}</a>',
    ]
    artifacts = row.get("artifacts")
    if isinstance(artifacts, dict):
        dag = artifacts.get("dependency_dag_pdf") or artifacts.get("dependency_dag_tex")
        if isinstance(dag, str) and dag.strip():
            links.append(f'<a href="{html_escape(github_link(dag.strip()))}">DAG</a>')
    return '<div class="artifact-links">' + " ".join(links) + "</div>"


def render_site_library_block(human: dict[str, Any]) -> str:
    indent = " " * 14
    lines = [f"{indent}{SITE_LIBRARY_BEGIN}"]
    for component in LIBRARY_COMPONENTS:
        title = html_escape(component["title"])
        paths = component["paths"]
        if paths:
            title = f'<a href="{html_escape(github_link(paths[0]))}">{title}</a>'
        lines.extend(
            [
                f"{indent}<tr>",
                f"{indent}  <td>{title}</td>",
                f"{indent}  <td>{html_escape(component['examples'])}</td>",
                f"{indent}  <td>{component_loc(component['paths']):,}</td>",
                f"{indent}</tr>",
            ]
        )
    lines.append(f"{indent}{SITE_LIBRARY_END}")
    return "\n".join(lines)


def render_site_stats_block(payload: dict[str, Any]) -> str:
    indent = " " * 8
    papers = payload["papers"]
    formalized = sum(1 for row in papers if str(row["status"]).startswith("Formalized"))
    partial = sum(1 for row in papers if row["status"] == "Partially formalized")
    lean_loc = sum(int(row["lean_loc"]) for row in papers)
    lines = [
        f"{indent}{SITE_STATS_BEGIN}",
        f'{indent}<p class="project-stats">',
        (
            f"{indent}  Currently, the project contains {formalized} formalized papers "
            f"and {partial} partially formalized papers, with {lean_loc:,} total "
            "lines of Lean code."
        ),
        f"{indent}</p>",
        f"{indent}{SITE_STATS_END}",
    ]
    return "\n".join(lines)


def render_site_status_block(payload: dict[str, Any]) -> str:
    indent = " " * 14
    lines = [f"{indent}{SITE_STATUS_BEGIN}"]
    for row in payload["papers"]:
        paper_href = row["source_url"] or github_link(row["paper_folder"])
        note = html_note_with_citation(row["main_note"], row.get("main_note_citation"))
        lines.extend(
            [
                f"{indent}<tr>",
                f"{indent}  <td>",
                (
                    f'{indent}    <a class="paper-source" href="{html_escape(paper_href)}">'
                    f"<cite>{html_escape(row['title'])}</cite></a> by"
                ),
                (
                    f"{indent}    {html_escape(row['authors'])}; "
                    f"{html_escape(row['publication'])}."
                ),
                f"{indent}  </td>",
                f"{indent}  <td>{site_status_artifacts_cell(row)}</td>",
                f"{indent}  <td>{html_escape(row['human_translation'])}</td>",
                f"{indent}  <td>{int(row['lean_loc']):,}</td>",
                f"{indent}  <td>{note}</td>",
                f"{indent}</tr>",
            ]
        )
    lines.append(f"{indent}{SITE_STATUS_END}")
    return "\n".join(lines)


def render_site_index(payload: dict[str, Any]) -> str:
    current = SITE_INDEX.read_text(encoding="utf-8")
    library_block = render_site_library_block(payload)
    library_start = current.find(SITE_LIBRARY_BEGIN)
    library_end = current.find(SITE_LIBRARY_END)
    if library_start >= 0 and library_end >= library_start:
        library_end += len(SITE_LIBRARY_END)
        line_start = current.rfind("\n", 0, library_start) + 1
        line_end = current.find("\n", library_end)
        if line_end < 0:
            current = current[:line_start] + library_block
        else:
            current = current[:line_start] + library_block + current[line_end:]

    stats_block = render_site_stats_block(payload)
    stats_start = current.find(SITE_STATS_BEGIN)
    stats_end = current.find(SITE_STATS_END)
    if stats_start >= 0 and stats_end >= stats_start:
        stats_end += len(SITE_STATS_END)
        line_start = current.rfind("\n", 0, stats_start) + 1
        line_end = current.find("\n", stats_end)
        if line_end < 0:
            current = current[:line_start] + stats_block
        else:
            current = current[:line_start] + stats_block + current[line_end:]

    block = render_site_status_block(payload)
    start = current.find(SITE_STATUS_BEGIN)
    end = current.find(SITE_STATUS_END)
    if start >= 0 and end >= start:
        end += len(SITE_STATUS_END)
        line_start = current.rfind("\n", 0, start) + 1
        line_end = current.find("\n", end)
        if line_end < 0:
            return current[:line_start] + block
        return current[:line_start] + block + current[line_end:]

    tbody_start = current.find("<tbody>")
    if tbody_start < 0:
        raise ValueError(f"{SITE_INDEX.relative_to(ROOT)} should contain a paper status <tbody>")
    tbody_open_end = current.find(">", tbody_start)
    tbody_end = current.find("</tbody>", tbody_open_end)
    if tbody_open_end < 0 or tbody_end < 0:
        raise ValueError(f"{SITE_INDEX.relative_to(ROOT)} should contain a complete paper status <tbody>")
    return current[: tbody_open_end + 1] + "\n" + block + "\n            " + current[tbody_end:]


def assert_required_static_site_copy(rendered: str) -> None:
    missing = [
        label
        for label, required in SITE_REQUIRED_STATIC_COPY.items()
        if required not in rendered
    ]
    if missing:
        joined = ", ".join(missing)
        raise ValueError(
            f"{SITE_INDEX.relative_to(ROOT)} is missing required static site copy: {joined}"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if generated status files are out of sync")
    parser.add_argument(
        "--include-untracked",
        action="store_true",
        help="also include untracked draft paper folders with status.json",
    )
    parser.add_argument(
        "--dashboard-audit",
        action="store_true",
        help=(
            "derive LLM statement-review counts through review_dashboard.py. "
            "This is slower; the default status sync reads tracked sidecars only."
        ),
    )
    args = parser.parse_args()

    records = paper_records(include_untracked=args.include_untracked)
    aggregate = aggregate_payload(records)
    human = human_payload(records, use_dashboard_audit=args.dashboard_audit)
    outputs = {
        AGGREGATE_STATUS: json.dumps(aggregate, indent=2, ensure_ascii=False) + "\n",
        HUMAN_STATUS: json.dumps(human, indent=2, ensure_ascii=False) + "\n",
        DOCS_PAPER_STATUS: render_paper_status_md(human),
        SITE_INDEX: render_site_index(human),
    }
    for folder, payload in records:
        legacy_notes = render_legacy_readme_notes(folder)
        if legacy_notes is not None:
            path, rendered = legacy_notes
            outputs[path] = rendered
        outputs[folder / "README.md"] = render_paper_readme(folder, payload)
    try:
        assert_no_root_readme_outputs(outputs)
        assert_root_readme_locked()
        assert_required_static_site_copy(outputs[SITE_INDEX])
    except ValueError as exc:
        print(exc)
        return 1
    if args.check:
        stale = []
        for path, rendered in outputs.items():
            current = path.read_text(encoding="utf-8") if path.exists() else ""
            if current != rendered:
                stale.append(path.relative_to(ROOT))
        if stale:
            print("generated status files are out of sync; run `python3 scripts/sync_paper_status.py`")
            for path in stale:
                print(f"- {path}")
            return 1
        return 0
    for path, rendered in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered, encoding="utf-8")
        print(f"wrote {path.relative_to(ROOT)} from paper-local status files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
