#!/usr/bin/env python3
"""Seed paper_coverage_llm.json from an explicit source-statement inventory.

This helper is intentionally conservative.  It only marks a source item
`covered` when its canonical key or alias exactly matches a current dashboard
row.  Everything else is left `uncertain` so a separate LLM/source-reading pass
can decide whether it is covered, partially covered, missing, or out of scope.
Do not use this exact-key scaffold to justify omitting source-visible
definitions, examples, remarks, propositions, theorems/corollaries, or
main-text lemmas for compactness; those should be represented by dashboard rows
before closeout unless explicitly outside the paper target.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"

sys.path.insert(0, str(ROOT / "scripts"))
from review_dashboard import (  # noqa: E402
    DEFAULT_LLM_PAPER_COVERAGE_FILE,
    paper_statement_inventory,
    paper_statement_inventory_digest,
    review_items_for_paper,
    review_surface_digest,
)


def seed_payload(folder: Path, validator: str, validator_type: str) -> dict[str, Any]:
    inventory = paper_statement_inventory(folder)
    items = review_items_for_paper(folder, use_cache=True)
    row_names = {item.name for item in items}
    coverage: dict[str, dict[str, Any]] = {}
    for key, item in sorted(inventory.items()):
        aliases = [str(alias) for alias in item.get("aliases", []) or [] if str(alias).strip()]
        candidates = [key, *aliases]
        matched = [candidate for candidate in candidates if candidate in row_names]
        if matched:
            judgment = "covered"
            reason = "Canonical source key or alias exactly matches current dashboard row name."
            review_rows = sorted(set(matched))
        else:
            judgment = "uncertain"
            reason = (
                "No exact source-key/alias match to a current dashboard row. "
                "Requires independent source-to-row review; compactness alone "
                "is not a reason to scope out source-visible named material."
            )
            review_rows = []
        coverage[key] = {
            "coverage": judgment,
            "review_rows": review_rows,
            "reason": reason,
            "source_evidence": "",
            "dashboard_evidence": "",
            "statement_sha256": str(item.get("statement_sha256") or ""),
            "audit_kind": "exact_key_scaffold",
            "source_grounded": False,
            "seed_scaffold": True,
        }
    return {
        "schema": 1,
        "paper": folder.name,
        "prompt_version": "paper-coverage-v2-source-grounded-source-to-dashboard",
        "audit_kind": "exact_key_scaffold",
        "source_grounded": False,
        "seed_scaffold": True,
        "validator": validator,
        "validator_type": validator_type,
        "validated_at": datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
            "+00:00",
            "Z",
        ),
        "comment": (
            "Seeded by exact source-key/alias matches. Non-exact items remain "
            "uncertain until an independent LLM/source-reading pass resolves them."
        ),
        "paper_statement_inventory_sha256": paper_statement_inventory_digest(inventory),
        "review_surface_sha256": review_surface_digest(items),
        "items": coverage,
    }


def iter_papers(paper: str | None) -> list[Path]:
    if paper:
        folder = PAPERS_DIR / paper
        if not folder.is_dir():
            raise SystemExit(f"unknown paper folder: {paper}")
        return [folder]
    return sorted(
        folder
        for folder in PAPERS_DIR.iterdir()
        if folder.is_dir() and folder.name != "TEMPLATE" and (folder / "PaperInterface.lean").exists()
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", default="", help="Optional paper folder to seed.")
    parser.add_argument(
        "--write",
        action="store_true",
        help="Write paper_coverage_llm.json. Without this flag, only print a summary.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Overwrite an existing paper_coverage_llm.json.",
    )
    parser.add_argument(
        "--validator",
        default="seed_paper_coverage.py",
        help="Validator label to store in the seeded sidecar.",
    )
    parser.add_argument(
        "--validator-type",
        default="script",
        choices=("script", "agent", "model", "human"),
        help="Validator type to store in the seeded sidecar.",
    )
    args = parser.parse_args()

    for folder in iter_papers(args.paper or None):
        inventory = paper_statement_inventory(folder)
        if not inventory:
            print(f"{folder.name}: no explicit/resolvable source inventory")
            continue
        payload = seed_payload(folder, args.validator, args.validator_type)
        values = [item.get("coverage") for item in payload["items"].values()]
        covered = sum(1 for value in values if value == "covered")
        uncertain = sum(1 for value in values if value == "uncertain")
        print(
            f"{folder.name}: inventory={len(inventory)} covered_by_exact_key={covered} "
            f"uncertain={uncertain}"
        )
        if not args.write:
            continue
        out = folder / DEFAULT_LLM_PAPER_COVERAGE_FILE
        if out.exists() and not args.force:
            raise SystemExit(f"{out} exists; use --force to overwrite")
        out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
