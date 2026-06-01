#!/usr/bin/env python3
"""Synchronize aggregate paper status from paper-local status JSON files."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
AGGREGATE_STATUS = PAPERS / "status.json"
TEMPLATE = PAPERS / "TEMPLATE"


def paper_dirs() -> list[Path]:
    return sorted(
        folder
        for folder in PAPERS.iterdir()
        if folder.is_dir() and folder.name != TEMPLATE.name and (folder / "status.json").exists()
    )


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


def aggregate_payload() -> dict[str, Any]:
    papers = [load_paper_status(folder) for folder in paper_dirs()]
    return {
        "schema": 1,
        "description": (
            "Aggregate index generated from papers/<PaperName>/status.json. "
            "Paper-local status files are the source of truth for status, "
            "review rows, and PaperInterface metadata."
        ),
        "review_count_policy": (
            "reviewed_rows counts saved human dashboard rows tracked in the public repository. "
            "total_rows counts the current dashboard review surface from each paper-local status.json. "
            "Agent source audits are not counted as human review."
        ),
        "paper_interface_maintenance_policy": (
            "PaperInterface.lean should stay compact and source-facing. Broad proof aliases belong "
            "in ProofInterface.lean or implementation modules."
        ),
        "papers": papers,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if papers/status.json is out of sync")
    args = parser.parse_args()

    payload = aggregate_payload()
    rendered = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    if args.check:
        current = AGGREGATE_STATUS.read_text(encoding="utf-8") if AGGREGATE_STATUS.exists() else ""
        if current != rendered:
            print("papers/status.json is out of sync; run `python3 scripts/sync_paper_status.py`")
            return 1
        return 0
    AGGREGATE_STATUS.write_text(rendered, encoding="utf-8")
    print(f"wrote {AGGREGATE_STATUS.relative_to(ROOT)} from paper-local status files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
