#!/usr/bin/env python3
"""Paper-scoped private checkpoint helper.

This intentionally avoids repository-wide audits, aggregate paper-status
regeneration, and cross-paper LLM sidecar refreshes.  Use it before a private
commit that should contain one paper folder plus an explicit list of shared
library/tooling files.
"""

from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def require_repo_path(path: Path) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(ROOT)
    except ValueError:
        fail(f"path is outside this repository: {path}")
    return resolved


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(2)


def run(cmd: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    print("+ " + " ".join(shlex.quote(part) for part in cmd), flush=True)
    return subprocess.run(cmd, cwd=ROOT, text=True, check=check)


def json_file(path: Path) -> object:
    try:
        with path.open(encoding="utf-8") as handle:
            return json.load(handle)
    except json.JSONDecodeError as exc:
        fail(f"{rel(path)} is not valid JSON: {exc}")


def default_build_target(paper_dir: Path, paper: str) -> str:
    status_path = paper_dir / "status.json"
    if status_path.exists():
        payload = json_file(status_path)
        if isinstance(payload, dict):
            raw = payload.get("build_target")
            if isinstance(raw, str) and raw.strip():
                return raw.strip()
    return paper


def existing_json_sidecars(paper_dir: Path) -> list[Path]:
    names = [
        "status.json",
        "assumption_match_llm.json",
        "lean_to_tex_llm.json",
        "paper_coverage_llm.json",
        "paper_statement_map.json",
        "review_surface_llm.json",
        "source_record_audit.json",
        "source_record_match_llm.json",
        "statement_match_llm.json",
    ]
    return [paper_dir / name for name in names if (paper_dir / name).exists()]


def path_arg(raw: str) -> Path:
    path = Path(raw)
    return path if path.is_absolute() else ROOT / path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run paper-scoped private checkpoint checks and print an explicit "
            "git add command for that paper plus named shared paths."
        )
    )
    parser.add_argument("paper", help="paper folder name, e.g. ExamplePaper")
    parser.add_argument(
        "--include-path",
        "--include-library",
        dest="include_path",
        action="append",
        default=[],
        help=(
            "extra shared path to validate and stage, such as an EconCSLib file; "
            "repeat for multiple paths"
        ),
    )
    parser.add_argument(
        "--build-target",
        help="override the default `lake build <paper>` target",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="skip the targeted Lean build",
    )
    parser.add_argument(
        "--no-json",
        action="store_true",
        help="skip JSON parsing for paper-local sidecars",
    )
    parser.add_argument(
        "--allow-missing-extra",
        action="store_true",
        help="allow --include-path entries that do not exist yet",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paper_dir = PAPERS / args.paper
    if not paper_dir.is_dir():
        fail(f"paper folder does not exist: {rel(paper_dir)}")

    paper_root_module = PAPERS / f"{args.paper}.lean"
    paper_paths = [paper_dir]
    if paper_root_module.exists():
        paper_paths.append(paper_root_module)

    extra_paths = [require_repo_path(path_arg(raw)) for raw in args.include_path]
    missing_extra_paths = [path for path in extra_paths if not path.exists()]
    if missing_extra_paths and not args.allow_missing_extra:
        missing = ", ".join(rel(path) for path in missing_extra_paths)
        fail(f"--include-path entry does not exist: {missing}")

    checkpoint_paths = [*paper_paths, *extra_paths]
    checkpoint_args = [rel(path) for path in checkpoint_paths]

    if not args.no_json:
        for path in existing_json_sidecars(paper_dir):
            json_file(path)
        print(f"checked JSON sidecars under {rel(paper_dir)}", flush=True)

    if not args.no_build:
        target = args.build_target or default_build_target(paper_dir, args.paper)
        run(["lake", "build", target])

    run(["git", "diff", "--check", "--", *checkpoint_args])
    run(["git", "status", "--short", "--", *checkpoint_args], check=False)

    quoted_paths = " ".join(shlex.quote(path) for path in checkpoint_args)
    print()
    print("Paper-scoped checkpoint complete.")
    print("Stage only this checkpoint with:")
    print(f"  git add -- {quoted_paths}")
    print()
    print("Do not refresh aggregate paper status or unrelated audit sidecars for this private checkpoint.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
