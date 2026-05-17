#!/usr/bin/env python3
"""Create paper-local `review-dashboard.sh` launchers for existing paper folders."""

from __future__ import annotations

import argparse
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"

REVIEW_LAUNCHER_TEXT = """#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)"
ROOT_DIR="$(cd \"${SCRIPT_DIR}/../..\" && pwd)"
PAPER_DIR=\"$(basename \"$SCRIPT_DIR\")\"

exec \"${ROOT_DIR}/scripts/launch_review_dashboard.sh\" --paper \"$PAPER_DIR\" \"$@\"
"""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Add paper-local review-dashboard launchers.")
    parser.add_argument("--paper", help="Optional paper folder name to scope the operation.")
    parser.add_argument(
        "--write",
        action="store_true",
        help="Write launchers. Without this flag, this is a dry-run scan.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Overwrite existing launchers.",
    )
    parser.add_argument(
        "--refresh-cache",
        action="store_true",
        help="After ensuring launchers, refresh each paper's dashboard metadata cache.",
    )
    return parser.parse_args()


def iter_papers(paper: str | None) -> list[Path]:
    papers = sorted(
        [path for path in PAPERS.iterdir() if path.is_dir() and path.name != "TEMPLATE"]
    )
    if paper:
        papers = [path for path in papers if path.name == paper]
    return papers


def ensure_launcher(folder: Path, *, write: bool, force: bool) -> tuple[bool, bool]:
    """Return `(installed_or_present, did_write)` for one folder."""

    script_path = folder / "review-dashboard.sh"
    if script_path.exists() and not force:
        return True, False

    if not write:
        return False, False

    script_path.write_text(REVIEW_LAUNCHER_TEXT, encoding="utf-8")
    script_path.chmod(0o755)
    return True, True


def refresh_cache(folder: Path) -> bool:
    cmd = [
        "python3",
        str(ROOT / "scripts" / "review_dashboard.py"),
        "--paper",
        folder.name,
        "--refresh-cache",
    ]
    proc = subprocess.run(cmd, cwd=str(ROOT), check=False, capture_output=True, text=True)
    if proc.returncode == 0:
        print(f"[cache-refreshed] {folder.name}")
        return True
    print(f"[cache-failed] {folder.name}")
    if proc.stdout.strip():
        print(proc.stdout.strip())
    if proc.stderr.strip():
        print(proc.stderr.strip())
    return False


def main() -> None:
    args = parse_args()
    written = 0
    present = 0
    missing = 0
    missing_interface = 0
    refreshed = 0
    refresh_failed = 0

    for folder in iter_papers(args.paper):
        if not (folder / "PaperInterface.lean").exists():
            print(f"[missing-paper-interface] {folder.name}")
            missing_interface += 1
            continue

        has_script, wrote = ensure_launcher(folder, write=args.write, force=args.force)
        if not has_script:
            if (folder / "PaperInterface.lean").exists():
                missing += 1
            continue
        if wrote:
            written += 1
            print(f"[written] {folder.name}/review-dashboard.sh")
        else:
            present += 1
            print(f"[present] {folder.name}/review-dashboard.sh")
        if args.refresh_cache:
            if refresh_cache(folder):
                refreshed += 1
            else:
                refresh_failed += 1

    if not args.write:
        print(
            f"{present} present, {missing} missing launcher(s), "
            f"{missing_interface} missing PaperInterface.lean file(s). Use --write to generate launchers."
        )
    else:
        msg = (
            f"{written} launcher(s) written/updated, {present} unchanged, "
            f"{missing_interface} missing PaperInterface.lean file(s)."
        )
        if args.refresh_cache:
            msg += f" {refreshed} cache(s) refreshed, {refresh_failed} cache refresh failure(s)."
        print(msg)


if __name__ == "__main__":
    main()
