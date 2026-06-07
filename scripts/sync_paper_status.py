#!/usr/bin/env python3
"""Synchronize aggregate paper status from paper-local status JSON files."""

from __future__ import annotations

import argparse
import html
import json
from pathlib import Path
from typing import Any

try:
    import review_dashboard
except Exception:  # pragma: no cover - status sync should still work without dashboard helpers.
    review_dashboard = None  # type: ignore[assignment]


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
AGGREGATE_STATUS = PAPERS / "status.json"
HUMAN_STATUS = PAPERS / "human_status.json"
DOCS_PAPER_STATUS = ROOT / "docs" / "PAPER_STATUS.md"
README = ROOT / "README.md"
SITE_INDEX = ROOT / "site" / "index.html"
TEMPLATE = PAPERS / "TEMPLATE"
README_STATUS_BEGIN = "<!-- BEGIN GENERATED PAPER STATUS TABLE -->"
README_STATUS_END = "<!-- END GENERATED PAPER STATUS TABLE -->"
SITE_LIBRARY_BEGIN = "<!-- BEGIN GENERATED LIBRARY COMPONENT ROWS -->"
SITE_LIBRARY_END = "<!-- END GENERATED LIBRARY COMPONENT ROWS -->"
SITE_STATUS_BEGIN = "<!-- BEGIN GENERATED PAPER STATUS ROWS -->"
SITE_STATUS_END = "<!-- END GENERATED PAPER STATUS ROWS -->"
GITHUB_MAIN = "https://github.com/nikhgarg/EconCSLib/blob/main/"

STATUS_LABELS = {
    "formalized": "Formalized",
    "formalized with caveat": "Formalized with caveat",
    "partially formalized": "Partially formalized",
    "scaffold": "Scaffold",
    "not started": "Not started",
    "not formalized": "Not formalized",
}

STATUS_GROUPS = {
    "formalized": 0,
    "formalized with caveat": 0,
    "partially formalized": 1,
}

PUBLICATION_OVERRIDES = {
    "DSWG24DiscretizationBias": ("PNAS Nexus, 2025", 2025),
    "GCG24UserItemFairness": ("NeurIPS, 2024", 2024),
    "GGSG19TopThree": ("HCOMP, 2019", 2019),
    "GHW01DigitalGoods": ("SODA, 2001", 2001),
    "GJ18InformativeRatingSystems": ("Manufacturing & Service Operations Management 23(3), 2020", 2020),
    "GN21DriverSurgePricing": ("Management Science, 2022", 2022),
    "GS62CollegeAdmissions": ("American Mathematical Monthly, 1962", 1962),
    "LG21TestOptionalPolicies": ("EAAMO, 2021", 2021),
    "LMMS04FairDivision": ("ACM EC, 2004", 2004),
    "LOS02CombinatorialAuctions": ("Journal of the ACM, 2002", 2002),
    "MBJG25ProducerFairness": ("ICWSM, 2025", 2025),
    "MSVV07AdWords": ("Journal of the ACM, 2007", 2007),
    "PRPKG24AccuracyDiversity": ("WWW '24 / The ACM Web Conference, 2024", 2024),
    "Roth82StableMatching": ("Mathematics of Operations Research, 1982", 1982),
}

SOURCE_URL_OVERRIDES = {
    "DSWG24DiscretizationBias": "https://arxiv.org/pdf/2405.16762",
    "GCG24UserItemFairness": "https://openreview.net/pdf?id=ZOZjMs3JTs",
    "GGSG19TopThree": "https://arxiv.org/abs/1906.08160",
    "GHW01DigitalGoods": "https://www.cs.miami.edu/home/burt/learning/Csc597.052/docs/goldberg.pdf",
    "GJ18InformativeRatingSystems": "https://doi.org/10.1287/msom.2020.0921",
    "GN21DriverSurgePricing": "https://arxiv.org/pdf/1905.07544",
    "GS62CollegeAdmissions": "http://www.jstor.org/stable/2312726",
    "LG21TestOptionalPolicies": "https://arxiv.org/pdf/2107.08922",
    "LMMS04FairDivision": "https://www.cs.cmu.edu/~arielpro/15896s15/docs/paper12a.pdf",
    "LOS02CombinatorialAuctions": "https://jmvidal.cse.sc.edu/library/lehmann02a.pdf",
    "MBJG25ProducerFairness": "https://arxiv.org/pdf/2207.04369",
    "MSVV07AdWords": "https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf",
    "PRPKG24AccuracyDiversity": "https://arxiv.org/abs/2307.15142",
    "Roth82StableMatching": "https://pubsonline.informs.org/doi/epdf/10.1287/moor.7.4.617",
}

README_TITLE_OVERRIDES = {
    "MSVV07AdWords": "MSVV07 AdWords",
}

LIBRARY_COMPONENTS = [
    {
        "title": "Foundations: finite math and graph tools",
        "paths": [
            "EconCSLib/Foundations/Math",
            "EconCSLib/Foundations/Graph",
        ],
        "examples": (
            "Finite-sum rewrites, order/rank lemmas, threshold and interval "
            "characterizations, asymptotic/exponential estimates, and cycle "
            "extraction in finite directed graphs."
        ),
        "papers": [
            "DSWG24DiscretizationBias",
            "LMMS04FairDivision",
            "GN21DriverSurgePricing",
            "LG21TestOptionalPolicies",
        ],
    },
    {
        "title": "Foundations: probability and stochastic processes",
        "paths": ["EconCSLib/Foundations/Probability"],
        "examples": (
            "Finite distributions, conditional expectations, kernels, atom "
            "and variance lemmas, Gaussian and exponential calculations, "
            "stochastic dominance, Markov chains, MDPs, CTMCs, and "
            "renewal-reward identities."
        ),
        "papers": [
            "DSWG24DiscretizationBias",
            "MBJG25ProducerFairness",
            "LMMS04FairDivision",
            "GN21DriverSurgePricing",
            "LG21TestOptionalPolicies",
            "GGSG19TopThree",
            "GJ18InformativeRatingSystems",
        ],
    },
    {
        "title": "Foundations: optimization and certificates",
        "paths": ["EconCSLib/Foundations/Optimization"],
        "examples": (
            "Argmax and endpoint principles, finite-search certificates, "
            "approximation guarantees, linear-program certificates, "
            "binary-choice optimality, move-graph descent, and "
            "choice-equilibrium existence."
        ),
        "papers": [
            "DSWG24DiscretizationBias",
            "MSVV07AdWords",
            "GN21DriverSurgePricing",
            "LG21TestOptionalPolicies",
            "LMMS04FairDivision",
        ],
    },
    {
        "title": "Rating-system applications",
        "paths": [
            "EconCSLib/Foundations/Econometrics/RatingModels",
            "EconCSLib/Learning/Bandits",
        ],
        "examples": (
            "Binary and ordinal signal models, posterior-mean ratings, "
            "bias/variance decompositions, prior-weighted updates, "
            "monotonicity/correction lemmas, and minimal bandit-regret "
            "interfaces."
        ),
        "papers": [
            "MBJG25ProducerFairness",
            "GJ18InformativeRatingSystems",
        ],
    },
    {
        "title": "Matching markets",
        "paths": ["EconCSLib/Markets/Matching"],
        "examples": (
            "Preference profiles, blocking pairs and stable matchings, "
            "deferred-acceptance invariants, proposer incentives, and "
            "many-to-one admissions models."
        ),
        "papers": ["GS62CollegeAdmissions", "Roth82StableMatching"],
    },
    {
        "title": "Auctions and mechanisms",
        "paths": ["EconCSLib/MechanismDesign/Auctions"],
        "examples": (
            "Allocation and payment rules, dominant-strategy truthfulness, "
            "benchmark-competitive digital-goods auctions, VCG-style welfare "
            "maximization, and single-minded set-packing mechanisms."
        ),
        "papers": ["GHW01DigitalGoods", "LOS02CombinatorialAuctions"],
    },
    {
        "title": "Online algorithms and regret",
        "paths": ["EconCSLib/Algorithms/Online"],
        "examples": (
            "Online matching/allocation state machines, primal-dual "
            "accounting, competitive-ratio certificates, regret interfaces, "
            "and platform-learning abstractions."
        ),
        "papers": ["MSVV07AdWords", "MBJG25ProducerFairness"],
    },
    {
        "title": "Complexity abstractions",
        "paths": ["EconCSLib/Algorithms/Complexity"],
        "examples": (
            "Decision/search problem interfaces, reductions, NP/ZPP-style "
            "class consequences, Yao-style minimax wrappers, and explicit "
            "external-solver assumptions."
        ),
        "papers": [
            "LOS02CombinatorialAuctions",
            "MSVV07AdWords",
            "LMMS04FairDivision",
        ],
    },
    {
        "title": "Applications: recommender systems",
        "paths": ["EconCSLib/Applications/RecommenderSystems"],
        "examples": (
            "Exposure and allocation policies, classwise fairness "
            "constraints, top-k recommendation surfaces, policy averaging, "
            "and accuracy/diversity trade-off statements."
        ),
        "papers": ["GCG24UserItemFairness"],
    },
    {
        "title": "Social choice, rankings, and fair division",
        "paths": ["EconCSLib/SocialChoice"],
        "examples": (
            "Ranking profiles, Kendall distance and Mallows-style sequential "
            "ranking models, score/payoff interfaces, envy graphs, "
            "bounded-envy allocations, and indivisible-goods fairness "
            "statements."
        ),
        "papers": ["LMMS04FairDivision", "GGSG19TopThree"],
    },
]


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


def paper_records() -> list[tuple[Path, dict[str, Any]]]:
    return [(folder, load_paper_status(folder)) for folder in paper_dirs()]


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
            "in ProofInterface.lean or implementation modules."
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


def llm_translation_label_from_counts(
    *,
    total: int,
    matches: int,
    mismatch: int = 0,
    uncertain: int = 0,
    unknown: int = 0,
    missing: int = 0,
    stale: int = 0,
) -> str:
    if total <= 0:
        return "not run"
    if not any([matches, mismatch, uncertain, unknown, stale]) and missing >= total:
        return "not run"
    parts = [f"{matches}/{total} match"]
    if mismatch:
        parts.append(f"{mismatch} mismatch")
    if uncertain:
        parts.append(f"{uncertain} uncertain")
    if unknown:
        parts.append(f"{unknown} unknown")
    if missing:
        parts.append(f"{missing} missing")
    if stale:
        parts.append(f"{stale} stale")
    return "; ".join(parts)


def llm_translation_label(folder: Path, payload: dict[str, Any]) -> str:
    if review_dashboard is not None:
        try:
            cached = review_dashboard.load_cached_review_rows(folder)
            if cached is not None:
                summary = review_dashboard.statement_translation_audit_summary(folder, cached)
                return llm_translation_label_from_counts(
                    total=int(summary.get("row_count", 0)),
                    matches=int(summary.get("matches", 0)),
                    mismatch=int(summary.get("mismatch_count", 0)),
                    uncertain=int(summary.get("uncertain_count", 0)),
                    unknown=int(summary.get("unknown_count", 0)),
                    missing=int(summary.get("missing_judgment_count", 0)),
                    stale=int(summary.get("stale_judgment_count", 0)),
                )
        except Exception:
            pass

    review_surface = payload.get("review_surface", {})
    include_names = review_surface.get("include_names") if isinstance(review_surface, dict) else None
    names = [str(name).strip() for name in include_names if str(name).strip()] if isinstance(include_names, list) else []
    judgments = load_llm_statement_judgments(folder)
    if not names:
        total = int(payload.get("human_review", {}).get("total_rows", 0))
        names = list(judgments)
    else:
        total = len(names)
    if not judgments:
        return "not run"

    matches = mismatch = uncertain = unknown = missing = 0
    for name in names:
        judgment = judgments.get(name)
        if judgment is None:
            missing += 1
            continue
        value = normalize_llm_judgment(judgment.get("judgment") or judgment.get("matches"))
        if value == "matches":
            matches += 1
        elif value == "mismatch":
            mismatch += 1
        elif value == "uncertain":
            uncertain += 1
        else:
            unknown += 1

    return llm_translation_label_from_counts(
        total=total,
        matches=matches,
        mismatch=mismatch,
        uncertain=uncertain,
        unknown=unknown,
        missing=missing,
    )


def lean_loc(folder: Path) -> int:
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


def human_status_rows(records: list[tuple[Path, dict[str, Any]]]) -> list[dict[str, Any]]:
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
            "llm_as_judge_translation": llm_translation_label(folder, payload),
            "lean_loc": lean_loc(folder),
            "main_note": human_note(payload),
            "main_note_citation": note_citation(payload),
            "main_note_review": human_summary_review(payload),
            "paper_folder": str(folder.relative_to(ROOT)),
            "review_entrypoint": payload["review_entrypoint"],
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


def human_payload(records: list[tuple[Path, dict[str, Any]]]) -> dict[str, Any]:
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
            "flags when available."
        ),
        "identifier_policy": (
            "Paper IDs and folder names are stable artifact identifiers and may track an arXiv, "
            "conference, or original working-paper year. Publication fields use the published "
            "citation title and year."
        ),
        "papers": human_status_rows(records),
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


def readme_paper_label(paper_id: str) -> str:
    override = README_TITLE_OVERRIDES.get(paper_id)
    if override is not None:
        return override
    for index, char in enumerate(paper_id):
        if char.isdigit():
            prefix = paper_id[: index + 2]
            descriptor = paper_id[index + 2 :]
            if descriptor:
                words = []
                word = descriptor[0]
                for current, following in zip(descriptor[1:], descriptor[2:] + " "):
                    if current.isupper() and (not word[-1].isupper() or following.islower()):
                        words.append(word)
                        word = current
                    else:
                        word += current
                words.append(word)
                return f"{prefix} {' '.join(words)}"
    return paper_id


def readme_note(payload: dict[str, Any]) -> str:
    return md_note_with_citation(human_note(payload), note_citation(payload))


def readme_interface_label(payload: dict[str, Any]) -> str:
    interface = payload.get("paper_interface", {})
    line_count = interface.get("line_count")
    if not isinstance(line_count, int):
        return "Unknown"
    if interface.get("oversized"):
        return f"Debt: {line_count} lines"
    return f"OK: {line_count} lines"


def render_readme_status_block(records: list[tuple[Path, dict[str, Any]]]) -> str:
    by_id = {payload["id"]: payload for _folder, payload in records}
    lines = [
        README_STATUS_BEGIN,
        "| Paper | Status | Human review | PaperInterface size | Public note |",
        "|---|---:|---:|---:|---|",
    ]
    for row in human_status_rows(records):
        payload = by_id[row["id"]]
        paper_link = f"[{readme_paper_label(str(row['id']))}]({row['paper_folder']})"
        lines.append(
            "| "
            + " | ".join(
                [
                    paper_link,
                    md_escape(row["status"]),
                    md_escape(row["human_review"]),
                    readme_interface_label(payload),
                    md_escape(readme_note(payload)),
                ]
            )
            + " |"
        )
    lines.append(README_STATUS_END)
    return "\n".join(lines)


def render_readme(records: list[tuple[Path, dict[str, Any]]]) -> str:
    current = README.read_text(encoding="utf-8")
    start = current.find(README_STATUS_BEGIN)
    end = current.find(README_STATUS_END)
    if start < 0 or end < 0 or end < start:
        raise ValueError(
            f"{README.relative_to(ROOT)} should contain generated status markers "
            f"{README_STATUS_BEGIN!r} and {README_STATUS_END!r}"
        )
    end += len(README_STATUS_END)
    return current[:start] + render_readme_status_block(records) + current[end:]


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
        "| Paper, authors, publication | Status | Human review | Lean LOC | Public note |",
        "|---|---|---:|---:|---|",
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


def render_site_status_block(payload: dict[str, Any]) -> str:
    indent = " " * 14
    lines = [f"{indent}{SITE_STATUS_BEGIN}"]
    for row in payload["papers"]:
        paper_href = row["source_url"] or github_link(row["paper_folder"])
        status_href = github_link(row["review_entrypoint"])
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
                (
                    f'{indent}  <td><a href="{html_escape(status_href)}">'
                    f"{html_escape(row['status'])}</a></td>"
                ),
                f"{indent}  <td>{int(row['lean_loc']):,}</td>",
                f"{indent}  <td>{note}</td>",
                f"{indent}  <td>{html_escape(row['human_translation'])}</td>",
                f"{indent}  <td>{html_escape(row['llm_as_judge_translation'])}</td>",
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if generated status files are out of sync")
    args = parser.parse_args()

    records = paper_records()
    aggregate = aggregate_payload(records)
    human = human_payload(records)
    outputs = {
        AGGREGATE_STATUS: json.dumps(aggregate, indent=2, ensure_ascii=False) + "\n",
        HUMAN_STATUS: json.dumps(human, indent=2, ensure_ascii=False) + "\n",
        DOCS_PAPER_STATUS: render_paper_status_md(human),
        README: render_readme(records),
        SITE_INDEX: render_site_index(human),
    }
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
        path.write_text(rendered, encoding="utf-8")
        print(f"wrote {path.relative_to(ROOT)} from paper-local status files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
