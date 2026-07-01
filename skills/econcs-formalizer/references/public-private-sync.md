# Public/Private Repository Sync

Use this reference whenever work has to move between `EconCSLib-private` and
`EconCSLib-public`, or when the user asks to keep both repositories in sync.

## Core Rule

Do a semantic, path-scoped sync. Do not raw-merge the private repository into
the public repository, and do not assume that a Git merge is safe just because
the folder names overlap. The private repo may contain unpublished paper
folders, local source caches, private planning notes, generated status rows for
private papers, and newer experimental audit code. The public repo must contain
only public-safe code, public paper artifacts, public workflow docs, and
generated surfaces regenerated from the public checkout.

## Preventing Divergence

Treat sync as a standing maintenance workflow, not a prompt to publish more
private work. The default direction is that private worktrees incorporate the
public repository after public PRs land, so private development stays based on
the current public library and workflow. Moving work from private to public is a
separate release/contribution decision that should happen only when the user or
maintainer explicitly asks for a public-safe PR.

- Use clean worktrees from remote refs when either checkout is dirty. Do not
  base sync decisions on a stale local working tree; compare `origin/main` and
  `public/main` or freshly pulled `main` refs.
- Keep a source-of-truth map before copying: shared Lean library code, scripts,
  CI, templates, and public-safe skill references should match across repos
  unless there is an explicitly recorded private experiment; generated
  aggregate surfaces are checkout-local; private paper folders, source caches,
  and paper-specific proof notes stay private.
- When a public PR lands, update the private superset promptly unless private
  intentionally has a newer experiment for the same path. This keeps private
  work aligned with the public base without implying that private papers should
  be promoted.
- When a useful private change appears, first ask whether it is intended for a
  public-safe contribution. If not, keep it private. If yes, prepare a narrow
  PR branch against public `main`; contributors should assume they do not have
  push access to public and should use ordinary fork/branch PR mechanics.
- Prefer ref-to-ref checks over visual inspection. After a sync, run direct
  diffs for shared paths such as `EconCSLib/`, `scripts/`, synced docs, synced
  skill references, and public paper folders. Investigate every remaining
  modified (`M`) diff under public paper folders; only private-only deletes,
  checkout-local generated aggregates, and intentionally sanitized skill/docs
  differences should remain.
- If a private skill reference contains useful general guidance plus private
  paper names, copy the idea into the public skill in sanitized form. Do not
  copy the private reference file wholesale unless a leakage scan confirms it
  contains no private paper IDs, private URLs, source-cache paths, or
  non-public planning details.
- Record the outcome in commits/PR bodies: what public changes were reflected
  into private, whether any explicitly requested public-safe contribution was
  prepared, which generated files were regenerated rather than copied, and which
  remaining diffs are intentional.

## Sync Direction

- Public to private: copy public `main` changes that affect shared library code,
  scripts, public-safe skills, templates, CI/workflows, and public paper folders
  into the private checkout unless private has an intentionally newer semantic
  version. Regenerate private aggregate status/site files in the private
  checkout after copying.
- Private to public: do this only for an explicitly requested public-safe
  release or contribution. Start from current public `main` on a branch or fork,
  then copy only allowlisted paths. Use exact paths, not broad `papers/` or
  `skills/` copies. Regenerate public aggregate status/site files in the public
  checkout.
- If both repos changed the same generated artifact, prefer the artifact whose
  inputs are newest and whose validation was run in the checkout that will
  publish it. Do not decide by filename alone.

## Latest-Wins Policy

For public-safe paths, prefer the latest semantically valid artifact:

- Lean source, scripts, and skill references: prefer the newer audited workflow
  or proof code, but check for private-only identifiers before copying to
  public.
- DAG PDFs, validation reports, and generated paper artifacts: use the newest
  version that matches the current paper status and source surface. If a PDF is
  copied, copy its TeX/source input when that input is tracked and public-safe.
- LLM-as-judge sidecars (`audit/lean_to_tex_llm.json`,
  `audit/statement_match_llm.json`, `audit/paper_coverage_llm.json`,
  `audit/assumption_match_llm.json`, `audit/source_record_match_llm.json`): use
  the sidecar that matches the current Lean declarations, current source
  inventory, current prompt version, and current digest fields. A newer
  timestamp is not enough.
- Source records (`audit/source_record_audit.json`,
  `audit/paper_statement_map.json`): use the version generated from the current
  Lean/source inventory. Regenerate when in doubt.
- Aggregate files (`papers/status.json`, `papers/human_status.json`,
  `docs/PAPER_STATUS.md`, `README.md`, `site/index.html`): never copy across
  the public/private boundary. Regenerate them in the destination checkout.

## Source Artifacts

Keep source-paper PDFs, extracted source text, publisher archives, arXiv source
archives, and dashboard caches private or ignored unless redistribution rights
and project policy explicitly allow publication. Public reports should cite the
source URL and, if needed, describe a local ignored cache. Planning, handoff,
audit, and citation-provenance notes written by the project may be tracked when
they do not reproduce source-paper text.

## Cache Discipline

Do not trust a warm checkout for public validation. Ignored
`.review_traces/paper_interface_cache.json` files can make
`review_dashboard.py --statement-check` pass locally while a fresh CI checkout
fails. Before treating sidecars as current:

1. Run `python3 scripts/review_dashboard.py --paper <paper> --refresh-cache`
   in the checkout being validated.
2. Regenerate tracked LLM sidecars from that current review surface if row
   names, Lean statement digests, source statement digests, prompt versions, or
   source-record audit digests changed.
3. Verify from a fresh or cache-free checkout when preparing a public PR that
   touches review sidecars.
4. If local and CI disagree, trust the fresh checkout/CI and inspect ignored
   cache files before editing proof code.

## Safe Copy Procedure

1. Inventory both repos:
   `git status -sb`, `git log --oneline -5`, `git remote -v`, and
   `find papers -maxdepth 1 -type d | sort`.
2. Build a path-level diff by category: shared library, scripts, skills,
   public paper folder, private-only paper folder, DAG/report PDFs, LLM
   sidecars, source caches, and generated aggregate surfaces.
3. For each path, record the chosen direction and reason:
   `public newer`, `private newer`, `destination regenerated`,
   `private-only`, `source-cache private`, or `public-safe PR`.
4. Copy with an explicit path list or `rsync --files-from`, never a broad
   repository-wide copy.
5. Regenerate aggregate status in the destination checkout.
6. Run the relevant validation in the destination checkout:
   `python3 scripts/sync_paper_status.py --check`,
   `python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0`,
   relevant `review_dashboard.py` checks, and targeted `lake build`.
7. Run leakage checks before public commits:
   `git diff --name-only` plus searches for private paper IDs, raw source
   caches, `.review_traces`, `.txt` source extracts, and private planning paths.
8. Commit with explicit pathspecs. For public changes, prepare a PR; do not
   assume direct push access.

## What Not To Do

- Do not raw-merge private `main` into public `main`.
- Do not copy `papers/status.json`, `papers/human_status.json`,
  `docs/PAPER_STATUS.md`, root `README.md`, or `site/index.html` across repos.
- Do not copy `.review_traces` caches, local source PDFs/text, or unpacked
  source archives into public by default.
- Do not keep stale LLM sidecars because a warm local checkout passes.
- Do not resolve conflicts by always choosing `ours` or `theirs`; decide by
  source status, current Lean surface, current audit schema, and public-safety.
