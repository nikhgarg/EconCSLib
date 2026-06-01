# Private Development Workflow

This repository is the private development counterpart to the public
`nikhgarg/EconCSLib` repository.

## Repository Layout

- `nikhgarg/EconCSLib`: public repository and public PR target.
- `nikhgarg/EconCSLib-private`: private development repository, with history
  based on public `main`.
- `nikhgarg/EconCSLib-private-archive-20260601`: archived copy of the old
  standalone private repository history.

Local remotes should use these names:

```bash
git remote add public https://github.com/nikhgarg/EconCSLib.git
git remote add archive https://github.com/nikhgarg/EconCSLib-private-archive-20260601.git
```

`origin` should point at `https://github.com/nikhgarg/EconCSLib-private.git`.

## Sync Rule

Keep private work based on public history. Before starting or publishing private
paper work:

```bash
git fetch public origin
git switch main
git rebase public/main
git push --force-with-lease origin main
```

Use `git merge-base --is-ancestor public/main HEAD` to confirm public `main` is
an ancestor of the private branch.

## Paper Branches

Develop each private paper on a topic branch forked from current public `main`:

```bash
git fetch public
git switch -c private/<PaperName> public/main
```

Keep each paper branch scoped to:

- `papers/<PaperName>/`
- `papers/<PaperName>.lean`
- the paper's `status.json`
- any reusable library files required by the paper
- minimal docs or workflow updates needed for review

When the paper is ready for public review, push a public branch and open a PR
against `nikhgarg/EconCSLib:main`:

```bash
git push public HEAD:refs/heads/release/<PaperName>
```

The PR should be clean because the branch shares public ancestry and carries
only the paper-ready delta.

## Machine-Readable Status

Every paper folder, public or private, owns its status in
`papers/<PaperName>/status.json`. After editing status metadata, regenerate the
aggregate:

```bash
python3 scripts/sync_paper_status.py
```

The aggregate `papers/status.json` is generated. README tables, dashboards,
and future site generation should read from the paper-local JSON files or the
generated aggregate rather than maintaining separate status logic.
