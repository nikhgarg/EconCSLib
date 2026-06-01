# EconCSLib GitHub Pages Site Draft

This directory contains the GitHub Pages source for the public `EconCSLib`
repository. The deployment workflow publishes this directory from `main` and
enables Pages through GitHub Actions on the first successful deployment.

## Preview Locally

From this repository:

```bash
python3 -m http.server 8080 --directory site
```

Then open `http://localhost:8080`.

Before judging the status table, run:

```bash
python3 scripts/sync_paper_status.py --check
```

The table in `site/index.html` should mirror the compact public source
[`papers/human_status.json`](../papers/human_status.json), while
[`papers/status.json`](../papers/status.json) remains the detailed audit
aggregate.

## Publishing Later

To publish:

1. Review the site text.
2. Confirm the status table matches `papers/human_status.json` and
   `docs/PAPER_STATUS.md`.
3. Commit and push the site files.
4. Confirm the Pages workflow succeeds.
5. Set the repository homepage URL after the first deployment succeeds.

For the full publishing checklist, see
[`docs/PAGES_PUBLISHING.md`](../docs/PAGES_PUBLISHING.md).
