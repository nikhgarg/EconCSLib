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

## Publishing Later

To publish:

1. Review the site text.
2. Commit and push the site files.
3. Confirm the Pages workflow succeeds.
4. Set the repository homepage URL after the first deployment succeeds.

For the full publishing checklist, see
[`docs/PAGES_PUBLISHING.md`](../docs/PAGES_PUBLISHING.md).
