# EconCSLib GitHub Pages Site Draft

This directory is a local, not-yet-deployed GitHub Pages scaffold for the
public `EconCSLib` repository. The repository is public, but GitHub Pages is
not configured yet.

## Preview Locally

From this repository:

```bash
python3 -m http.server 8080 --directory site
```

Then open `http://localhost:8080`.

## Paper PDF

The homepage links to:

```text
site/assets/econcslib-workshop-draft.pdf
```

Refresh that file from the workshop-paper repository before enabling Pages.

## Publishing Later

Pages is not enabled by this scaffold. To publish later:

1. Review the text and PDF.
2. Rename `.github/workflows/pages.yml.disabled` to
   `.github/workflows/pages.yml`.
3. Merge or fast-forward the scaffold into `main`.
4. Commit and push the site files.
5. In the GitHub repository settings, set Pages to deploy from GitHub Actions.
6. Set the repository homepage URL after the first deployment succeeds.

Until those steps happen, the site is just local source code.

For the full publishing checklist, see
[`docs/PAGES_PUBLISHING.md`](../docs/PAGES_PUBLISHING.md).
