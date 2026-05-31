# GitHub Pages Publishing Plan

This document records how to publish the project site when the paper and public
repository are ready.

## Current State

- The draft site lives on the local `pages-scaffold` branch under `site/`.
- The workflow file is intentionally disabled as
  `.github/workflows/pages.yml.disabled`.
- GitHub Pages is not enabled by this scaffold.
- The current draft paper PDF is checked in at
  `site/assets/econcslib-workshop-draft.pdf`.

## Before Publishing

1. Rebuild the workshop paper PDF in `../2026_EconCSLibpaper`.
2. Copy the latest PDF into `site/assets/econcslib-workshop-draft.pdf`.
3. Review `site/index.html` for accurate paper status and contact text.
4. Confirm `docs/PAPER_STATUS.md` matches the site status table.
5. Rename `.github/workflows/pages.yml.disabled` to
   `.github/workflows/pages.yml`.
6. Push the branch or merge it into `main`.
7. In GitHub repository settings, set Pages to deploy from GitHub Actions.

## Updating After Publication

Treat the site as a summary layer. The source of truth remains:

- `README.md` for the public repository overview;
- `docs/PAPER_STATUS.md` for paper-level status;
- paper-local `FINAL_VALIDATION_REPORT.md` files for detailed caveats; and
- `CONTRIBUTING.md` for the contribution policy.

When a paper status changes, update those files first, then update the site.
