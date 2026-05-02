# Theorem Ergonomics and Front-Facing Declaration Standards

These conventions are for all source-specific wrappers and reusable declarations
that will be inspected by humans first, and Lean second.

## 1) Paper-facing declaration shape

For `MainTheorems.lean`-style files:

- State source definitions and statement wrappers in the same order as the paper
  text.
- Keep source notation explicit, even when generic wrappers exist in `EconCSLib`.
- Prefer source names in docstrings and comments:
  - “Lemma X”, “Theorem 3.1”, “Proposition A”, etc.
- Keep each source item anchored by a concrete declaration with a stable name.
- If a declaration is scaffold-only, name it clearly as placeholder and keep its
  status as `scaffold` / `not started`.

## 2) Declaration quality bar

- Use `## Main declarations` in module docstrings for every paper-facing ledger
  and reusable `EconCSLib` module.
- Place all assumptions on theorem arguments, not in informal side comments.
- Keep theorem names in `snake_case` in reusable modules and avoid paper-identifer
  prefixes there.
- Keep wrappers for source theorems in source order and use a clear section split:
  definitions → lemmas/corollaries → main theorems.

## 3) Status protocol

- Do not mark a ledger row `formalized` unless:
  - declaration exists,
  - assumptions list is `None` (or `None; <paper assumptions>`),
  - and the proof route is source-faithful.
- Use `formalized with caveat` for statement or proof-route deviations that are
  fully explicit.
- Use `conditional` only when an unresolved hypothesis or bridge is required.
- Reserve `scaffold` / `not started` rows for placeholders.

## 4) Visual DAG protocol

For each paper DAG:

- Keep the metadata block at the top of the figure.
- Keep paper nodes on grid points to make visual inspections fast.
- If you change layout, re-render and inspect a rendered image before merging.
- Do not encode proof debt only in node labels; use status text in README table too.

## 5) Quick human verification loop

Before claiming progress:

1. Update `DependencyDAG.tex` for topology.
2. Update `MainTheorems.lean` source wrappers.
3. Update `README.md` theorem table with matching declaration names.
4. Compile the paper folder and the shared `smoke check` file.
5. Run the repository audit with strict style when declarations are finalized.

## 6) Reusable declaration discoverability

- Keep library-style theorem names short, snake_case, and grouped by intent:
  - `..._mono`, `..._eq`, `..._iff`, `..._of_...`, `..._implies_...`.
- Keep paper-logic wrappers in paper folders and generic helpers in `EconCSLib/`.
- Add one-line comments when a theorem is a convenience shell over a lower-level
  lemma so downstream users know where to inspect proof details.

## 7) Human verification checklist

- For each new reusable theorem set, add a one-line `#check` in
  `examples/SmokeChecks.lean` (or a nearby sibling file) with the target name.
- Add a matching import path check in `scripts/check_smoke.py` when the module
  is added as part of a new user-facing API surface.
- Keep each paper folder metadata/lemma declaration pair next to each other in
  review order so a human can verify the semantic meaning before reading proofs.
