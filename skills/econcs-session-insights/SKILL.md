---
name: econcs-session-insights
description: Mine Codex session traces for recurring EconCSLib workflow lessons, preserve provenance for user feedback, and promote durable rules into the operational skills without creating a parallel formalization rulebook. Use when asked to review past sessions, distill process insights, update skills from repeated mistakes, or apply a Skill-DISCO-style trace-to-skill workflow to EconCSLib work.
---

# EconCS Session Insights

Credit: this skill adapts the trace-distillation idea from Guo, Qi, Gu,
Cheng, and Xiong, *SKILL-DISCO: Distilling and Compiling Agent Traces into
Reusable Procedural Skills*, arXiv:2606.26669v1. Their framework normalizes
successful agent traces, clusters repeated procedural structure, and compiles
the stable patterns into reusable skills; this file applies that idea to
EconCSLib formalization sessions.

Use this skill to turn prior Codex sessions into concise, reusable procedural
guidance for EconCSLib formalization work. The goal is not to preserve history.
The goal is to find repeated execution patterns, repeated user corrections, and
stable cross-paper rules that should affect future agents.

## Trace Distillation Workflow

1. Start from `~/.codex/history.jsonl`.
   - First read the `Last reviewed through` timestamp in
     `references/user-feedback-course-corrections.md`.
   - For routine updates, inspect only history rows and raw session turns after
     that timestamp. Do a full backfill only when the user asks for one or the
     ledger is missing/corrupt.
   - Treat it as the high-level successful-trace index: user goals,
     corrections, status checks, and boundary decisions.
   - Group messages by session id and topic before opening raw session files.
   - Do not begin by scanning every raw `~/.codex/sessions/**/*.jsonl` file.
     Session continuations and subagents duplicate long instruction contexts and
     can dominate runtime without adding new procedural signal.

2. Open raw session JSONL files only when needed.
   - Sample sessions that contain repeated correction phrases, failed tools,
     unusual commits, CI fixes, or paper-boundary decisions.
   - Ignore system/developer boilerplate, encrypted reasoning, copied context,
     and repeated continuation payloads.
   - Extract only normalized operations: user directive, repo/paper context,
     action class, files or tools touched, result, and user correction.

3. Segment normalized operations into subgoals.
   Use these default clusters for EconCSLib:
   - proof planning and theorem closure;
   - source-version and TeX/PDF convention checks;
   - assumption/certificate provenance;
   - reusable library elevation;
   - documentation, DAG, status, and audit timing;
   - public/private repository release hygiene;
   - CI/build/runtime environment handling;
   - subagent coordination and handoff boundaries.

   For the current distilled course-correction ledger, see
   `references/user-feedback-course-corrections.md`. Load it when the task asks
   specifically about prior user feedback, repeated corrections, or process
   hardening from session history.

4. Consolidate only repeated lessons.
   A candidate insight is skill-worthy when it appears in at least two sessions,
   affects at least two papers, or corrects a serious workflow failure. Do not
   add one-off paper notation, temporary proof names, or paper-local strategy
   details to a general skill.

5. Compile insights into the narrowest appropriate skill file.
   - Main workflow rules go in `skills/econcs-formalizer/SKILL.md`.
   - Math-domain proof tactics go in the relevant reference file under
     `skills/econcs-formalizer/references/`.
   - Public-release rules go in the public/release workflow guidance.
   - If the insight is still experimental, put it in a separate draft skill like
     this one for review before merging.

6. Validate the skill update.
   - Keep the patch concise and grep for accidental paper-specific names.
   - Check that the new instruction is actionable, not just retrospective.
   - Update the `Last reviewed through` timestamp to the newest processed
     session/history timestamp only after the promoted rules and ledger edits are
     written.
   - Do not commit generated transcript summaries or text caches unless the
     user explicitly asked for them.

## Promotion Destinations

This skill is a provenance and maintenance layer, not a day-to-day paper
formalization rulebook. Durable lessons should be promoted into the narrowest
operational destination:

- `skills/econcs-formalizer/SKILL.md` for active paper formalization workflow,
  source provenance, audits, documentation timing, public/private repo hygiene,
  and subagent use.
- `skills/econcs-formalizer/references/proof-*.md` for math-domain tactics,
  theorem patterns, and reusable proof routes.
- `skills/lean-community-conventions/SKILL.md` for Lean naming, style,
  documentation, and proof-claim gate conventions.
- Paper-local planning or audit files for paper-specific notation, source
  deviations, and temporary proof strategy.

The current feedback ledger lives in
`references/user-feedback-course-corrections.md`. Load it only when a task asks
to mine prior sessions, explain the origin of a process rule, or update skills
from repeated feedback.

## Applying Insights Back to Skills

When merging a draft insight into an operational skill:

1. Rewrite it as a short command or checklist item.
2. Remove references to the session that taught the lesson.
3. Remove paper-specific notation unless the destination is a paper-specific
   reference.
4. Put math-specific proof content in the relevant proof reference, not the main
   workflow skill.
5. Delete or demote any duplicate rule from this session-insights skill once it
   has been promoted.
