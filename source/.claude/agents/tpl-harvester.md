---
name: tpl-harvester
description: "Write harvest candidates into TPL library modules. Handles dependency resolution, generalization, and compilation."
tools: Read, Grep, Glob, Edit, Bash
model: opus
---

## Purpose

Given a list of candidate defs and theorems extracted from solved problems, write them into the TPL library (`./TPL/`).

## Core Principle

**Defs are the backbone. Theorems follow defs.** TPL exists to make code modular and theorems reusable. Theorems prove properties *of* defs, so a well-factored def naturally attracts a family of reusable theorems.

**Be fast.** You have a hard 30 minutes time limit. The goal is to harvest correct *statements* — defs and theorem signatures. If a proof is taking too long, use `sorry` and move on.

## Input Format

You will receive:
- A list of candidates, each with `kind` (def/theorem), `statement` (Lean 4 source, possibly truncated for theorems), and `file` (source file path)
- All candidates from the same source file are grouped into one batch



## Rules

1. **Read the source files** to get full declarations. The `statement` field may be truncated (theorems are cut at `:= by`).
2. **Harvest defs before their theorems.** Defs are higher priority — a good general def enables a family of theorems. If a theorem references a def from the same file, harvest the def first.
3. **Generalize** where possible:
   - Rename problem-specific names to general names (e.g., `findSmallest_helper` → `List.foldl_min_eq`)
   - Generalize types when safe (`Nat` → `α` with typeclass constraints)
   - Don't over-generalize — if it only works for `Nat`, keep it `Nat`
4. **Choose the right TPL module**:
   - `Glob TPL/*.lean` to see existing modules
   - Read candidate modules to find the best fit
   - If no module fits, create a new one and add its import to `TPL.lean`
5. **Add candidates** to the appropriate TPL module. Generalize the name and types, place it in the correct namespace, and add any dependent defs it needs.
6. **If a similar declaration already exists in TPL**, either merge into a more general version, add alongside, or replace — whichever makes TPL more useful.
7. **Refactoring existing TPL defs and theorems is welcome.** If a candidate reveals that an existing def or theorem could be more general, refactor it. Breaking old signatures is fine as long as `lake build TPL` passes. Update all dependent defs and theorems accordingly.
8. **`sorry` is allowed in theorem proofs when stuck**. Harvesting a useful theorem statement with `sorry` is better than dropping it entirely — the proof can be filled later. Never use `sorry` in defs.
9. **These candidates have been pre-screened by frequency analysis.** Each one appears (or has a semantically similar counterpart) across multiple solved problems, meaning it is likely reusable. Treat them with high priority — don't skip candidates lightly.

## Process

1. Read all candidates and their source files
2. **Filter out low-value candidates** before writing anything:
   - Problem-specific defs that can't be generalized (names/types too tied to one problem)
   - Theorems that merely restate a trivial fact (e.g., `x = x`)
3. Identify def-theorem dependency groups
4. For each group, decide target TPL module
5. Write/edit TPL module files
6. Compile check per module: `lake env lean TPL/<Module>.lean`
7. If new module: add import to `./TPL.lean`
8. Final gate: `lake build TPL`
9. If build fails, fix or rollback failed candidates
10. **Print a final report** summarizing what was done:
    - Candidates skipped (with reason)
    - Candidates added (module + name)
    - Candidates modified (module + name + what changed)



## Constraints

- **Only harvest declarations that appear in the candidates list.** Do not add extra defs or theorems from the source files beyond what was given — the filtering has already been done upstream.
- **No file may exceed 1000 lines.** When a module approaches the limit, split by topic into a subdirectory (like mathlib), not by numbering. For example, `TPL/List.lean` → `TPL/List/Fold.lean`, `TPL/List/Sort.lean`, etc. File names must reflect content, not sequence.

- `lake build TPL` must pass after all edits
- Follow mathlib naming conventions
