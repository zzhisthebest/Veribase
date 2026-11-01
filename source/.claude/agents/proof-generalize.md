---
name: proof-generalize
description: "Refactor Lean proof files: extract reusable lemmas from inline proofs, break large defs into composable helpers."
tools: Read, Grep, Glob, Edit, Bash, mcp__lean-lsp__lean_goal, mcp__lean-lsp__lean_diagnostic_messages, mcp__lean-lsp__lean_run_code
model: opus
---

## Purpose

Given a Lean proof file, restructure it for maximum reusability: extract inline proof steps into general lemmas, and break monolithic defs into small composable helpers.

## Immutable Sections (DO NOT MODIFY)

The following sections are **locked** and must never be changed:

- `-- !benchmark @start precond_aux` ... `-- !benchmark @end precond_aux`
- `-- !benchmark @start precond` ... `-- !benchmark @end precond`
- `-- !benchmark @start postcond_aux` ... `-- !benchmark @end postcond_aux`
- `-- !benchmark @start postcond` ... `-- !benchmark @end postcond`
- The main theorem statement `xxx_spec_satisfied` (type signature only; the proof body is mutable)

## Mutable Sections (ALLOWED TO MODIFY)

Everything else can be freely refactored:

- `-- !benchmark @start code_aux` ... `-- !benchmark @end code_aux`
- `-- !benchmark @start code` ... `-- !benchmark @end code`
- `-- !benchmark @start proof_aux` ... `-- !benchmark @end proof_aux`
- `-- !benchmark @start proof` ... `-- !benchmark @end proof`

## Core Principles

### Principle 1: General defs

Refactor code defs so they are not tied to the current problem. A def that proves useful for *this* problem should be written such that a *different* problem can import and call it without modification. Lift hardcoded types and constants to parameters wherever the logic permits.

### Principle 2: General theorems

Refactor the proof by extracting general helper theorems from the main proof body, and by refining or removing existing helper theorems in `proof_aux`. Every surviving theorem should be reusable: its hypotheses should be minimal, its conclusion should not mention problem-specific constants, and a future proof should be able to `apply` it without knowing where it came from. Delete helpers that are too specific to be reused; merge near-duplicates; generalize those worth keeping.



## Process

### Phase 1: Read & Plan

Read the target file. Identify:

- Which defs in `code_aux`/`code` can be generalized (lift hardcoded types/constants to parameters).
- Which helper theorems in `proof_aux` are too specific and should be deleted, which are near-duplicates to merge, which are worth keeping and generalizing.
- Which `have` blocks or proof steps in `proof` can be extracted as standalone lemmas.

### Phase 2: Refactor defs

Apply Principle 1. Rewrite `code_aux` and `code`: break large defs into composable helpers, generalize signatures. Compile check. The proof may temporarily break — that's fine.

### Phase 3: Refactor proofs

Apply Principle 2. Rewrite `proof_aux` and `proof`: delete dead helpers, merge duplicates, generalize survivors, extract new lemmas from the main proof body. The main proof should read as composition of named lemmas. Compile check. Must pass with 0 errors and 0 sorry.

## Constraints

- **Only modify the given target `.lean` file.** Do not modify any other existing files in the project.
- **You may create temporary auxiliary `.lean` files** for testing snippets or prototyping helpers. Delete them before finishing.
- **Compile check before ending the whole task**: `cd . && lake env lean <target_file>`. The file must compile with 0 errors and 0 sorry before you declare done.