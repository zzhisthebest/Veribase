---
name: codegen-prover
description: "Generate both code implementation and correctness proof from a formal specification. For the wake-sleep pipeline."
tools: Read, Grep, Glob, Edit, Bash, mcp__lean-lsp__lean_goal, mcp__lean-lsp__lean_local_search, mcp__lean-lsp__lean_leanfinder, mcp__lean-lsp__lean_leansearch, mcp__lean-lsp__lean_loogle, mcp__lean-lsp__lean_multi_attempt, mcp__lean-lsp__lean_diagnostic_messages, mcp__lean-lsp__lean_run_code
model: inherit
---

## Purpose

Given a Lean 4 file with a formal specification (precondition + postcondition) and sorry placeholders for both code and proof, fill in:
1. **Code implementation** — the function body that satisfies the spec
2. **Correctness proof** — a formal proof that the implementation meets the postcondition

## Inputs

- Target file path (a spec-only lean file with sorry in code and proof sections)
- Natural language problem description

## Sections in the Target File

The file uses benchmark markers to delimit sections:

```
-- !benchmark @start code_aux     ← Helper definitions for your implementation (you fill)
-- !benchmark @end code_aux

def funcName (...) :=
  -- !benchmark @start code       ← Main implementation (you fill)
  sorry
  -- !benchmark @end code

-- !benchmark @start proof_aux    ← Helper lemmas for your proof (you fill)
-- !benchmark @end proof_aux

theorem funcName_spec_satisfied (...) := by
  -- !benchmark @start proof      ← Correctness proof (you fill)
  sorry
  -- !benchmark @end proof
```

**DO NOT MODIFY** these sections (they are the specification — treat as read-only):
- `precond` / `precond_aux` — precondition
- `postcond` / `postcond_aux` — postcondition
- `import` — except you may add imports
- Function signature line (name, parameters, return type)
- Theorem statement (everything before `:= by`)

**DO NOT MODIFY THE TEST ENVIRONMENT.** Do not change any files, directories,
permissions, dependencies, build configuration, cache directories, scripts, or
environment settings outside the target Lean task file. The current test
environment must remain unchanged.

## TPL: preferred theorem library

**Before searching mathlib, search TPL.** TPL (`./TPL/`) is a local library of reusable definitions and theorems for program-verification proofs.
General (`./TPL/`, excluding `./TPL/Specific/`) provides broadly reusable definitions and theorems, whereas Specific (`./TPL/Specific/`) is harvested from tasks drawn from the same distribution as the target benchmark and may provide more directly applicable declarations. Do not assume in advance that either one is more effective.

**Core principle: use TPL actively, but keep retrieval focused and bounded.**
Always search TPL for reusable definitions and theorems before solving a goal
from scratch, and inspect genuinely promising matches carefully. However, TPL
retrieval should support the proof rather than dominate it. If a small number of
focused searches yields no clearly applicable declaration, proceed with mathlib
or a direct solution instead of browsing TPL broadly or repeatedly trying weakly
related results.

**Rules:**

1. **`import TPL` should already be in the file.** If not, add it.
2. **Search order**: TPL → mathlib. Never reimplement something TPL already provides.
3. **If TPL has a definition that fits your implementation, USE IT.** This is the key advantage — TPL theorems about that definition are then directly applicable to your proof.
4. **Discovery is retrieval-first.** Before scanning source files, query the TPL
   declaration index with a short natural-language description of the current
   operation or proof fact:
   ```
   python ./scripts/search_tpl.py \
     "select a minimum element by a measure with tie breaking" --kind def

   python ./scripts/search_tpl.py \
     "selected element belongs to the input and has minimum measure" --kind theorem
   ```
   The output includes exact declarations, types, modules, documentation, and
   a small theorem family for each matched definition. After retrieval, inspect only the returned modules with
   `Grep`/`Read`. For the same operation or proof goal, make at most two focused
   retrieval attempts. If neither returns a suitable declaration, stop searching
   TPL for that goal and continue with mathlib or a direct solution; do not replace
   the failed retrieval with a broad scan of the TPL source tree. This limit is
   per goal, not per file: a later, independent subgoal may start a new search.
5. **Do not modify TPL and TPL.lean.** 

## Strategy

### Phase 1: Understand the Specification

1. Read the target file: understand precond, postcond, function signature, return type.
2. Read the NL description for intent and edge cases. **Strictly follow all constraints in the description, including time/space complexity requirements.** Choose your algorithm accordingly before writing any code.
3. If postcond references aux definitions (in `postcond_aux`), read those carefully — your implementation must satisfy them.

### Phase 2: Search TPL for Reusable Components

1. Identify the underlying operations independently of task-specific names (for
   example: sort, argmin with tie-breaking, enumerate index pairs, or fold a maximum).
2. Run at least one focused retrieval query for matching definitions:
   ```
   python ./scripts/search_tpl.py \
     "<description of the required operation>" --kind def
   ```
3. Inspect the source module reported for promising results and check that the
   complete signature and semantics fit the task.
4. If a TPL definition matches, plan to use it in your implementation together
   with its retrieved theorem family.

### Phase 3: Write the Implementation

1. Write helper definitions in `code_aux` if needed (recursive helpers, data structures).
2. Write the main function body in `code` section.
3. **Modularity**: Extract reusable logic into named definitions in `code_aux` rather than inlining everything in `code`. For example, a recursive helper, a `foldl`-based aggregation, or a filtering step should each be its own `def` in `code_aux`, with the main `code` section composing them. This makes helpers independently extractable to TPL later.
4. **Compile check** after writing code (proof is still sorry):
   ```
   lean_diagnostic_messages(file)
   ```
   Code must type-check (return type must match). The sorry in proof is expected.

### Phase 4: Write the Proof

1. Use `lean_goal` to see what needs to be proved after unfolding.
2. Run a second focused retrieval query describing the current conclusion and
   its important hypotheses, using `--kind theorem`, then inspect the returned modules.
3. Write helper lemmas in `proof_aux` if needed (loop invariants, induction lemmas).
4. **Modularity**: Extract intermediate proof steps as named `theorem`/`lemma` in `proof_aux` rather than burying them as `have` blocks inside the main proof. A standalone lemma like `myHelper_mono (l : List Nat) : ...` is reusable; a `have` buried in the proof body is not. The main `proof` section should read as a composition of named lemmas.
5. Write the main proof in `proof` section.
6. **Compile check** — file must have NO errors and NO remaining sorry:
   ```
   lean_diagnostic_messages(file)
   ```

### Phase 5: Validate (MANDATORY — DO NOT EXIT UNTIL THIS PASSES)

1. Run full file compilation:
   ```bash
   cd . && lake env lean <target_file> 2>&1
   ```
2. Check for errors (sorry warnings are failures — all sorry must be eliminated).
3. **CRITICAL: If ANY errors or sorry remain, you MUST fix them and re-validate. You are NOT allowed to exit until `lake env lean <file>` returns exit code 0 with zero "sorry" warnings.**
4. Fix loop: diagnose errors via `lean_diagnostic_messages`, fix the issue, re-run `lake env lean`. Repeat until clean.
5. If proof is stuck after multiple fix attempts, reconsider your implementation — a complex `code` often leads to an unprovable proof. Simplify or restructure `code`/`code_aux` to make the proof easier, then reprove.
   **Avoid getting trapped in repeated local repairs. If the current approach
   stops making meaningful progress, step back promptly and switch to a simpler
   implementation or proof strategy.**
6. If you fundamentally cannot solve the problem, state that explicitly — do NOT pretend success.

## Output

After Phase 5 passes (0 errors, 0 sorry), stop immediately and return exactly
`done`. Do not generate a summary, report, explanation, recap, or list of used
TPL declarations. The validated target file is the only required output.

## Constraints

- **CRITICAL: DO NOT modify files other than the target task.lean and test files you create.** You may ONLY:
  - Edit the target `task.lean` file (the one specified in the prompt)
  - Create and edit temporary test `.lean` files (delete them before finishing)
  - **NEVER modify TPL.lean, TPL/ files, other task files, config files, lakefile.lean, or any other project files.** Modifying anything beyond the target file is strictly forbidden and will corrupt the benchmark.
- **DO NOT modify spec sections** (precond, postcond, postcond_aux, precond_aux)
- **DO NOT modify the function signature** (name, parameters, return type)
- **DO NOT modify the theorem statement** (everything before `:= by`)
- **CRITICAL: NEVER add `axiom`, `constant`, or any other unproved assumption.** Do not encode a guarantee from the natural-language description as an axiom when it is absent from the Lean precondition. If the theorem cannot be proved from the declarations and hypotheses already present in the task, report failure instead of introducing an assumption.
- **DO NOT use sorry** in the final result (including in helpers)
- **DO NOT read existing Lean files outside the task** — you may only read: (1) the target task file, (2) TPL library files in `./TPL/`, (3) TPL's generated declaration index through `./scripts/search_tpl.py`, and (4) Mathlib and standard library files that Lean resolves via `import`. You may NEVER read other task files, existing proof files, benchmark results, or any other `.lean` files in the project.
- **Test files**: you may create temporary `.lean` files for testing snippets, but MUST delete them before finishing.
- **Validate after every phase**: `lean_diagnostic_messages` after each edit
- Follow mathlib 100-char line width
- Keep helper lemmas minimal and well-named
