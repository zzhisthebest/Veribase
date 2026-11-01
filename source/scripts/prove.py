#!/usr/bin/env python3
"""Solve construction tasks over multiple proving rounds.

Usage:
    python scripts/prove.py --dataset construction_tasks --tag construction
    python scripts/prove.py --dataset construction_tasks --tag construction --rounds 3
    python scripts/prove.py --dataset construction_tasks --tag construction --batch-size 5
"""

import argparse, json, subprocess, sys, time, shutil, re, os, signal
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_ROOT = ROOT / "results"

def _cleanup_stale():
    """Kill all lean/lake processes from previous runs.
    VS Code will restart lake serve / lean --server automatically when needed."""
    for sig in [signal.SIGTERM, signal.SIGKILL]:
        subprocess.run(["pkill", "-f", "-u", "anonymous-user", "claude -p"], capture_output=True)
        # kill compile-check lake/lean, skip LSP (--server, --worker, serve)
        subprocess.run(["pkill", "-f", "-u", "anonymous-user", "lake env lean"], capture_output=True)
        subprocess.run(
            f"pgrep -u anonymous-user lean | while read p; do "
            f"  grep -qF -- --server /proc/$p/cmdline 2>/dev/null && continue; "
            f"  grep -qF -- --worker /proc/$p/cmdline 2>/dev/null && continue; "
            f"  kill -{sig} $p 2>/dev/null; "
            f"done", shell=True, capture_output=True)
        subprocess.run(["pkill", "-u", "anonymous-user", "git"], capture_output=True)

def _save_trace(trace_dir, problem, mode, raw_stdout):
    trace_dir.mkdir(parents=True, exist_ok=True)
    (trace_dir / f"{problem}_{mode}.jsonl").write_text(raw_stdout)

def _parse_result(raw_stdout):
    for line in reversed(raw_stdout.strip().split('\n')):
        try:
            evt = json.loads(line)
        except json.JSONDecodeError:
            continue
        if evt.get('type') == 'result':
            usage = evt.get('usage', {})
            tokens = usage.get('input_tokens', 0) + usage.get('output_tokens', 0)
            return {'tokens': tokens, 'cost_usd': evt.get('total_cost_usd', 0) or 0}
    return {'tokens': 0, 'cost_usd': 0}

def load_results(results_file):
    if not results_file.exists():
        return {}
    return json.loads(results_file.read_text())

def save_results(results, results_file):
    results_file.write_text(json.dumps(results, indent=2) + "\n")

def ensure_orig(task_path):
    orig_path = task_path.with_suffix(".lean.orig")
    if not orig_path.exists():
        shutil.copy2(task_path, orig_path)

def restore_from_orig(task_path):
    orig_path = task_path.with_suffix(".lean.orig")
    if orig_path.exists():
        shutil.copy2(orig_path, task_path)

def set_tpl_import(task_path, enable):
    text = task_path.read_text()
    has_import = 'import TPL\n' in text
    if enable and not has_import:
        task_path.write_text('import TPL\n' + text)
    elif not enable and has_import:
        task_path.write_text(text.replace('import TPL\n', ''))

def compile_check(filepath):
    try:
        r = subprocess.run(
            ["lake", "env", "lean", str(filepath)],
            capture_output=True, text=True, cwd=str(ROOT), timeout=300
        )
    except subprocess.TimeoutExpired:
        return False, True
    has_sorry = "declaration uses 'sorry'" in r.stdout
    return r.returncode == 0, has_sorry

def build_prompt(task_path, desc_path, no_tpl=False):
    description = desc_path.read_text() if desc_path.exists() else "(no description)"
    constraint = "\n\n## Constraint\nDo NOT use or import the TPL library." if no_tpl else ""
    return f"""Target file: {task_path}

## Problem Description
{description}{constraint}"""

def run_agent(task_path, desc_path, timeout, mode, trace_dir):
    """Phase 1: run the agent, return raw result. No compile_check."""
    problem = task_path.parent.name
    start_time = time.time()
    if mode == "withTPL":
        prompt = build_prompt(task_path, desc_path, no_tpl=False)
        cmd = ["claude", "-p", prompt,
               "--agent", "codegen-prover",
               "--output-format", "stream-json", "--verbose",
               "--allow-dangerously-skip-permissions"]
    else:
        prompt = build_prompt(task_path, desc_path, no_tpl=True)
        cmd = ["claude", "-p", prompt,
               "--agent", "codegen-baseline",
               "--output-format", "stream-json", "--verbose",
               "--allow-dangerously-skip-permissions"]

    try:
        r = subprocess.run(cmd, capture_output=True, text=True, cwd=str(ROOT), timeout=timeout)
        elapsed = time.time() - start_time
        _save_trace(trace_dir, problem, mode, r.stdout)
        metrics = _parse_result(r.stdout)
        return {"exit": "ok", "elapsed": elapsed, "metrics": metrics,
                "returncode": r.returncode}
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start_time
        return {"exit": "timeout", "elapsed": elapsed}

def run_mode(mode, problems, results, args, dataset_dir, proof_dir, results_file, trace_dir):
    already_proved = {p for p in problems if results.get(p, {}).get(mode, {}).get('status') == 'proved'}
    never_tried = [p for p in problems if mode not in results.get(p, {}) and p not in already_proved]
    retry = [p for p in problems if mode in results.get(p, {}) and p not in already_proved]
    pending = (never_tried + retry)[::-1]
    print(f"\n{'='*60}")
    print(f"Mode: {mode} — {len(pending)} pending / {len(problems)} total")
    print(f"{'='*60}")

    if not pending:
        print("All done.")
        return

    for batch_start in range(0, len(pending), args.batch_size):
        batch = pending[batch_start : batch_start + args.batch_size]
        batch_num = batch_start // args.batch_size + 1
        total_batches = (len(pending) + args.batch_size - 1) // args.batch_size
        print(f"\n── Batch {batch_num}/{total_batches} ({len(batch)} problems) ──")

        for problem in batch:
            task_path = dataset_dir / problem / "task.lean"
            task_path.chmod(0o644)
            restore_from_orig(task_path)
            set_tpl_import(task_path, enable=(mode == "withTPL"))

        # ── Phase 1: run all agents in parallel ──
        raw_results = {}
        with ThreadPoolExecutor(max_workers=args.batch_size) as executor:
            futures = {}
            for problem in batch:
                task_path = dataset_dir / problem / "task.lean"
                desc_path = dataset_dir / problem / "description.txt"
                print(f"  [START] {problem}")
                futures[executor.submit(run_agent, task_path, desc_path, args.timeout, mode, trace_dir)] = problem

            for future in as_completed(futures):
                problem = futures[future]
                raw = future.result()
                raw_results[problem] = raw
                print(f"  [DONE] {problem} ({int(raw['elapsed'])}s)")
                task_path = dataset_dir / problem / "task.lean"
        # ── Phase 2: compile-check in parallel ──
        print(f"\n  ── Phase 2: compile-check ──")
        mode_proof_dir = proof_dir / mode
        mode_proof_dir.mkdir(parents=True, exist_ok=True)

        def check_one(problem):
            raw = raw_results[problem]
            task_path = dataset_dir / problem / "task.lean"
            ok, has_sorry = compile_check(task_path)
            status = "proved" if (ok and not has_sorry) else ("partial" if ok else "failed")
            metrics = raw.get("metrics", {})
            return problem, status, int(raw["elapsed"]), metrics.get("tokens", 0), metrics.get("cost_usd", 0.0)

        with ThreadPoolExecutor(max_workers=args.batch_size) as ex:
            futures = {ex.submit(check_one, p): p for p in batch}
            for future in as_completed(futures):
                problem, status, elapsed, tokens, cost = future.result()
                result = {"status": status, "time_s": elapsed, "tokens": tokens, "cost_usd": cost}
                print(f"  [{result['status'].upper()}] {problem} ({elapsed}s, ${cost:.3f})")
                results.setdefault(problem, {})[mode] = result
                save_results(results, results_file)
                task_path = dataset_dir / problem / "task.lean"
                shutil.copy2(task_path, mode_proof_dir / f"{problem}.lean")
                restore_from_orig(task_path)

def print_comparison(results, modes):
    print(f"\n{'='*60}")
    print(f"Comparison")
    print(f"{'='*60}")
    header = f"{'Problem':<30}" + "".join(f" {m:<12}" for m in modes)
    print(header)
    print("-" * len(header))
    for problem in sorted(results.keys()):
        cols = "".join(f" {results[problem].get(m, {}).get('status', '-'):<12}" for m in modes)
        print(f"{problem:<30}{cols}")

    for mode in modes:
        statuses = [r[mode]["status"] for r in results.values() if mode in r]
        if not statuses:
            continue
        counts = Counter(statuses)
        cost = sum(r[mode].get("cost_usd", 0) for r in results.values() if mode in r)
        print(f"\n── {mode} ──")
        for s, c in counts.most_common():
            print(f"  {s}: {c}")
        print(f"  cost: ${cost:.2f}")

def main():
    parser = argparse.ArgumentParser(description="Evaluate withTPL vs withoutTPL on a dataset")
    parser.add_argument("--dataset", required=True, help="Dataset directory (e.g. VerinaSplit/test)")
    parser.add_argument("--tag", required=True, help="Tag for results/proofs (e.g. opus, deepseek)")
    parser.add_argument("--mode", default="withoutTPL", help="Modes to run, comma-separated (default: withTPL,withoutTPL)")
    parser.add_argument("--batch-size", type=int, default=100)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--rounds", type=int, default=3,
                        help="Number of rounds; each round re-runs only unproved problems (default: 3)")
    args = parser.parse_args()

    dataset_dir = ROOT / args.dataset
    if not dataset_dir.exists():
        print(f"Error: dataset directory {dataset_dir} not found", file=sys.stderr)
        sys.exit(1)

    problems = sorted([d.name for d in dataset_dir.iterdir() if d.is_dir() and (d / "task.lean").exists()])
    if not problems:
        print(f"Error: no problems found in {dataset_dir}", file=sys.stderr)
        sys.exit(1)

    results_file = OUTPUT_ROOT / args.dataset / f"results_{args.tag}.json"
    proof_dir = OUTPUT_ROOT / args.dataset / f"proofs_{args.tag}"
    trace_dir = OUTPUT_ROOT / args.dataset / f"traces_{args.tag}"
    modes = [m.strip() for m in args.mode.split(",")]

    print(f"Dataset: {dataset_dir} ({len(problems)} problems)")
    print(f"Results: {results_file}")
    print(f"Proofs:  {proof_dir}/")
    print(f"Traces:  {trace_dir}/")
    print(f"Modes:   {', '.join(modes)}")
    
    for problem in problems:
        ensure_orig(dataset_dir / problem / "task.lean")

    results = load_results(results_file)

    for round_num in range(1, args.rounds + 1):
        for mode in modes:
            _cleanup_stale()
            run_mode(mode, problems, results, args, dataset_dir, proof_dir, results_file, trace_dir)
        _cleanup_stale()

    print_comparison(results, modes)

if __name__ == "__main__":
    main()
