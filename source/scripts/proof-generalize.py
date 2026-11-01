#!/usr/bin/env python3
"""Run proof-generalize agent on a directory of Lean proof files.

Usage:
    python scripts/proof-generalize.py --proofs-dir train_proofs
    python scripts/proof-generalize.py --proofs-dir train_proofs --batch-size 5 --rounds 2
"""

import argparse, json, subprocess, sys, time, signal, shutil
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

MODE = "generalize"


def _cleanup_stale():
    """Kill stale claude/lean processes from previous runs."""
    for sig in [signal.SIGTERM, signal.SIGKILL]:
        subprocess.run(["pkill", "-f", "-u", "anonymous-user", "claude -p"], capture_output=True)
        subprocess.run(["pkill", "-f", "-u", "anonymous-user", "lake env lean"], capture_output=True)
        subprocess.run(
            f"pgrep -u anonymous-user lean | while read p; do "
            f"  grep -qF -- --server /proc/$p/cmdline 2>/dev/null && continue; "
            f"  grep -qF -- --worker /proc/$p/cmdline 2>/dev/null && continue; "
            f"  kill -{sig} $p 2>/dev/null; "
            f"done", shell=True, capture_output=True)
        subprocess.run(["pkill", "-u", "anonymous-user", "git"], capture_output=True)


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


def backup(filepath):
    orig = filepath.with_suffix(filepath.suffix + ".orig")
    if not orig.exists():
        shutil.copy2(filepath, orig)

def restore(filepath):
    orig = filepath.with_suffix(filepath.suffix + ".orig")
    if orig.exists():
        shutil.copy2(orig, filepath)

def compile_check(filepath):
    r = subprocess.run(
        ["lake", "env", "lean", str(filepath)],
        capture_output=True, text=True, cwd=str(ROOT), timeout=300
    )
    has_sorry = "declaration uses 'sorry'" in r.stdout
    return r.returncode == 0, has_sorry


def run_agent(filepath, timeout):
    """Run proof-generalize agent on a single file."""
    start_time = time.time()
    prompt = f"Target file: {filepath}"
    cmd = ["claude", "-p", prompt,
           "--agent", "proof-generalize",
           "--output-format", "stream-json", "--verbose",
           "--allow-dangerously-skip-permissions"]

    try:
        r = subprocess.run(cmd, capture_output=True, text=True, cwd=str(ROOT), timeout=timeout)
        elapsed = time.time() - start_time
        metrics = _parse_result(r.stdout)
        return {"exit": "ok", "elapsed": elapsed, "metrics": metrics, "returncode": r.returncode}
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start_time
        return {"exit": "timeout", "elapsed": elapsed}


def main():
    parser = argparse.ArgumentParser(description="Run proof-generalize agent to refactor Lean proofs")
    parser.add_argument("--proofs_path", required=True, help="Directory of .lean proof files")
    parser.add_argument("--batch-size", type=int, default=500)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--rounds", type=int, default=1) 
    args = parser.parse_args()

    proofs_dir = Path(args.proofs_path)
    files = sorted(proofs_dir.glob("*.lean"))
    results_file = proofs_dir / f"results_of_generalization.json"

    print(f"Proofs dir: {proofs_dir} ({len(files)} files)")
    print(f"Results:    {results_file}")

    results = load_results(results_file)

    for round_num in range(1, args.rounds + 1):
        already_generalized = {f.stem for f in files
                        if results.get(f.stem, {}).get(MODE, {}).get('status') == 'generalized'}
        retry = [f for f in files if f.stem not in already_generalized and MODE in results.get(f.stem, {})]
        pending = [f for f in files if f.stem not in already_generalized]# and f not in retry]
        pending = pending[::-1]
        print(f"\n{'='*60}")
        print(f"Round {round_num}/{args.rounds} — {len(pending)} pending / {len(retry)} retry / {len(files)} total")
        print(f"{'='*60}")

        if not pending:
            print("All done.")
            break

        for batch_start in range(0, len(pending), args.batch_size):
            batch = pending[batch_start : batch_start + args.batch_size]
            batch_num = batch_start // args.batch_size + 1
            total_batches = (len(pending) + args.batch_size - 1) // args.batch_size
            print(f"\n── Batch {batch_num}/{total_batches} ({len(batch)} files) ──")

            _cleanup_stale()

            # Backup before running agents
            for f in batch:
                backup(f)

            # Phase 1: run agents in parallel
            raw_results = {}
            with ThreadPoolExecutor(max_workers=args.batch_size) as executor:
                futures = {}
                for f in batch:
                    print(f"  [START] {f.name}")
                    futures[executor.submit(run_agent, f, args.timeout)] = f

                for future in as_completed(futures):
                    f = futures[future]
                    raw = future.result()
                    raw_results[f] = raw
                    print(f"  [DONE] {f.name} ({int(raw['elapsed'])}s)")

            # Phase 2: compile-check in parallel
            print(f"\n  ── Phase 2: compile-check ──")

            def check_one(f):
                raw = raw_results[f]
                if raw["exit"] != "ok" or raw["returncode"] != 0:
                    return f, "timeout" if raw["exit"] == "timeout" else "claude_error", int(raw["elapsed"]), 0, 0
                ok, has_sorry = compile_check(f)
                status = "generalized" if (ok and not has_sorry) else ("partial" if ok else "failed")
                return f, status, int(raw["elapsed"]), raw["metrics"]["tokens"], raw["metrics"]["cost_usd"]

            with ThreadPoolExecutor(max_workers=args.batch_size) as ex:
                futures = {ex.submit(check_one, f): f for f in batch}
                for future in as_completed(futures):
                    f, status, elapsed, tokens, cost = future.result()
                    result = {"status": status, "time_s": elapsed, "tokens": tokens, "cost_usd": cost}
                    print(f"  [{result['status'].upper()}] {f.name} ({elapsed}s, ${cost:.3f})")
                    results.setdefault(f.stem, {})[MODE] = result
                    save_results(results, results_file)

            # Restore files that failed to generalize
            for f in batch:
                s = results.get(f.stem, {}).get(MODE, {}).get("status")
                if s != "generalized":
                    restore(f)

            _cleanup_stale()

    # Summary
    print(f"\n{'='*60}")
    print(f"Proof-generalize Summary")
    print(f"{'='*60}")
    statuses = [r[MODE]["status"] for r in results.values() if MODE in r]
    if statuses:
        counts = Counter(statuses)
        cost = sum(r[MODE].get("cost_usd", 0) for r in results.values() if MODE in r)
        for s, c in counts.most_common():
            print(f"  {s}: {c}")


if __name__ == "__main__":
    main()
