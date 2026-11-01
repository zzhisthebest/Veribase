#!/usr/bin/env python3
"""Evaluate withTPL vs withoutTPL on a dataset.

Usage:
    python scripts/test_eval.py --dataset VerinaSplit/test --tag opus
    python scripts/test_eval.py --dataset VerinaSplit/test --tag opus --mode withTPL
    python scripts/test_eval.py --dataset VerinaSplit/test --tag opus --mode withoutTPL --batch-size 5
"""

import argparse, json, subprocess, sys, time, shutil, re, os, signal, atexit
import socket
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_ROOT = ROOT / "results"
PERMISSION_SNAPSHOT_FILE = ROOT / ".claude" / "test_permission_snapshot.json"

READABLE_ALLOWLIST = {
    ROOT / ".lake",
    ROOT / ".git",
    ROOT / ".claude",
    ROOT / ".api_key",
    ROOT / ".claude_api_keys",
    ROOT / "scripts",
    ROOT / "lakefile.lean",
    ROOT / "lake-manifest.json",
    ROOT / "lean-toolchain",
}

TPL_ALLOWLIST = {
    ROOT / "TPL",
    ROOT / "TPL.lean",
    ROOT / "TPL_INDEX.jsonl",
    ROOT / "TPL_INDEX.embeddings.npy",
}

_PERMISSION_SNAPSHOT = {}
_EXITING_AFTER_SIGNAL = False
_TPL_SEARCH_SERVICE = None
PROBLEM_KEEP_FILES = {"task.lean", "task.lean.orig", "description.txt"}
SCRIPTS_KEEP_FILES = {"test_eval.py", "run_test.sh"}

def start_tpl_search():
    socket_path = Path(f"/tmp/artifact_tpl_search_{os.getpid()}.sock")
    log_path = Path(f"/tmp/artifact_tpl_search_{os.getpid()}.log")
    os.environ["TPL_SEARCH_SOCKET"] = str(socket_path)
    log = log_path.open("w")
    process = subprocess.Popen(
        [sys.executable, str(ROOT / "scripts" / "search_tpl.py"),
         "--serve", "--socket", str(socket_path)],
        cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
    )
    for _ in range(120):
        if process.poll() is not None:
            break
        if socket_path.exists():
            try:
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
                    client.settimeout(1)
                    client.connect(str(socket_path))
                    client.sendall(b'{"ping": true}\n')
                    if b'"ok": true' in client.recv(1024):
                        print(f"TPL semantic search ready (pid {process.pid})")
                        return process, log, socket_path, log_path
            except OSError:
                pass
        time.sleep(0.5)
    process.terminate()
    process.wait(timeout=10)
    log.close()
    detail = log_path.read_text(errors="replace")[-2000:]
    raise SystemExit(f"Failed to start TPL semantic search:\n{detail}")

def stop_tpl_search(service):
    if not service:
        return
    process, log, socket_path, log_path = service
    process.terminate()
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()
    log.close()
    socket_path.unlink(missing_ok=True)
    log_path.unlink(missing_ok=True)

def validate_tpl_index():
    index = ROOT / "TPL_INDEX.jsonl"
    embeddings = ROOT / "TPL_INDEX.embeddings.npy"
    if not index.exists() or not embeddings.exists():
        raise SystemExit("TPL index or embeddings are missing; run scripts/build_tpl_index.sh")
    sources = [ROOT / "TPL.lean", *(ROOT / "TPL").rglob("*.lean")]
    if (any(path.stat().st_mtime > index.stat().st_mtime for path in sources)
            or embeddings.stat().st_mtime < index.stat().st_mtime):
        raise SystemExit("TPL index is stale; run scripts/build_tpl_index.sh")

def cleanup_dataset_extra_files(dataset_dir):
    """Delete stale scratch files inside evaluated problem directories."""
    if not dataset_dir.exists():
        return
    removed = 0
    for problem_dir in dataset_dir.iterdir():
        if not problem_dir.is_dir() or not (problem_dir / "task.lean").exists():
            continue
        for child in problem_dir.iterdir():
            if child.name in PROBLEM_KEEP_FILES:
                continue
            if child.is_dir():
                shutil.rmtree(child)
            else:
                child.chmod(0o644)
                child.unlink()
            removed += 1
    print(f"Cleaned dataset extra files/dirs: {removed}")

def _remember_mode(path):
    if path not in _PERMISSION_SNAPSHOT:
        _PERMISSION_SNAPSHOT[path] = path.stat().st_mode & 0o777
        PERMISSION_SNAPSHOT_FILE.parent.mkdir(parents=True, exist_ok=True)
        PERMISSION_SNAPSHOT_FILE.write_text(json.dumps(
            {str(p): mode for p, mode in _PERMISSION_SNAPSHOT.items()},
            indent=2
        ) + "\n")

def _chmod_recorded(path, mode):
    if not path.exists():
        return
    try:
        _remember_mode(path)
        path.chmod(mode)
    except FileNotFoundError:
        pass

def _hide_task_file(path):
    """Hide a task file and record its previous mode for interruption recovery."""
    _chmod_recorded(path, 0o000)

def _hide_path(path, allow_tpl=False):
    """Make a top-level path unreadable during evaluation."""
    if not path.exists():
        return

    # Do not chmod symlinks. Path.chmod follows symlinks by default and can
    # accidentally hide real dependency files under .lake/packages, e.g.
    # Mathlib -> .lake/packages/mathlib/Mathlib.
    if path.is_symlink():
        return

    if path.name == "scripts" and path.is_dir() and not path.is_symlink():
        for child in path.iterdir():
            keep = child.name in SCRIPTS_KEEP_FILES or (
                allow_tpl and child.name == "search_tpl.py"
            )
            if not keep:
                _chmod_recorded(child, 0o000)
        _chmod_recorded(path, 0o111)
    else:
        _chmod_recorded(path, 0o000)

def _is_ancestor_or_self(path, target):
    try:
        target.relative_to(path)
        return True
    except ValueError:
        return False

def _hide_except_descendant(path, keep, hidden):
    """Hide children of `path` except the branch leading to `keep`.

    Keep ancestor directories readable/openable; only hide sibling paths outside
    the dataset branch.
    """
    if path.resolve() == keep:
        return
    if not path.is_dir() or path.is_symlink():
        _hide_path(path)
        hidden.append(str(path))
        return
    for child in path.iterdir():
        child_resolved = child.resolve()
        if child_resolved == keep or _is_ancestor_or_self(child_resolved, keep):
            _hide_except_descendant(child, keep, hidden)
        else:
            _hide_path(child)
            hidden.append(str(child))

def hide_non_allowlisted_paths(dataset_dir, allow_tpl=False):
    """Hide ROOT entries except the allowlist and the dataset's top-level tree."""
    allowlist = {p.resolve() for p in READABLE_ALLOWLIST if p.exists()}
    if allow_tpl:
        allowlist.update(p.resolve() for p in TPL_ALLOWLIST if p.exists())
    dataset_resolved = dataset_dir.resolve()
    allowlist.add(dataset_resolved)
    hidden = []
    for path in ROOT.iterdir():
        resolved = path.resolve()
        if resolved in allowlist:
            continue
        if _is_ancestor_or_self(resolved, dataset_resolved):
            # Do not touch the top-level directory that contains the dataset.
            # This keeps the dataset tree directly openable in editors/file managers.
            continue
        _hide_path(path, allow_tpl=allow_tpl)
        hidden.append(str(path))
    if hidden:
        print("Hidden non-allowlisted paths:")
        for path in hidden:
            print(f"  {path}")

def restore_hidden_path_permissions():
    """Restore permissions changed by hide_non_allowlisted_paths."""
    snapshot = dict(_PERMISSION_SNAPSHOT)
    if PERMISSION_SNAPSHOT_FILE.exists():
        try:
            snapshot.update({
                Path(path): mode
                for path, mode in json.loads(PERMISSION_SNAPSHOT_FILE.read_text()).items()
            })
        except json.JSONDecodeError:
            pass
    for path, mode in sorted(snapshot.items(), key=lambda item: len(item[0].parts)):
        try:
            path.chmod(mode)
        except FileNotFoundError:
            pass
    _PERMISSION_SNAPSHOT.clear()
    try:
        PERMISSION_SNAPSHOT_FILE.unlink(missing_ok=True)
    except PermissionError:
        pass

def _restore_and_exit_on_signal(signum, frame):
    """Restore permissions immediately on Ctrl+C/SIGTERM.

    A plain `finally` block can be delayed while ThreadPoolExecutor waits for
    worker threads and child processes. On interrupt, restore first and then
    exit immediately.
    """
    global _EXITING_AFTER_SIGNAL
    if _EXITING_AFTER_SIGNAL:
        os._exit(128 + signum)
    _EXITING_AFTER_SIGNAL = True
    print("\nInterrupted; restoring file permissions...", file=sys.stderr, flush=True)
    try:
        restore_hidden_path_permissions()
    except Exception as exc:
        print(f"Warning: failed to restore permissions: {exc}", file=sys.stderr, flush=True)
    try:
        _cleanup_stale()
    except Exception:
        pass
    try:
        stop_tpl_search(_TPL_SEARCH_SERVICE)
    except Exception:
        pass
    os._exit(128 + signum)

def install_exit_handlers():
    atexit.register(restore_hidden_path_permissions)
    signal.signal(signal.SIGINT, _restore_and_exit_on_signal)
    signal.signal(signal.SIGTERM, _restore_and_exit_on_signal)

def _cleanup_stale():
    """Kill all lean/lake processes from previous runs.
    VS Code will restart lake serve / lean --server automatically when needed."""
    for sig in [signal.SIGTERM, signal.SIGKILL]:
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
            cached_input = usage.get('cache_read_input_tokens', 0)
            cache_creation = usage.get('cache_creation_input_tokens', 0)
            input_tokens = (
                usage.get('input_tokens', 0)
                + cache_creation
                + cached_input
            )
            output_tokens = usage.get('output_tokens', 0)
            return {
                'input_tokens': input_tokens,
                'cached_input_tokens': cached_input,
                'cache_creation_input_tokens': cache_creation,
                'output_tokens': output_tokens,
                'reasoning_output_tokens': usage.get('reasoning_output_tokens'),
                'total_tokens': input_tokens + output_tokens,
                'cost_usd': evt.get('total_cost_usd'),
            }
    return _empty_metrics()

def _empty_metrics():
    return {
        'input_tokens': None,
        'cached_input_tokens': None,
        'cache_creation_input_tokens': None,
        'output_tokens': None,
        'reasoning_output_tokens': None,
        'total_tokens': None,
        'cost_usd': None,
    }

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
    lines = text.splitlines(keepends=True)
    has_import = any(line.strip() == 'import TPL' for line in lines)
    if enable and not has_import:
        task_path.write_text('import TPL\n' + text)
    elif not enable:
        task_path.write_text(''.join(
            line for line in lines
            if not line.lstrip().startswith('import TPL')
        ))

def compile_check(filepath):
    try:
        r = subprocess.run(
            ["lake", "env", "lean", str(filepath)],
            capture_output=True, text=True, cwd=str(ROOT), timeout=300,
        )
    except subprocess.TimeoutExpired:
        return False, False
    has_sorry = "declaration uses 'sorry'" in (r.stdout + r.stderr)
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
    except subprocess.TimeoutExpired as exc:
        elapsed = time.time() - start_time
        partial_stdout = exc.stdout or ""
        if isinstance(partial_stdout, bytes):
            partial_stdout = partial_stdout.decode(errors="replace")
        _save_trace(trace_dir, problem, mode, partial_stdout)
        return {
            "exit": "timeout",
            "elapsed": elapsed,
            "metrics": _empty_metrics(),
        }

def run_agent_retrying_claude_errors(task_path, desc_path, timeout, mode, trace_dir):
    """Retry a clean, full-time attempt whenever Claude exits with an error."""
    problem = task_path.parent.name
    attempt = 1
    while True:
        raw = run_agent(task_path, desc_path, timeout, mode, trace_dir)
        if raw["exit"] != "ok" or raw.get("returncode", 0) == 0:
            return raw

        attempt += 1
        print(
            f"  [CLAUDE_ERROR] {problem} ({int(raw['elapsed'])}s); "
            f"retrying with a fresh {timeout}s limit (attempt {attempt})"
        )
        restore_from_orig(task_path)
        set_tpl_import(task_path, enable=(mode == "withTPL"))

def run_mode(mode, problems, results, args, dataset_dir, proof_dir, results_file, trace_dir):
    pending = [
        p for p in problems
        if mode not in results.get(p, {})
        or results[p][mode].get("status") == "claude_error"
    ]
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
                futures[executor.submit(
                    run_agent_retrying_claude_errors,
                    task_path,
                    desc_path,
                    args.timeout,
                    mode,
                    trace_dir,
                )] = problem

            for future in as_completed(futures):
                problem = futures[future]
                raw = future.result()
                raw_results[problem] = raw
                print(f"  [DONE] {problem} ({int(raw['elapsed'])}s)")
                task_path = dataset_dir / problem / "task.lean"
                _hide_task_file(task_path)
        # ── Phase 2: compile-check in parallel ──
        print(f"\n  ── Phase 2: compile-check ──")
        mode_proof_dir = proof_dir / mode
        mode_proof_dir.mkdir(parents=True, exist_ok=True)

        def check_one(problem):
            raw = raw_results[problem]
            if raw["exit"] != "ok" or raw["returncode"] != 0:
                status = "timeout" if raw["exit"] == "timeout" else "claude_error"
                return problem, status, int(raw["elapsed"]), raw.get("metrics", _empty_metrics())
            task_path = dataset_dir / problem / "task.lean"
            task_path.chmod(0o644)
            ok, has_sorry = compile_check(task_path)
            status = "proved" if (ok and not has_sorry) else ("partial" if ok else "failed")
            return problem, status, int(raw["elapsed"]), raw["metrics"]

        with ThreadPoolExecutor(max_workers=args.batch_size) as ex:
            futures = {ex.submit(check_one, p): p for p in batch}
            for future in as_completed(futures):
                problem, status, elapsed, metrics = future.result()
                result = {"status": status, "time_s": elapsed, **metrics}
                cost = metrics["cost_usd"]
                cost_text = f"${cost:.3f}" if cost is not None else "cost unavailable"
                print(f"  [{result['status'].upper()}] {problem} ({elapsed}s, {cost_text})")
                results.setdefault(problem, {})[mode] = result
                save_results(results, results_file)
                task_path = dataset_dir / problem / "task.lean"
                task_path.chmod(0o644)
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
        costs = [
            r[mode].get("cost_usd")
            for r in results.values()
            if mode in r and r[mode].get("cost_usd") is not None
        ]
        print(f"\n── {mode} ──")
        for s, c in counts.most_common():
            print(f"  {s}: {c}")
        if costs:
            print(f"  cost: ${sum(costs):.2f}")
        else:
            print("  cost: unavailable")

def main():
    global _TPL_SEARCH_SERVICE
    install_exit_handlers()

    parser = argparse.ArgumentParser(description="Evaluate withTPL vs withoutTPL on a dataset")
    parser.add_argument("--dataset", required=True, help="Dataset directory (e.g. VerinaSplit/test)")
    parser.add_argument("--tag", required=True, help="Tag for results/proofs (e.g. opus, deepseek)")
    parser.add_argument("--mode", default="withoutTPL,withTPL", help="Modes to run, comma-separated (default: withTPL,withoutTPL)")
    parser.add_argument("--batch-size", type=int, default=500)
    parser.add_argument("--timeout", type=int, default=1800)
    args = parser.parse_args()

    restore_hidden_path_permissions()

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
    search_service = None
    if "withTPL" in modes:
        validate_tpl_index()
        search_service = start_tpl_search()
        _TPL_SEARCH_SERVICE = search_service

    print(f"Dataset: {dataset_dir} ({len(problems)} problems)")
    print(f"Results: {results_file}")
    print(f"Proofs:  {proof_dir}/")
    print(f"Traces:  {trace_dir}/")
    print(f"Modes:   {', '.join(modes)}")

    try:
        cleanup_dataset_extra_files(dataset_dir)

        for problem in problems:
            ensure_orig(dataset_dir / problem / "task.lean")

        results = load_results(results_file)

        for mode in modes:
            restore_hidden_path_permissions()
            hide_non_allowlisted_paths(dataset_dir, allow_tpl=(mode == "withTPL"))
            _cleanup_stale()
            run_mode(mode, problems, results, args, dataset_dir, proof_dir, results_file, trace_dir)
        _cleanup_stale()
        
        print_comparison(results, modes)
    finally:
        stop_tpl_search(search_service)
        _TPL_SEARCH_SERVICE = None
        restore_hidden_path_permissions()

if __name__ == "__main__":
    main()
