#!/usr/bin/env python3
"""
TPL Harvester

1. Extract declarations with extract_decls.
2. Generate descriptions and embeddings; compute cross-file frequency.
3. Send frequent candidates to DeepSeek for generalization.
4. Write declarations to TPL and compile.
"""

import argparse, hashlib, json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import numpy as np
from openai import OpenAI
from sentence_transformers import SentenceTransformer

ROOT = Path(__file__).resolve().parents[1]
DESC_CACHE = ROOT / ".cache" / "desc_cache.json"

API_KEY = os.environ["OPENROUTER_API_KEY"]
API_BASE = "https://openrouter.ai/api/v1"
API_MODEL = "deepseek/deepseek-chat"


def extract_decls(file_path):
    path = Path(file_path).resolve()
    module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
    try:
        r = subprocess.run(['lake', 'exe', 'extract_decls', module],
                           capture_output=True, text=True, cwd=str(ROOT), timeout=300)
    except subprocess.TimeoutExpired:
        return []
    if r.returncode != 0:
        return []
    seen, out = set(), []
    for d in json.loads(r.stdout):
        src = d['source'].strip()
        if src not in seen:
            seen.add(src)
            out.append({'file': str(path), 'kind': d['kind'], 'source': src})
    return out



def load_cache():
    DESC_CACHE.parent.mkdir(parents=True, exist_ok=True)
    return json.loads(DESC_CACHE.read_text()) if DESC_CACHE.exists() else {}

def save_cache(cache):
    DESC_CACHE.write_text(json.dumps(cache, indent=2, ensure_ascii=False) + "\n")

def describe(client, source, cache):
    key = hashlib.md5(source.encode()).hexdigest()
    if key in cache:
        return cache[key]
    resp = client.chat.completions.create(
        model=API_MODEL, max_tokens=256, temperature=0.0,
        messages=[{"role": "user", "content":
            f"""You are a mathematician and an expert in Lean. Below is a declaration in Lean 4:

```lean4
{source}
```

Generate a natural language description of this declaration.
First determine the sub-domain (e.g. list operations, arithmetic, sorting, etc.).
Then determine its difficulty, whether it's trivial or not. Highlight the use of well-known lemma or their variants if it is non-trivial.
Then summarize to a brief description.

Instructions:
1. Keep the description short, within 1 to 5 sentences.
2. Introduce the name if it is some well-known theorem or one of its variants.
3. Enclose the description in one pair of <description> tags."""}])
    text = resp.choices[0].message.content or ""
    m = re.search(r'<description>(.*?)</description>', text, re.DOTALL)
    cache[key] = m.group(1).strip() if m else text.strip()[:200]
    return cache[key]

def describe_batch(client, sources, cache, workers=256):
    uncached = [s for s in sources if hashlib.md5(s.encode()).hexdigest() not in cache]
    if uncached:
        print(f"  Describing {len(uncached)} declarations ({len(sources)-len(uncached)} cached)", file=sys.stderr)
        with ThreadPoolExecutor(max_workers=workers) as ex:
            list(as_completed({ex.submit(describe, client, s, cache): s for s in uncached}))
        save_cache(cache)
    return [cache[hashlib.md5(s.encode()).hexdigest()] for s in sources]


def compute_frequencies(decls, descs, model, threshold=0.80):
    embs = model.encode(descs, batch_size=512, show_progress_bar=True)
    norms = np.linalg.norm(embs, axis=1, keepdims=True)
    norms[norms == 0] = 1
    sim = (embs / norms) @ (embs / norms).T

    files = [d['file'] for d in decls]
    freqs = []
    for i in range(len(decls)):
        similar_files = set()
        for j in range(len(decls)):
            if sim[i, j] > threshold:
                similar_files.add(files[j])
        freqs.append(len(similar_files))
    return freqs


# ── main ──────────────────────────────────────────────────────────

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--proofs_path', type=str)
    p.add_argument('--min-freq', type=int, default=3)
    p.add_argument('--threshold', type=float, default=0.80)
    p.add_argument('--start-batch', type=int, default=1)
    p.add_argument('--candidates-path', '--candidates_path', type=Path,
                   default=ROOT / "scripts" / "harvest_candidates.json",
                   help='Path to read or write candidate JSON')
    p.add_argument('--resume', action='store_true',
                   help='Resume from candidate JSON, skipping extraction, descriptions, and frequency computation')
    p.add_argument('--candidates-only', action='store_true',
                   help='Stop after generating candidate JSON without calling tpl-harvester')
    args = p.parse_args()

    candidates_path = args.candidates_path

    if args.resume:
        high = json.loads(candidates_path.read_text())
        print(f"[resume] Read {len(high)} candidates from {candidates_path}", file=sys.stderr)
    else:
        proofs_dir = Path(args.proofs_path)
        paths = sorted(proofs_dir.glob("*.lean"))
        print(f"[0] proof files: {len(paths)}", file=sys.stderr)

        print(f"[1] Extracting declarations ({len(paths)} files)", file=sys.stderr)
        decls = []
        with ThreadPoolExecutor(max_workers=min(len(paths), 256)) as ex:
            for f in as_completed({ex.submit(extract_decls, p): p for p in paths}):
                decls.extend(f.result())
        def is_spec(src):
            s = src
            if re.search(r'\bdef\s+\S+_precond\b', s):
                return True
            if re.search(r'\bdef\s+\S+_postcond\b', s):
                return True
            if re.search(r'\btheorem\s+\S+_postcond_satisfied\b', s):
                return True
            return False
        decls = [d for d in decls if not is_spec(d['source'])]
        print(f"Extracted {len(decls)} declarations")

        print(f"[2] Generating descriptions", file=sys.stderr)
        client = OpenAI(api_key=API_KEY, base_url=API_BASE)
        cache = load_cache()
        descs = describe_batch(client, [d['source'][:500] for d in decls], cache)

        print(f"[3] Computing frequencies", file=sys.stderr)
        model = SentenceTransformer('all-MiniLM-L6-v2')
        freqs = compute_frequencies(decls, descs, model, threshold=args.threshold)
        for i in range(len(decls)):
            decls[i]['frequency'] = freqs[i]

        for lo, hi in [(1,4),(5,9),(10,19),(20,49),(50,99),(100,None)]:
            label = f"{lo}-{hi}" if hi else f"{lo}+"
            cnt = sum(1 for d in decls if d['frequency'] >= lo and (hi is None or d['frequency'] <= hi))
            print(f"  freq {label}: {cnt}", file=sys.stderr)

        high = sorted([d for d in decls if d['frequency'] >= args.min_freq],
                      key=lambda d: -d['frequency'])
        print(f"  freq>={args.min_freq}: {len(high)}", file=sys.stderr)
        json_out = [{'kind': d['kind'], 'frequency': d['frequency'],
                     'file': d['file'], 'source': d['source'][:500]} for d in high]
        candidates_path.parent.mkdir(parents=True, exist_ok=True)
        candidates_path.write_text(json.dumps(json_out, indent=2, ensure_ascii=False) + "\n")
        print(f"  Candidates written to {candidates_path}", file=sys.stderr)

    if args.candidates_only:
        return

    if not high:
        return

    # return
    print(f"[4] Calling tpl-harvester", file=sys.stderr)
    from collections import defaultdict
    by_file = defaultdict(list)
    for d in high:
        by_file[d['file']].append({'kind': d['kind'],
                                   'statement': d['source'], 'file': d['file']})
    batches = [by_file[k] for k in sorted(by_file.keys())]

    for i, batch in enumerate(batches):
        if i + 1 < args.start_batch:
            continue
        prompt = f"""Harvest these candidates into TPL.

## Candidates (batch {i+1}/{len(batches)}, from {batch[0]['file']})
{json.dumps(batch, indent=2)}
"""
        print(f"  tpl-harvester batch {i+1}/{len(batches)} ({len(batch)} candidates, {batch[0]['file']})", file=sys.stderr)
        try:
            subprocess.run(
                ["claude", "-p", prompt, "--agent", "tpl-harvester",
                 "--allow-dangerously-skip-permissions"],
                cwd=str(ROOT), timeout=1800
            )
        except subprocess.TimeoutExpired:
            print(f"  [TIMEOUT] batch {i+1}, skipping", file=sys.stderr)


if __name__ == '__main__':
    main()
