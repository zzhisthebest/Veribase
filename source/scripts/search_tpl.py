#!/usr/bin/env python3
"""High-precision semantic search over the declaration-level TPL index."""

import argparse
import json
import math
import os
import queue
import re
import socket
import socketserver
import threading
import time
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INDEX = ROOT / "TPL_INDEX.jsonl"
DEFAULT_EMBEDDINGS = ROOT / "TPL_INDEX.embeddings.npy"
DEFAULT_SOCKET = Path(os.environ.get("TPL_SEARCH_SOCKET", "/tmp/artifact_tpl_search.sock"))
MODEL_NAME = "all-MiniLM-L6-v2"

SEMANTIC_WEIGHT = 0.72
LEXICAL_WEIGHT = 0.28
MIN_SEMANTIC = 0.50

SYNONYMS = {
    "minimum": ["min", "argmin", "least", "smallest"],
    "maximum": ["max", "argmax", "greatest", "largest"],
    "min": ["minimum", "argmin", "smallest"],
    "max": ["maximum", "argmax", "largest"],
    "power": ["pow", "exponentiation"],
    "exponentiation": ["pow", "power"],
    "modulo": ["mod", "remainder"],
    "subarray": ["contiguous", "slice", "segment"],
    "contiguous": ["subarray", "slice", "segment"],
    "member": ["mem", "membership", "contains"],
    "membership": ["mem", "member", "contains"],
    "contains": ["mem", "member", "membership"],
    "sorted": ["ordered", "pairwise", "sort"],
    "ordered": ["sorted", "pairwise", "order"],
    "permutation": ["perm", "isperm"],
    "length": ["size", "len"],
    "string": ["char", "characters", "text"],
    "prefix": ["take", "initial"],
    "suffix": ["drop", "tail"],
}


def tokenize(text):
    text = text.replace("_", " ")
    text = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", text)
    return re.findall(r"[A-Za-z][A-Za-z0-9!?']*|\d+|[≤≥<>]=?|∈|∉|↔|→", text.lower())


def query_tokens(query):
    tokens = tokenize(query)
    return list(dict.fromkeys(tokens + [word for token in tokens for word in SYNONYMS.get(token, ())]))


def compact(text, limit):
    text = " ".join(text.split())
    return text if len(text) <= limit else text[: limit - 1] + "…"


def load_entries(path):
    with path.open() as stream:
        return [json.loads(line) for line in stream if line.strip()]


def theorem_families(entries):
    families = defaultdict(list)
    definition_names = {entry["name"] for entry in entries if entry["kind"] == "def"}
    for entry in entries:
        if entry["kind"] != "theorem":
            continue
        for dependency in entry.get("dependencies", ()):
            if dependency in definition_names:
                families[dependency].append(entry)
    return families


def semantic_text(entry, families):
    parts = [
        " ".join(tokenize(entry["name"])),
        entry["name"],
        entry["module"],
        entry.get("doc", ""),
        entry["statement"],
        " ".join(entry.get("dependencies", ())),
    ]
    if entry["kind"] == "def":
        related = families.get(entry["name"], ())[:8]
        parts.extend(f"{item['name']}: {item.get('doc', '')} {item['statement']}" for item in related)
    return "\n".join(part for part in parts if part)


def lexical_tokens(entry):
    short_name = entry["name"].rsplit(".", 1)[-1]
    tokens = tokenize(short_name) * 8
    tokens += tokenize(entry["name"]) * 5
    tokens += tokenize(entry["statement"]) * 3
    tokens += tokenize(entry.get("doc", "")) * 2
    tokens += tokenize(entry["module"])
    for dependency in entry.get("dependencies", ()):
        tokens += tokenize(dependency) * 2
    return tokens


def load_model():
    os.environ.setdefault("CUDA_VISIBLE_DEVICES", "")
    from sentence_transformers import SentenceTransformer
    return SentenceTransformer(MODEL_NAME, local_files_only=True, device="cpu")


def build_embeddings(index_path, embeddings_path):
    import numpy as np

    entries = load_entries(index_path)
    families = theorem_families(entries)
    model = load_model()
    vectors = model.encode(
        [semantic_text(entry, families) for entry in entries],
        batch_size=64,
        normalize_embeddings=True,
        show_progress_bar=False,
    ).astype(np.float32)
    np.save(embeddings_path, vectors)
    print(f"Built {len(entries)} declaration embeddings at {embeddings_path}")


class SearchEngine:
    def __init__(self, index_path, embeddings_path):
        import numpy as np

        self.entries = load_entries(index_path)
        self.embeddings = np.load(embeddings_path)
        if self.embeddings.shape != (len(self.entries), 384):
            raise SystemExit(
                f"TPL embeddings do not match the index: {self.embeddings.shape} for {len(self.entries)} entries"
            )
        self.model = load_model()
        self.families = theorem_families(self.entries)
        self.name_to_index = {entry["name"]: i for i, entry in enumerate(self.entries)}
        self.indices_by_kind = {
            kind: np.array([i for i, entry in enumerate(self.entries) if entry["kind"] == kind])
            for kind in ("def", "theorem")
        }
        self.document_lengths = []
        self.document_frequency = Counter()
        self.postings = defaultdict(list)
        for entry in self.entries:
            tokens = lexical_tokens(entry)
            counts = Counter(tokens)
            index = len(self.document_lengths)
            self.document_lengths.append(len(tokens))
            self.document_frequency.update(counts.keys())
            for token, frequency in counts.items():
                self.postings[token].append((index, frequency))
        self.average_length = sum(self.document_lengths) / len(self.document_lengths)
        self.name_tokens = [set(tokenize(entry["name"])) for entry in self.entries]

    def encode(self, queries):
        return self.model.encode(
            queries,
            batch_size=64,
            normalize_embeddings=True,
            show_progress_bar=False,
        )

    def lexical_scores(self, query):
        import numpy as np

        qtokens = query_tokens(query)
        scores = np.zeros(len(self.entries), dtype=np.float32)
        for token in qtokens:
            postings = self.postings.get(token, ())
            if not postings:
                continue
            df = self.document_frequency[token]
            idf = math.log(1 + (len(self.entries) - df + 0.5) / (df + 0.5))
            for i, frequency in postings:
                denominator = frequency + 1.5 * (
                    0.25 + 0.75 * self.document_lengths[i] / self.average_length
                )
                scores[i] += idf * frequency * 2.5 / denominator
        return scores

    def search(self, query, query_vector, kind, top_k):
        import numpy as np

        semantic = self.embeddings @ query_vector
        lexical = self.lexical_scores(query)
        allowed = self.indices_by_kind[kind] if kind else np.arange(len(self.entries))
        lexical_max = float(lexical[allowed].max()) if len(allowed) else 0.0
        lexical_normalized = lexical / lexical_max if lexical_max else lexical
        qtokens = set(query_tokens(query))
        name_matches = np.array([len(qtokens & tokens) for tokens in self.name_tokens])
        combined = SEMANTIC_WEIGHT * semantic + LEXICAL_WEIGHT * lexical_normalized
        combined += 0.02 * np.minimum(name_matches, 3)

        def confident(i):
            return (
                semantic[i] >= MIN_SEMANTIC
                or (semantic[i] >= 0.34 and name_matches[i] >= 2)
                or (semantic[i] >= 0.40 and name_matches[i] >= 1 and combined[i] >= 0.60)
            )

        ranked = allowed[np.argsort(-combined[allowed])]
        ranked = [int(i) for i in ranked if confident(i)]
        general = [i for i in ranked if not self.entries[i]["module"].startswith("TPL.Specific")][:top_k]
        specific = [i for i in ranked if self.entries[i]["module"].startswith("TPL.Specific")][:top_k]
        return "\n\n".join([
            self.format_results("General", general, combined, semantic),
            self.format_results("Specific", specific, combined, semantic),
        ])

    def format_results(self, source_name, selected, combined, semantic):
        if not selected:
            return f"=== {source_name} candidates ===\nNo sufficiently relevant TPL declarations found."

        lines = [f"=== {source_name} candidates ==="]
        for i in selected:
            entry = self.entries[i]
            source = ROOT / f"{entry['module'].replace('.', '/')}.lean"
            statement = compact(entry["statement"], 600)
            lines.append(f"{combined[i]:.3f} (semantic {semantic[i]:.3f}) [{entry['kind']}] {entry['name']}")
            lines.append(f"  module: {entry['module']}")
            lines.append(f"  source: {source}")
            lines.append(f"  type: {statement}")
            if entry.get("doc"):
                lines.append(f"  doc: {compact(entry['doc'], 220)}")
            if entry["kind"] == "def":
                related = self.families.get(entry["name"], ())
                if related:
                    related = sorted(
                        related,
                        key=lambda theorem: -combined[self.name_to_index[theorem["name"]]],
                    )[:3]
                    lines.append("  family:")
                    for theorem in related:
                        lines.append(f"    - {theorem['name']} : {compact(theorem['statement'], 320)}")
        return "\n".join(lines)


class SearchBatcher:
    def __init__(self, engine):
        self.engine = engine
        self.jobs = queue.Queue()
        threading.Thread(target=self.run, daemon=True).start()

    def submit(self, request):
        event = threading.Event()
        job = {"request": request, "event": event, "response": None}
        self.jobs.put(job)
        event.wait()
        return job["response"]

    def run(self):
        while True:
            batch = [self.jobs.get()]
            deadline = time.monotonic() + 0.05
            while len(batch) < 64:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    break
                try:
                    batch.append(self.jobs.get(timeout=remaining))
                except queue.Empty:
                    break
            requests = [job["request"] for job in batch]
            try:
                vectors = self.engine.encode([request["query"] for request in requests])
                for job, request, vector in zip(batch, requests, vectors):
                    job["response"] = {
                        "ok": True,
                        "text": self.engine.search(
                            request["query"], vector, request.get("kind"), int(request.get("top_k", 5))
                        ),
                    }
            except Exception as error:
                for job in batch:
                    job["response"] = {"ok": False, "error": str(error)}
            finally:
                for job in batch:
                    job["event"].set()


class SearchHandler(socketserver.StreamRequestHandler):
    def handle(self):
        request = json.loads(self.rfile.readline())
        if request.get("ping"):
            response = {"ok": True, "text": "ready"}
        else:
            response = self.server.batcher.submit(request)
        self.wfile.write((json.dumps(response) + "\n").encode())


class SearchServer(socketserver.ThreadingUnixStreamServer):
    daemon_threads = True
    request_queue_size = 256


def serve(index_path, embeddings_path, socket_path):
    socket_path.parent.mkdir(parents=True, exist_ok=True)
    socket_path.unlink(missing_ok=True)
    engine = SearchEngine(index_path, embeddings_path)
    with SearchServer(str(socket_path), SearchHandler) as server:
        server.batcher = SearchBatcher(engine)
        print(f"TPL semantic search ready at {socket_path}", flush=True)
        try:
            server.serve_forever()
        finally:
            socket_path.unlink(missing_ok=True)


def send_request(socket_path, request):
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
            client.settimeout(120)
            client.connect(str(socket_path))
            client.sendall((json.dumps(request) + "\n").encode())
            chunks = []
            while True:
                chunk = client.recv(65536)
                if not chunk:
                    break
                chunks.append(chunk)
    except OSError as error:
        raise SystemExit(
            f"TPL semantic search service is unavailable at {socket_path}: {error}. "
            "Start it with scripts/search_tpl.py --serve."
        )
    response = json.loads(b"".join(chunks))
    if not response.get("ok"):
        raise SystemExit(f"TPL search failed: {response.get('error', 'unknown error')}")
    return response["text"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("query", nargs="?")
    parser.add_argument("--index", type=Path, default=DEFAULT_INDEX)
    parser.add_argument("--embeddings", type=Path, default=DEFAULT_EMBEDDINGS)
    parser.add_argument("--socket", type=Path, default=DEFAULT_SOCKET)
    parser.add_argument("--kind", choices=["def", "theorem"])
    parser.add_argument("--top-k", type=int, default=5)
    parser.add_argument("--build-embeddings", action="store_true")
    parser.add_argument("--serve", action="store_true")
    parser.add_argument("--ping", action="store_true")
    args = parser.parse_args()

    if args.build_embeddings:
        build_embeddings(args.index, args.embeddings)
    elif args.serve:
        serve(args.index, args.embeddings, args.socket)
    elif args.ping:
        print(send_request(args.socket, {"ping": True}))
    else:
        if not args.query:
            parser.error("provide a natural-language query")
        print(send_request(args.socket, {
            "query": args.query,
            "kind": args.kind,
            "top_k": args.top_k,
        }))


if __name__ == "__main__":
    main()
