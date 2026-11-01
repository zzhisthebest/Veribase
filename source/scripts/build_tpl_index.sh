#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
INDEX="$ROOT/TPL_INDEX.jsonl"
TEMP_INDEX=$(mktemp "$ROOT/.TPL_INDEX.filtered.jsonl.XXXXXX")
TEMP_EMBEDDINGS=$(mktemp "$ROOT/.TPL_INDEX.embeddings.XXXXXX.npy")

cleanup() {
  rm -f "$TEMP_INDEX" "$TEMP_EMBEDDINGS"
}
trap cleanup EXIT

cd "$ROOT"
lake build tpl_index
lake exe tpl_index > "$TEMP_INDEX"
python -c '
import json
import sys

path = sys.argv[1]
count = 0
with open(path) as stream:
    for line in stream:
        entry = json.loads(line)
        assert entry["kind"] in {"def", "theorem"}
        assert not entry["name"].startswith("_")
        count += 1
if count == 0:
    raise SystemExit("TPL index is empty")
print(f"Validated {count} declarations")
' "$TEMP_INDEX"
python "$ROOT/scripts/search_tpl.py" \
  --build-embeddings \
  --index "$TEMP_INDEX" \
  --embeddings "$TEMP_EMBEDDINGS"
mv "$TEMP_INDEX" "$INDEX"
mv "$TEMP_EMBEDDINGS" "$ROOT/TPL_INDEX.embeddings.npy"
