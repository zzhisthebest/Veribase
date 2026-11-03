# VeriBase

**VeriBase: Automated Construction of Theorem Libraries for Software Verification**

[Paper (arXiv:2611.01743)](https://arxiv.org/abs/2611.01743)

VeriBase turns successful Lean verification solutions into reusable libraries
of code and associated theorems through proving, generalization, and harvesting.
This repository provides the generated general library, four benchmark-specific
libraries, construction and evaluation scripts, and agent instructions.

**Authors:** Zihao Zhang, Zenan Li, Taolue Chen, Zhe Zhou, Tao Xie, and Yuan Yao.

## Package contents

| Location | Contents |
| --- | --- |
| `libraries/general/general.lean` | Entry point importing the general library. |
| `libraries/general/general/` | Lean definitions and theorems, organized by data type and topic. |
| `libraries/benchmark-specific/verina/` | Verina-specific library. |
| `libraries/benchmark-specific/fvapps/` | FVAPPS-specific library. |
| `libraries/benchmark-specific/vericontest/` | VeriContest-specific library. |
| `libraries/benchmark-specific/verisoftbench/` | VeriSoftBench-specific theorems, organized by source repository and topic. |
| `source/scripts/prove.py` | Solving construction tasks, including multiple rounds. |
| `source/scripts/proof-generalize.py` | Running the generalization agent on successful solutions. |
| `source/scripts/extract_decls.lean` | Extracting declarations from Lean files. |
| `source/scripts/harvest.py` | Generating descriptions, estimating candidate frequency, and invoking the harvester. |
| `source/scripts/test.py` | Orchestrating evaluation, checking outputs, and saving results and traces. |
| `source/scripts/tpl_index.lean` | Extracting library declarations and their metadata for retrieval. |
| `source/scripts/search_tpl.py` | Semantic and keyword-based declaration retrieval. |
| `source/scripts/build_tpl_index.sh` | Builds the general-library declaration index and embeddings. |
| `source/.claude/agents/` | Instructions for the solving, generalization, and harvesting agents. |
| `source/lean-toolchain`, `source/lakefile.lean` | Lean version and project dependencies. |

`TPL` stands for **Theorem and Program Library**. In the original construction
and evaluation scripts, it is a generic working name for the library currently
in use, not a separate library.


## Inspecting the library

Start with `libraries/general/general.lean`; its modules are organized by data
type and topic. To compile, install Elan and run from the package root:

```bash
cp -R libraries/general/general source/
cp libraries/general/general.lean source/
cd source
lake update
lake exe cache get
lake build general
```

General, Verina, FVAPPS, and VeriContest use **Lean 4.18.0**. For a specific
library, copy its named `.lean` file and source directory into `source/`, then
build the matching target, e.g. `lake build verina`, in a separate working copy.
Library compilation does not require a model API key; fetching dependencies
requires network access.

VeriSoftBench uses **Lean 4.24.0** and modified upstream repositories with
selected lemmas removed (not bundled). Load `verisoftbench/<Repository>.lean`
in the corresponding repository environment; `verisoftbench.lean` imports only
common declarations.

## Declaration retrieval

Retrieval combines `all-MiniLM-L6-v2` embeddings and keyword matching, returning
five results by default. After building the general library, run from `source/`:

```bash
python -m pip install -r requirements.txt
python -c "from sentence_transformers import SentenceTransformer; SentenceTransformer('all-MiniLM-L6-v2')"
bash scripts/build_tpl_index.sh
python scripts/search_tpl.py --serve
```

Query from another terminal in `source/`:

```bash
python scripts/search_tpl.py "list permutation preserves membership" --kind theorem --top-k 5
python scripts/search_tpl.py "count occurrences in a list" --kind def --top-k 5
```


## Construction and evaluation scripts

The scripts require task files, the `claude` CLI, and an authenticated backend.
Harvesting uses similarity threshold `0.80`, minimum frequency `3`, and
`OPENROUTER_API_KEY` for description generation. Runs may incur API charges.
Use a dedicated working copy for agent runs, which modify task files and
temporarily change file permissions. The scripts retain the research harness's
dataset-layout and process-cleanup conventions; configure these for your local
environment before launching construction or evaluation.

## License

Original VeriBase contributions are available under the [MIT License](LICENSE),
except for files covered by a more specific notice. The construction/evaluation
source retains Apache-2.0, and several VeriSoftBench files retain LGPL-2.1.
See [third-party notices](THIRD_PARTY_NOTICES.md) for scope and dependencies.
