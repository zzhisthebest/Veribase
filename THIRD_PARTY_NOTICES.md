# Licensing and third-party notices

The root MIT license covers original VeriBase contributions except where a
file or directory specifies another license. It does not replace third-party
copyrights, licenses, or notices.

## Construction and evaluation source

The `source/` snapshot originates from an Apache-2.0-licensed working project.
Its Apache-2.0 license is retained in `source/LICENSE`; it is not silently
relicensed under the root MIT license. Public-release changes include the
general-library index-building wrapper and the simplified Lake targets.

## Explicit LGPL-2.1 notices

The following released VeriSoftBench files carry LGPL-2.1 notices, which are
retained. The full license is provided in `LICENSES/LGPL-2.1.txt` and in the
VeriSoftBench library directory as `LICENSE.md`.

- `libraries/benchmark-specific/verisoftbench/verisoftbench/Loom/GuardHimp.lean`
- `libraries/benchmark-specific/verisoftbench/verisoftbench/Loom/WP.lean`
- `libraries/benchmark-specific/verisoftbench/verisoftbench/Loom/NonDetT.lean`
- `libraries/benchmark-specific/verisoftbench/verisoftbench/Common/Algebra/CompleteBooleanAlgebra.lean`

## External dependencies and construction sources

Lean, Mathlib, Batteries, Plausible, the embedding model, and benchmark
repositories retain their respective licenses. Downloaded dependencies,
benchmark task datasets, and model weights are not bundled in this repository.
VeriSoftBench modules require the corresponding modified upstream repository
environments described in the README.

The released libraries are generated from verification-task solutions. The
root MIT license grants rights only in contributions owned by the VeriBase
contributors; any incorporated third-party material remains subject to its
original terms. The paper's license is separate from the software licenses.
