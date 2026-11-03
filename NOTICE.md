# Dependencies and attribution

This development builds on:

- **Lean 4** and **Mathlib** (`v4.35.0`) — the Lean prover and its mathematical
  library. Mathlib is licensed Apache-2.0.
- **harfe/fixed-point-theorems-lean4** — the Brouwer and Kakutani fixed-point
  theorems in Lean 4, licensed MIT (Copyright (c) 2026 harfe). This repository
  imports those theorems (`FixedPointTheorems.brouwer`, `FixedPointTheorems.kakutani`)
  as a dependency; their axiom audit is reproduced as part of this development's
  own audit. See https://github.com/harfe/fixed-point-theorems-lean4

The fixed-point theorems are supplied by the harfe dependency and are not
re-hosted here. The exact dependency revision is pinned. The formalizations
in `GEOverlap.lean` and `formal/` are maintained in this project under its MIT
license. Underlying classical mathematics is not claimed as a new invention:
the status documentation names its economic and mathematical predecessors.
The historical foundation seal is retained unchanged; current scope and the
extension inventory are stated in README.md and the release manifest.
