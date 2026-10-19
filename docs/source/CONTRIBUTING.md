# Contributing to WalshIntegral

Read README.md, AGENTS.md and the exact Lean declarations before editing. Use
the pinned Lean toolchain and Mathlib manifest together. Compile changed
modules locally before running a verification gate.

Preserve every hypothesis and quantifier, including predictable finite-variance
domains and almost-sure equality separately at each output. A totalized integral
being defined does not prove its argument belongs to the integration domain.

Keep the claim ledger, public theorem inventory, type/axiom checks, examples and
documentation aligned. A change to a mathematical constant, sign or domain
boundary needs a real compiling consumer and a meaningful negative control.
Keep positive witnesses and exact expected-failure diagnostics.

Retain provenance and Apache-2.0 notices. Distinguish known-theorem formalization
from mathematical novelty. Never fabricate receipts or treat evidence for a
different scientific source as acceptance of changed code. Record the actual
source, compiler, dependencies and checker tools used by each verification run.
