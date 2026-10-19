# Trust and reproducibility

The pinned Lean toolchain and Mathlib revision are recorded in `lean-toolchain` and `lake-manifest.json`. They must be used together. Run `bash verify.sh` only in an isolated disposable checkout: the verifier deletes that checkout's `.lake/build` to force a fresh own-package build.

The verifier checks source policy, exact theorem inventory, import ownership, public and all owned constant axioms, examples and ten negative controls. Negative fixtures must fail for the intended sole-False reason; their positive witnesses must compile cleanly. Only `propext`, `Classical.choice` and `Quot.sound` are allowed foundational axioms.

A release claim requires evidence bound to the exact scientific source commit, including a native compiled-module replay and independent comparison. The generated README verification block records these checks for its named scientific content. Evidence from a different scientific source must not be silently relabeled.

Kernel checking establishes the stated Lean theorem with its hypotheses. The prose description, relation to the classical literature, and suitability for an application require mathematical review. L² classes, chosen representatives, separate almost-sure identities and literal equality are distinct interfaces.

For the exact local command and required output variables, see [verification.md](verification.md).
