# Reproduce the verification checks

Use Linux with Bash, Git, Python 3, GNU coreutils, a C toolchain, and the pinned
Lean installation. Keep lean-toolchain and lake-manifest.json unchanged. Obtain
public dependency artifacts with `lake exe cache get` before the verification
run. Never run `lake update` during a frozen replay.

From the repository root, make the pinned toolchain's native checker available
and choose a fresh external directory. The `native` directory below must not
already exist; the verification scripts create and retain it.

```sh
export PATH="$(dirname "$(elan which lean)"):$PATH"
export LEAN_NUM_THREADS=1
verification_dir=$(mktemp -d)
export VERIFY_ARTIFACTS_DIR="$verification_dir/checks"
export LIBRARY_AUDIT_DIR="$verification_dir/native"
bash verify.sh "$verification_dir/verify.log" \
  > "$verification_dir/wrapper.stdout" \
  2> "$verification_dir/wrapper.stderr"
```

The script rebuilds the package's own production, reference and test cones
from fresh own outputs. Public Mathlib dependency artifacts may be reused.
It checks the inventory, elaborated types, standard-axiom closures, examples,
strict expected-reason negatives, all compiler-owned private/generated helpers,
compiled escape controls and exact native module replays. Reference and
production declarations are inspected in separate environments.

Retain the entire external directory, including raw positive/negative
diagnostics, native reports, provider bindings and wrapper seal lines. Native
raw reports can be large; deterministic gzip reports and their hashes are
retained alongside them. Use a fresh external directory for another run.

This command runs the checks. An official lower-tier receipt additionally
requires the actual retained executor terminal state and receipt producer.
Independent comparator evidence is a separate check. Inspect the generated
[README verification record](../README.md#verification-at-a-glance) and its
canonical receipts for actual execution and exact source identity.
