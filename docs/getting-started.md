# Getting started

Install elan, clone `https://github.com/chenle02/walsh-integral-lean.git`, and use the pinned toolchain and manifest unchanged. Run `lake exe cache get` for public dependencies, then `lake build`. Import `WalshIntegral`. The compiled examples are in `WalshIntegralTest/Examples.lean`.

For a downstream project, see dependency.md. The README verification block records actual source-bound checks; normal compilation alone does not establish independent comparison or a complete ownership audit.

For the exact local command and required output variables, see [verification.md](verification.md).
