#!/usr/bin/env bash
# Audit the axioms of EVERY constant the package's own modules define, read from the compiled environment:
# public and private theorems, lemmas, definitions, instances and generated auxiliaries (G7, G13). A source
# regex cannot see private helpers or tell a lemma from prose; the environment can.
#
# usage: owned_audit.sh PKG [ALLOWED_REGEX]     run from the package root after `lake build PKG`
#   PKG            the library name, e.g. RoughHeatKernel (modules: PKG.lean and PKG/**/*.lean)
#   ALLOWED_REGEX  default 'propext|Classical.choice|Quot.sound'
# Prints the audit output (so a receipt binds it) and `owned audit: PASS (N owned constants)`; exits 1 on a
# forbidden axiom, on a missing row, or when Lean fails.
set -euo pipefail
pkg="$1"; allowed="${2:-propext|Classical.choice|Quot.sound}"
mods=$( { [ -f "$pkg.lean" ] && echo "$pkg"; find "$pkg" -name '*.lean' 2>/dev/null \
          | LC_ALL=C sort | sed 's/\.lean$//; s#/#.#g'; } | LC_ALL=C sort -u)
[ -n "$mods" ] || { echo "owned audit: no modules found for $pkg" >&2; exit 1; }
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
{
  echo "import Lean"
  for m in $mods; do echo "import $m"; done
  echo "open Lean Elab Command"
  echo "run_cmd do"
  echo "  let env ← getEnv"
  printf '  let modules : Array Name := #[%s]\n' "$(for m in $mods; do printf '`%s, ' "$m"; done | sed 's/, $//')"
  cat <<'LEAN'
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx.toNat]! then
        names := names.push name
  logInfo m!"OWNED-COUNT {names.size}"
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    logInfo m!"OWNED-AXIOMS {name}: {axioms.toList}"
LEAN
} > "$tmp/OwnedAudit.lean"
# `lake lean`, not `lake env lean`: it hands Lean the build's own import paths (--setup), so a dependency-side
# PKG/ or PKG.olean earlier on LEAN_PATH cannot shadow the package (G14).
lake lean "$tmp/OwnedAudit.lean" > "$tmp/out" 2>&1 || { cat "$tmp/out" >&2; echo "owned audit: Lean failed" >&2; exit 1; }
cat "$tmp/out"
joined="$(tr '\n' ' ' < "$tmp/out")"
count="$(grep -o 'OWNED-COUNT [0-9]*' <<<"$joined" | awk '{print $2}')"
rows="$(grep -o 'OWNED-AXIOMS [^ ]*: \[[^]]*\]' <<<"$joined" | wc -l)"
[ -n "$count" ] && [ "$count" -gt 0 ] && [ "$rows" -eq "$count" ] \
  || { echo "owned audit: $rows axiom rows for ${count:-?} owned constants" >&2; exit 1; }
bad="$(grep -o 'OWNED-AXIOMS [^ ]*: \[[^]]*\]' <<<"$joined" | sed 's/.*\[//; s/\]//' | tr ',' '\n' \
       | sed 's/^ *//; s/ *$//; s/\.{.*}$//' | sed '/^$/d' | sort -u | grep -v -x -E "$allowed" || true)"
if [ -n "$bad" ]; then
  echo "owned audit: forbidden axiom(s): $(tr '\n' ' ' <<<"$bad")" >&2
  grep -o 'OWNED-AXIOMS [^ ]*: \[[^]]*\]' <<<"$joined" | grep -F -f <(printf '%s\n' $bad) >&2 || true
  exit 1
fi
echo "owned audit: PASS ($count owned constants, only: ${allowed//|/, })"
