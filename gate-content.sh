#!/usr/bin/env bash
# Verification gate for a lab Lean package (template: Le-AI-Lab templates/lean-package-verify, owner lean-ops).
# Copy into the package root with scripts/theorem_names.awk, scripts/owned_audit.sh and scripts/lake_guard.sh,
# then set PKG and TEST (and ROOTS if the root package has more lean_libs than PKG).
# The log this prints is what `lean-pkg receipt slurm|systemd` binds: keep the per-constant audit output in it.
set -euo pipefail
shopt -s nullglob                       # G8: a missing control is an empty list, never a literal pattern
cd "$(dirname "$0")"
PKG="${PKG:-WalshIntegral}"            # library name: PKG.lean and PKG/**/*.lean
TEST="${TEST:-${PKG}Test}"              # TypeCheck.lean, AxiomCheck.lean, Examples.lean, *.lean.disabled
ROOTS="${ROOTS:-$PKG $TEST WalshIntegralChallenge WalshIntegralSolution}"                   # every root lean_lib namespace (shadow and fresh-build checks)
# Negative controls (step 7): strict = each control imports a witness that compiles clean and fails only with
# unsolved goals `⊢ False`; legacy = packages not yet migrated (missing witness, helper declarations and
# non-False goals are WARN lines, every other rule holds). New copies keep strict; see README "Negative controls".
NEG_CONTROLS="${NEG_CONTROLS:-strict}"
ALLOWED='propext|Classical.choice|Quot.sound'
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

# 0. Fresh build (G15): Lake reads its local artifact cache by default (LAKE_ARTIFACT_CACHE unset = on), and a
#    module restored from it is "Reused" without its `sorry` warning; `--no-cache` only governs downloads.
#    Point the cache at a new empty directory (LAKE_CACHE_DIR="" does NOT disable it) and switch reads off;
#    the empty directory also covers a lakefile `enableArtifactCache = true`, which overrides the variable.
export LAKE_CACHE_DIR="$tmp/lake-cache" LAKE_ARTIFACT_CACHE=false
mkdir -p "$LAKE_CACHE_DIR"
echo "lake-cache-dir: $LAKE_CACHE_DIR (fresh, empty)"
echo "lake-artifact-cache: $LAKE_ARTIFACT_CACHE"
if grep -n -E 'enableArtifactCache' lakefile.lean lakefile.toml 2>/dev/null; then
  echo "lakefile sets enableArtifactCache: reads are confined to the empty cache above"
fi

echo "toolchain: $(lean --version | sed -n '1p')"
echo "manifest mathlib revision: $(grep -B8 '"name": "mathlib"' lake-manifest.json | grep -m1 '"rev"' | sed 's/^ *//')"

# 1. No placeholders or project axioms in library sources (a source scan; step 4b is the binding audit).
srcs=("$PKG".lean)
while IFS= read -r f; do srcs+=("$f"); done < <(find "$PKG" -name '*.lean' | LC_ALL=C sort)
if grep -n -w -E 'sorry|admit|axiom|opaque' "${srcs[@]}"; then
  echo "placeholder or project axiom found" >&2; exit 1
fi
echo "placeholder audit: PASS"
# The proved reference cone must also be free of proof holes and reflective escape syntax.
reference_sources=(WalshIntegralChallenge.lean WalshIntegralSolution.lean)
while IFS= read -r f; do reference_sources+=("$f"); done < <(find WalshIntegralChallenge -name '*.lean' | LC_ALL=C sort)
if grep -n -w -E 'sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|skipKernelTC|trustLevel|include_str|include_bytes|run_io|run_cmd|run_elab' "${reference_sources[@]}"; then
  echo "reference proof escape found" >&2; exit 1
fi

# 2. Build the library from scratch: drop the root package's own outputs (dependencies stay), build verbosely
#    so Lake names every job's action (-v; --log-level info keeps trace messages out), then refuse any root
#    module that was not built in this run (G15).
rm -rf .lake/build
echo "root build dir: removed .lake/build for a fresh build"
# The full log goes to the guard; stdout keeps every root job and anything with output, not the thousands of
# silent dependency jobs (Mathlib) that -v also lists.
# The markers bound the build for `lean-pkg receipt`, which judges cache lines (Reused/Replayed/Unpacked) only
# between them: the later `lake lean FILE` steps re-print the stored warnings of just-built modules as
# `Replayed`, which is not a restore (exact strings: lean-pkg lake_hygiene BUILD_BEGIN / BUILD_END).
echo "lean-pkg-build: begin"
set +e
# Separate duplicate-name environments and serialize independent cones at the
# scheduler level. LEAN_NUM_THREADS alone only limits each Lean compiler.
for target in "$PKG" WalshIntegralChallenge "$TEST" WalshIntegralSolution; do
  lake build -v --log-level info --no-ansi "$target" || exit "$?"
done 2>&1 | tee "$tmp/build.log"
build_exit=${PIPESTATUS[0]}
set -e
echo "lean-pkg-build: end"
[ "$build_exit" -eq 0 ] || { echo "lake build failed (exit $build_exit)" >&2; exit 1; }
# shellcheck disable=SC2086
bash scripts/lake_guard.sh fresh "$tmp/build.log" $ROOTS

# 2b. No dependency shadows the package (G14): Lake puts the root's lib dir last on LEAN_PATH and Lean loads
#     the first match, so a dependency-side ROOT/ or ROOT.olean would be read instead. The elaboration steps
#     below use `lake lean FILE`, which passes the build's own import paths via --setup; this check also
#     covers anyone who runs `lake env lean` on the tree.
# shellcheck disable=SC2086
bash scripts/lake_guard.sh shadow "$(lake env printenv LEAN_PATH)" "$PWD/.lake/build/lib/lean" $ROOTS

# 3. Public inventory cross-check: source theorems/lemmas == inventory == #check list == #print axioms list.
awk -f scripts/theorem_names.awk "${srcs[@]}" | LC_ALL=C sort > "$tmp/source"
LC_ALL=C sort THEOREM_INVENTORY.txt > "$tmp/inventory"
sed -n 's/^#check @//p' "$TEST/TypeCheck.lean" | LC_ALL=C sort > "$tmp/check"
sed -n 's/^#print axioms //p' "$TEST/AxiomCheck.lean" | LC_ALL=C sort > "$tmp/axioms"
for f in source check axioms; do
  if ! diff -u "$tmp/inventory" "$tmp/$f"; then
    echo "theorem inventory mismatch ($f)" >&2; exit 1
  fi
done
echo "theorem inventory: PASS ($(wc -l < "$tmp/inventory") public theorems and lemmas)"

# 4. Axiom audit of the public inventory.
lake lean "$TEST/AxiomCheck.lean" > "$tmp/axiom-out"
cat "$tmp/axiom-out"
reported="$(grep -c -E "depends on axioms|does not depend on any axioms" "$tmp/axiom-out" || true)"
if [ "$reported" -ne "$(wc -l < "$tmp/inventory")" ]; then
  echo "axiom result count $reported does not match the inventory" >&2; exit 1
fi
if tr '\n' ' ' < "$tmp/axiom-out" | grep -o 'depends on axioms: \[[^]]*\]' \
    | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/^ *//; s/ *$//; s/\.{.*}$//' | sed '/^$/d' | sort -u \
    | grep -v -x -E "$ALLOWED"; then
  echo "unexpected axiom dependency" >&2; exit 1
fi
echo "axiom audit: PASS (only propext, Classical.choice, Quot.sound)"

# 4b. Owned audit: every constant the package's modules define, private helpers included (G7, G13).
bash scripts/owned_audit.sh "$PKG" "$ALLOWED"
bash scripts/owned_audit.sh WalshIntegralChallenge "$ALLOWED"

# 5. Elaborated types.
lake lean "$TEST/TypeCheck.lean" > "$tmp/types"
echo "type check: PASS ($(grep -c "^@\?$PKG" "$tmp/types" || true) declarations printed)"

# 6. Usage examples must compile.
lake lean "$TEST/Examples.lean"
echo "usage examples: PASS"

# 7. Negative controls (G8, G17): at least one. For each `$TEST/NegX.lean.disabled` the positive part lives in
#    the witness `$TEST/NegXWitness.lean` (module `$TEST.NegXWitness`, in a `$TEST` lean_lib), which must compile
#    clean on its own first; the control imports it and must fail with exit 1, every error `unsolved goals`
#    and every goal ending in exactly `⊢ False` (lake_guard.sh witness / negative-control print why not).
case "$NEG_CONTROLS" in strict) neg_flag=() ;; legacy) neg_flag=(--legacy) ;;
  *) echo "NEG_CONTROLS must be strict or legacy, not '$NEG_CONTROLS'" >&2; exit 1 ;; esac
echo "negative controls: $NEG_CONTROLS"
# Preserve raw diagnostics outside the source tree and outside the positive receipt
# log. Each log digest is sealed below; the unchanged strict parser judges it.
strict_log_dir="${LIBRARY_AUDIT_DIR:?set an absent external evidence directory}.strict"
[ ! -e "$strict_log_dir" ] || { echo "strict diagnostic directory already exists: $strict_log_dir" >&2; exit 1; }
mkdir -p "$strict_log_dir"
negs=("$TEST"/*.lean.disabled)
[ "${#negs[@]}" -gt 0 ] || { echo "no negative control in $TEST/*.lean.disabled" >&2; exit 1; }
for neg in "${negs[@]}"; do
  base="${neg%.lean.disabled}"; witness_args=()
  witness_log="$strict_log_dir/${base##*/}-witness.log"
  negative_log="$strict_log_dir/${base##*/}-negative.log"
  if [ -f "${base}Witness.lean" ]; then
    set +e; lake lean "${base}Witness.lean" > "$witness_log" 2>&1; wexit=$?; set -e
    bash scripts/lake_guard.sh witness "${base}Witness.lean" "$witness_log" "$wexit" \
      || { cat "$witness_log" >&2; exit 1; }
    echo "strict-witness-log: ${base##*/} sha256: $(sha256sum "$witness_log" | cut -d' ' -f1)"
    witness_args=("${base//\//.}Witness")
  fi
  # The control's own diagnostics are printed only on refusal: its `error:` lines are expected, not a failure.
  set +e; lake lean "$neg" > "$negative_log" 2>&1; nexit=$?; set -e
  bash scripts/lake_guard.sh negative-control ${neg_flag[@]+"${neg_flag[@]}"} "$neg" "$negative_log" "$nexit" \
    ${witness_args[@]+"${witness_args[@]}"} || { cat "$negative_log" >&2; exit 1; }
  echo "strict-negative-log: ${base##*/} sha256: $(sha256sum "$negative_log" | cut -d' ' -f1)"
done

# Keep full raw native reports/controls; the receipt binds their hashes in the sealed verify log.
LIBRARY_AUDIT_DIR=${LIBRARY_AUDIT_DIR:?set an absent external evidence directory for native reports}
export LIBRARY_AUDIT_DIR
python3 scripts/native_owned.py

echo "verification gate: PASS"
