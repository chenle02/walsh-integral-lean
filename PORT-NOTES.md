# Port notes: sharp-bdg-linear onto the module-system main

Local branch `sharp-bdg-linear-modules`, created from `origin/main` 2a27a12 (0.9.0, module-system port
and package-qualified roots). It carries the 10 commits of `origin/sharp-bdg-linear` (tip f19eb7f,
merge base c111340) that main lacks. Nothing was pushed, tagged or released.

## Commits

| Here | From | Subject | Conflict / change |
|---|---|---|---|
| fe4a9bc | 115a1b4 | GaussianStein (O1) | none |
| 9f3dfa7 | c885642 | Rio first-order comparison (O2a) | none (auto-merged with main's Rio module header) |
| e997f5a | 3a7f9e7 | GaussianStep (O2b) | none |
| cb1c4b4 | 27e7506 | bdgConst p = p - 1 (O3) | MomentBound.lean header: kept main's `module` / `public import` / `@[expose] public section` and added `public import WalshIntegral.GaussianStep` |
| bc706d1 | (new) | module headers for GaussianStein and GaussianStep | GaussianStein: `module`, `public import Mathlib`, `public section` (theorems only, as Rio). GaussianStep: `public import` of Rio, Integral, GaussianStein and `@[expose] public section` (it defines `SteinIdentity`) |
| acbd638 | 263d04c | registration; inventory 122 -> 152 | WalshIntegral.lean: main's `public import` umbrella plus GaussianStein and GaussianStep. Inventory, TypeCheck and AxiomCheck re-checked against main (122 + 30 = 152; source == inventory == #check == #print axioms) |
| d9f413a | c0998fc | Challenge reference refresh | Challenge.lean is gone on main: registered the two new modules in WalshIntegralChallenge.lean; the four reference files under WalshIntegralChallenge/Reference/WalshIntegral/ are the library files with `public import WalshIntegral.` rewritten to `public import WalshIntegralChallenge.Reference.WalshIntegral.` |
| f35751e | 4a96400 | docs | README.md and docs/status.md: kept main's 0.8.0/0.9.0 text and added an "Unreleased (after 0.9.0)" paragraph; module table merged. CHANGELOG.md is new (122 -> 152). The generated lean-pkg page block in README.md (between the page markers) was not regenerated |
| e73d57d | f19eb7f | drop worker audit scratch files | none |

Skipped: 64a7a4a (the same GaussianStein file brought onto the w2 branch, duplicate of 115a1b4) and the
merge commit 7d9410c.

The library sources GaussianStein, GaussianStep, MomentBound and Rio differ from f19eb7f only in their
import/section header lines. No statement, proof, sorry or axiom was changed or added.

## Verification (Home-Dell, Lean v4.35.0, Mathlib v4.35.0, LEAN_NUM_THREADS=3)

- `lake exe cache get`: cache already present; `lake build WalshIntegral`: success, 59 s.
- `bash verify.sh LOG` (LIBRARY_AUDIT_DIR outside the tree) at e73d57d: `verification gate: PASS`,
  19 min 26 s wall. Placeholder audit PASS; fresh build PASS (40 own modules built); LEAN_PATH shadow
  check PASS; theorem inventory PASS (152); axiom audit PASS (propext, Classical.choice, Quot.sound);
  owned audit PASS (500 owned constants) for WalshIntegral and for WalshIntegralChallenge; type check
  PASS (152); usage examples PASS; 10/10 strict negative controls and witnesses PASS (NegBdgConstZero
  included); native owned cones (production 598, reference 500), compiled escape controls
  (EscapePositive, EscapeNegative, EscapeNative) and leanchecker module replay PASS; claim axioms 14/14;
  sorry-count 0.
- `lean-pkg receipt comparator --repo . --evidence-dir <outside>` at e73d57d: 14/14 comparator.json
  slots accepted (toolchain mechanism, Lean default kernel). The receipt file it wrote into
  `.lean-receipts/` was moved out of the tree and not committed.
- Statement identity against f19eb7f (separate worktree build): `#check @` with `pp.all` for all 140
  f19eb7f inventory names plus `#print` of gaussianMoment, bdgConst, mixedNormSq, elementarySum,
  elementarySumIntegral, slabVariance, truncateField and SteinIdentity: byte-identical output. A
  metaprogram hashing the type of every `WalshIntegral.*` constant (240 in f19eb7f, 252 here): all 240
  present with the same kind and type hash; every def value hash equal except
  `WhiteNoise.completedNaturalFiltration`, whose body changed in main's module port 17a10f4 (type
  unchanged), not in this port.

## Not done

- No push, tag, release, registry write or lower-tier receipt; the lean-pkg page block, docs/*.html and
  formalization.yaml derived keys are left for regeneration at release time.
- The companion has not been rebuilt against this branch.
