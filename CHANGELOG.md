# Changelog

## Unreleased (after 0.9.0)

- Strengthened constant: `WalshIntegral.MomentBound.bdgConst p = p - 1` (previously
  `(p - 1) * gaussianMoment p ^ 2`, quadratic in p). Every public statement keeps its form; only the
  constant value changes. New `bdgConst_eq`, `bdgConst_le_self`, `eLpNorm_slabVariance_le` and
  `eLpNorm_add_slab_sq_le`.
- New modules `WalshIntegral.GaussianStein` (one-dimensional Gaussian integration by parts) and
  `WalshIntegral.GaussianStep` (the Gaussian slab step with constant p − 1), in module form, with
  reference copies under `WalshIntegralChallenge.Reference.WalshIntegral`.
- `WalshIntegral.Rio`: six helpers made public and a first-order comparison added
  (`first_order_power_bound`, `eLpNorm_add_sq_le_of_deriv_le`).
- Public theorem inventory: 122 → 152.

Earlier releases are recorded in README.md, docs/status.md and CITATION.cff.
