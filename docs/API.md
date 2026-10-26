# API guide

Import `WalshIntegral` for the full package. Individual imports follow the module map in the README.

The main construction starts with `WalshIntegral.WhiteNoise.IsWhiteNoise P F W`. It asserts isometry, Gaussian laws, adapted versions and whole-future independence. `exists_whiteNoise` and `exists_completed_whiteNoise` supply concrete probability-space realizations.

`WalshIntegral.Integral.PredL2 F P` consists of L² classes with predictable representatives. `walshL2 hW` is the unique linear isometric extension agreeing with random elementary integrands; `integral_sq_walshL2` is the Itô isometry. For raw fields use `InDomain` and `walshT`. Off its domain, `walshT` is defined to be zero; this convention does not establish integrability.

`WalshIntegral.MomentBound.eLpNorm_walshT_sq_le` assumes real p≥2, predictable measurability and finite `mixedNormSq`. These assumptions imply the genuine L² domain. Its exact constant is `bdgConst p = (p - 1) * gaussianMoment p ^ 2`, with quadratic growth in p.

`WalshIntegral.Modification.CausalKernel` packages a Borel causal kernel with deterministic L² membership and L² continuity at every real output. `exists_predictable_modification` assumes a predictable input and finite `kernelVariance` at every output, and gives a predictable version equal almost surely at each output separately. Neither a common exceptional set nor sample continuity is concluded.

Added in 0.8.0 (verified at `35bc9935bea9`): `integral_walshL2` states that the Walsh integral of every `PredL2` class has expectation zero, `integral_elementaryIntegral` is the elementary case, and `integral_walshT` gives expectation zero of the totalized integral for every field (off the domain it is identically zero, so this is not evidence of integrability). `exists_adapted_representative` chooses, for each `PredL2` class, a predictable representative whose sample sections at every time t ≥ 0 are `F t`-measurable.

Added in 0.8.0 (verified at `35bc9935bea9`): `WalshIntegral.Predictable.measurable_timeSection` states that a predictable field is adapted: at every t ≥ 0 and space point x, `ω ↦ f (t, x, ω)` is `F t`-measurable. `measurable_timeSection_of_le` is the version at real time r ≤ u with level `F u`.

`WalshIntegral.Predictable.isPredictable_parametric_integral` concerns predictable measurability of the totalized Bochner integral. Integrability must be established separately when using it as an integral representation.

Exact public theorem names are in [THEOREM_INVENTORY.txt](../THEOREM_INVENTORY.txt); the Lean source statements are authoritative.
