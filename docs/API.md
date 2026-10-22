# API guide

Import `WalshIntegral` for the full package. Individual imports follow the module map in the README.

The main construction starts with `WalshIntegral.WhiteNoise.IsWhiteNoise P F W`. It asserts isometry, Gaussian laws, adapted versions and whole-future independence. `exists_whiteNoise` and `exists_completed_whiteNoise` supply concrete probability-space realizations.

`WalshIntegral.Integral.PredL2 F P` consists of L² classes with predictable representatives. `walshL2 hW` is the unique linear isometric extension agreeing with random elementary integrands; `integral_sq_walshL2` is the Itô isometry. For raw fields use `InDomain` and `walshT`. Off its domain, `walshT` is defined to be zero; this convention does not establish integrability.

`WalshIntegral.MomentBound.eLpNorm_walshT_sq_le` assumes real p≥2, predictable measurability and finite `mixedNormSq`. These assumptions imply the genuine L² domain. Its exact constant is `bdgConst p = p - 1` (`bdgConst_eq`), with linear growth in p (`bdgConst_le_self`). The proof inducts the Gaussian slab step `WalshIntegral.GaussianStep.eLpNorm_add_gaussian_slab_sq_le` over a time grid; that step rests on Stein's identity `WalshIntegral.GaussianStein.integral_mul_eq_variance_mul_integral_deriv`.

`WalshIntegral.Modification.CausalKernel` packages a Borel causal kernel with deterministic L² membership and L² continuity at every real output. `exists_predictable_modification` assumes a predictable input and finite `kernelVariance` at every output, and gives a predictable version equal almost surely at each output separately. Neither a common exceptional set nor sample continuity is concluded.

`WalshIntegral.Predictable.isPredictable_parametric_integral` concerns predictable measurability of the totalized Bochner integral. Integrability must be established separately when using it as an integral representation.

Exact public theorem names are in [THEOREM_INVENTORY.txt](../THEOREM_INVENTORY.txt); the Lean source statements are authoritative.
