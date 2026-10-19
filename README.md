<div align="center">

<img src="docs/assets/mark.svg" width="88" height="88" alt="WalshIntegral abstract mark">

# WalshIntegral

[Documentation](https://chenle02.github.io/walsh-integral-lean/) · [API](https://chenle02.github.io/walsh-integral-lean/api.html) · [Verification](#verification-at-a-glance)

</div>

A Lean 4 library for space-time white noise, predictable integration, real-p moment estimates and predictable versions of stochastic convolutions. It depends on Mathlib and has no paper-specific dependency.

**Source API 0.6.0.** This source contains 110 inventoried public theorems across seven library modules, including 12 implementation lemmas used by the isometric extension. It exposes 6 curated reusable claims. The generated verification record below identifies actual source-bound evidence.

## Mathematical scope

- Construct isonormal space-time white noise on a countable Gaussian product probability space and its completion, with adapted representatives and independence of the whole future from the past.
- Construct the Walsh integral as the unique linear isometry from predictable L² classes that agrees with bounded random elementary integrands. Prove its Itô isometry and almost-sure congruence and causality laws.
- Bound the Lᵖ norm for every real p≥2 with finite mixed norm. The squared-norm bound uses the explicit constant `(p - 1) * gaussianMoment p ^ 2`, which grows quadratically in p. The sharp linear growth bound is outside this release's scope.
- Construct predictable modifications of stochastic convolutions for deterministic causal kernels with the stated L² regularity, on the full finite-variance domain. Equality holds almost surely separately at each output point. Sample continuity, indistinguishability and a common exceptional set over all output points require additional results.

`walshT` is zero outside its predictable finite-variance domain. Its substantive integration theorems state the hypotheses that place their inputs in that domain. Chosen representatives of L² classes are treated modulo almost-everywhere equality.

## Use

The current source pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Keep these exact pins together. Import `WalshIntegral` for the complete library or an individual module below. Use the same toolchain in a downstream Lake project and select a published tag or exact commit from the repository verification record.

| Module | Main interface |
|---|---|
| `WalshIntegral.GaussianSeries` | Gaussian coordinates and orthonormal-series construction |
| `WalshIntegral.WhiteNoise` | `IsWhiteNoise`, Gaussian rectangle laws and existence |
| `WalshIntegral.Predictable` | `predictableSigma` and predictable causal parametric integration |
| `WalshIntegral.Integral` | `InDomain`, `PredL2`, `walshL2`, `walshT`, Itô isometry and uniqueness |
| `WalshIntegral.Rio` | Real-p martingale-difference moment inequality |
| `WalshIntegral.MomentBound` | `mixedNormSq` and `eLpNorm_walshT_sq_le` |
| `WalshIntegral.Modification` | `CausalKernel` and `exists_predictable_modification` |

The filtration is indexed by nonnegative real times; predictable fields use real time, space and sample coordinates. Integration uses positive-time Lebesgue measure times spatial Lebesgue measure times the probability measure. No right-continuity assumption on the filtration is imposed by the modification theorem.

## Verification

`./verify.sh` builds the library from fresh package outputs, checks import ownership and the exact public theorem inventory, audits axioms of public and all owned constants, compiles usage examples and checks ten negative fixtures with their positive witnesses. The allowed foundational axioms are `propext`, `Classical.choice` and `Quot.sound`.

The generated verification block and canonical receipts identify the scientific commit and actual checks. Successful compilation establishes the elaborated Lean statements; readers should check their hypotheses and the scope described above.

## License

Apache-2.0; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

See the [verification recipe](docs/verification.md) for the exact command, required output variables and retained evidence.

<!-- lean-pkg:page:begin -->
## Verification at a glance

No verification record has been generated for this staging source.
<!-- lean-pkg:page:end -->
