# WalshIntegral — source API 0.8.0

Constructed space-time white noise, the Walsh L² integral, explicit real-p bounds and predictable convolution versions.

Mathematical capsule:
- White noise on the countable Gaussian product and its completion, with compatible natural filtration.
- The unique predictable L² isometric extension agreeing with bounded random elementary integrands.
- For real p ≥ 2 and finite mixed norm: the squared-norm coefficient (p − 1) · gaussianMoment(p)², with quadratic growth in p.
- For regular deterministic causal kernels and finite variance at every output: a predictable version, equal almost surely at each output separately.
- Added in 0.8.0 (verified at 35bc9935bea9): mean zero of the Walsh integral and of the totalized integral; predictable fields have F t-measurable time sections and every predictable L² class has an adapted representative.

Not established:
- A common exceptional set over every output, indistinguishability or sample-continuous paths.
- The sharp linear-in-p squared-norm bound or a general Itô theory.
- An arbitrary probability-space realization or an SPDE well-posedness theorem.

Verification authority: https://github.com/chenle02/walsh-integral-lean/blob/main/README.md#verification-at-a-glance
Canonical receipts: https://github.com/chenle02/walsh-integral-lean/tree/main/.lean-receipts
These static docs do not assert live release/CI/acceptance state. Each receipt covers only its named scientific content.
