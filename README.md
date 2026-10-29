<div align="center">

<img src="docs/assets/mark.svg" width="88" height="88" alt="WalshIntegral abstract mark">

# WalshIntegral

[Documentation](https://chenle02.github.io/walsh-integral-lean/) · [API](https://chenle02.github.io/walsh-integral-lean/api.html) · [Verification](#verification-at-a-glance)

</div>

Verified revision `cca30eeee631`: generic integral-increment identities and L² convergence utilities bring the public inventory to 122 theorems and 14 curated claims. The fresh native gate and all 14 official three-kernel statement comparisons passed. Published release records below retain their original source scope.

A Lean 4 library for space-time white noise, predictable integration, real-p moment estimates and predictable versions of stochastic convolutions. It depends on Mathlib and has no paper-specific dependency.

**Source API 0.8.0.** Version 0.8.0 adds, with every 0.7.0 statement unchanged: mean zero of the Walsh integral (`integral_walshL2` on predictable L² classes, `integral_elementaryIntegral` on elementary integrands, and `integral_walshT` for the totalized integral and every field), and adaptedness of predictable fields (`measurable_timeSection`, `measurable_timeSection_of_le`: sample sections at time t ≥ 0 are `F t`-measurable; `exists_adapted_representative`: every predictable L² class has such an adapted predictable representative). Scientific source `35bc9935bea9` (0.8.0) passed both verification tiers; receipts for 0.7.0 and earlier remain historical. Version 0.7.0 ported every file to the Lean module system (`module` headers, `public import`, `@[expose]` on definitions), so a downstream `module` file can `public import WalshIntegral`.

## Mathematical scope

- Construct isonormal space-time white noise on a countable Gaussian product probability space and its completion, with adapted representatives and independence of the whole future from the past.
- Construct the Walsh integral as the unique linear isometry from predictable L² classes that agrees with bounded random elementary integrands. Prove its Itô isometry and almost-sure congruence and causality laws.
- Added in 0.8.0 (verified at `35bc9935bea9`): the Walsh integral has mean zero on predictable L² classes, and the totalized integral `walshT` has mean zero for every field. Predictable fields are adapted: at every time t ≥ 0 and space point x the sample section is `F t`-measurable, and every predictable L² class has an adapted predictable representative.
- Bound the Lᵖ norm for every real p≥2 with finite mixed norm. The squared-norm bound uses the explicit constant `(p - 1) * gaussianMoment p ^ 2`, which grows quadratically in p. The sharp linear growth bound is outside this release's scope.
- Construct predictable modifications of stochastic convolutions for deterministic causal kernels with the stated L² regularity, on the full finite-variance domain. Equality holds almost surely separately at each output point. Sample continuity, indistinguishability and a common exceptional set over all output points require additional results.

`walshT` is zero outside its predictable finite-variance domain. Its substantive integration theorems state the hypotheses that place their inputs in that domain. Chosen representatives of L² classes are treated modulo almost-everywhere equality.

## Use

The current source pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Keep these exact pins together. Import `WalshIntegral` for the complete library or an individual module below. Use the same toolchain in a downstream Lake project and select a published tag or exact commit from the repository verification record.

| Module | Main interface |
|---|---|
| `WalshIntegral.GaussianSeries` | Gaussian coordinates and orthonormal-series construction |
| `WalshIntegral.WhiteNoise` | `IsWhiteNoise`, Gaussian rectangle laws and existence |
| `WalshIntegral.Predictable` | `predictableSigma`, predictable causal parametric integration and adapted time sections |
| `WalshIntegral.Integral` | `InDomain`, `PredL2`, `walshL2`, `walshT`, Itô isometry, uniqueness and mean zero |
| `WalshIntegral.Rio` | Real-p martingale-difference moment inequality |
| `WalshIntegral.MomentBound` | `mixedNormSq` and `eLpNorm_walshT_sq_le` |
| `WalshIntegral.Modification` | `CausalKernel` and `exists_predictable_modification` |

The filtration is indexed by nonnegative real times; predictable fields use real time, space and sample coordinates. Integration uses positive-time Lebesgue measure times spatial Lebesgue measure times the probability measure. No right-continuity assumption on the filtration is imposed by the modification theorem.

## Verification

Source `35bc9935bea9` passed the complete local verifier and independent three-kernel comparison for all 8 curated claims. The verifier checks the exact 116-theorem inventory, compiler-owned declaration axiom dependencies (including private/generated helpers; 538 production declarations in 24 modules and 440 reference declarations in 8 modules), elaborated types, usage examples and ten strict negative fixtures with separately compiled witnesses. Its permitted axioms are `Classical.choice`, `Quot.sound` and `propext`. The [trust guide](docs/trust.md) explains the scope of each check. The generated record below retains the scientific source snapshot’s earlier staging summary and reports the current receipt-backed results. Proof checking does not validate this prose or remove hypotheses from a theorem.

The generated verification block and canonical receipts identify the scientific commit and actual checks. Successful compilation establishes the elaborated Lean statements; readers should check their hypotheses and the scope described above.

## License

Apache-2.0; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
The verification record identifies the executors for this release. See the [historical resource acknowledgment](docs/citation.md#historical-compute) for earlier development.

See the [verification recipe](docs/verification.md) for the exact command, required output variables and retained evidence.

<!-- lean-pkg:page:begin -->
<!-- Generated by `lean-pkg page walsh-integral` from coverage.yaml, claims.yaml, the claims ledger and the receipts committed under .lean-receipts/. Do not edit between the markers: change the data and run `lean-pkg page walsh-integral --write`. -->

## Verification at a glance

**How to read this page.** Lean has checked every step of the proofs listed here. Each result is exactly its Lean statement: read the statements below to see what is proved. The titles, the words and the notes are the authors' description, which Lean does not check.

Space-time white noise, predictable L² Walsh integration, explicit real-p moment bounds and predictable convolution modifications. Exact hypotheses and separate almost-sure equality are retained.

- Main results: 14; verified: 14 of 14.

## Main results

### White noise exists on the completed Gaussian product

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
There exist a compatible isonormal Gaussian white noise, its completed natural filtration, and a countable orthonormal-series representation on the completed product of standard Gaussian laws.
```

**In Lean.** `WalshIntegral.WhiteNoise.exists_completed_whiteNoise` in [WalshIntegralChallenge/Reference/WalshIntegral/WhiteNoise.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/WhiteNoise.lean#L463): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem exists_completed_whiteNoise :
    ∃ (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace CompletedSample))
      (W : H →L[ℝ] Lp ℝ 2 completedProductGaussian)
      (e : HilbertBasis ℕ ℝ H) (ξ : ℕ → Lp ℝ 2 completedProductGaussian),
      IsWhiteNoise completedProductGaussian F W ∧
      IsCompletedNatural completedProductGaussian F W ∧
      (∀ n, (fun ω => ξ n ω) =ᵐ[completedProductGaussian] (fun ω => ω n)) ∧
      ∀ h : H, Tendsto (fun N => ∑ n ∈ Finset.range N, (inner ℝ h (e n)) • ξ n)
        atTop (𝓝 (W h))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The Walsh integral satisfies the Itô isometry

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every compatible white noise and predictable square-integrable input class, the expected square of its Walsh integral equals its squared time-space-sample norm.
```

**In Lean.** `WalshIntegral.Integral.integral_sq_walshL2` in [WalshIntegralChallenge/Reference/WalshIntegral/Integral.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/Integral.lean#L622): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_sq_walshL2 (hW : IsWhiteNoise P F W) (G : PredL2 F P) :
    (∫ ω, (walshL2 hW G ω) ^ 2 ∂P) =
      ∫ q : ℝ × ℝ × Ω, (G.val q) ^ 2 ∂spaceTimeSample P
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Elementary agreement determines the integral uniquely

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
A continuous linear map from predictable L² classes to sample L² that agrees with integration on every bounded random elementary integrand equals the constructed Walsh integral.
```

**In Lean.** `WalshIntegral.Integral.walshL2_unique` in [WalshIntegralChallenge/Reference/WalshIntegral/Integral.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/Integral.lean#L630): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem walshL2_unique (hW : IsWhiteNoise P F W)
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P)
    (hJ : ∀ e : Elementary F, J (elementaryClass P e) = elementaryIntegral W e) :
    J = (walshL2 hW).toContinuousLinearMap
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Real-p martingale differences satisfy Rio’s inequality

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let p≥2 be real. For a finite adapted Lᵖ martingale-difference sequence centered conditionally on the preceding filtration, the squared Lᵖ norm of its sum is at most p−1 times the sum of its squared Lᵖ norms.
```

**In Lean.** `WalshIntegral.Rio.eLpNorm_sum_sq_le` in [WalshIntegralChallenge/Reference/WalshIntegral/Rio.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/Rio.lean#L466): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem eLpNorm_sum_sq_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    {p : ℝ} (hp : 2 ≤ p) (d : ℕ → Ω → ℝ)
    (hadapted : ∀ k, StronglyMeasurable[ℱ (k + 1)] (d k))
    (hLp : ∀ k, MemLp (d k) (ENNReal.ofReal p) P)
    (hcentered : ∀ k, P[d k | ℱ k] =ᵐ[P] (0 : Ω → ℝ)) (n : ℕ) :
    eLpNorm (fun ω => ∑ k ∈ Finset.range n, d k ω) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (p - 1) *
        ∑ k ∈ Finset.range n, eLpNorm (d k) (ENNReal.ofReal p) P ^ 2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The Walsh integral has an explicit real-p mixed-norm estimate

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For real p≥2, a predictable input with finite mixed norm belongs to the genuine L² integration domain. Its squared Lᵖ Walsh norm is bounded by bdgConst(p) times mixedNormSq, where bdgConst(p)=(p−1)·gaussianMoment(p)². This constant grows quadratically in p.
```

**In Lean.** `WalshIntegral.MomentBound.eLpNorm_walshT_sq_le` in [WalshIntegralChallenge/Reference/WalshIntegral/MomentBound.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/MomentBound.lean#L1546): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem eLpNorm_walshT_sq_le (hW : IsWhiteNoise P F W) {p : ℝ} (hp : 2 ≤ p)
    (G : ℝ → ℝ → Ω → ℝ)
    (hG : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2))
    (hfin : mixedNormSq P p G < ⊤) :
    eLpNorm (walshT hW G) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (bdgConst p) * mixedNormSq P p G
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Finite-variance convolutions admit predictable modifications

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For a jointly measurable causal kernel with deterministic L² membership and L² continuity at every real output, every predictable input with finite kernel variance at every output has a predictable stochastic-convolution version. Equality holds almost surely separately at each output; no common exceptional set or sample continuity is asserted.
```

**In Lean.** `WalshIntegral.Modification.exists_predictable_modification` in [WalshIntegralChallenge/Reference/WalshIntegral/Modification.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/Modification.lean#L811): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem exists_predictable_modification (hW : IsWhiteNoise P F W)
    (K : CausalKernel) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2))
    (hfin : ∀ t x, kernelVariance P K Φ t x < ⊤) :
    ∃ Ψ : ℝ → ℝ → Ω → ℝ,
      Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => Ψ q.1 q.2.1 q.2.2) ∧
        ∀ t x, walshT hW (kernelField K t x Φ) =ᵐ[P] Ψ t x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The Walsh integral has mean zero

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every compatible white noise and predictable square-integrable input class, the expectation of its Walsh integral is zero. The totalized integral has expectation zero for every field.
```

**In Lean.** `WalshIntegral.Integral.integral_walshL2` in [WalshIntegralChallenge/Reference/WalshIntegral/Integral.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/Integral.lean#L803): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_walshL2 (hW : IsWhiteNoise P F W) (G : PredL2 F P) :
    ∫ ω, walshL2 hW G ω ∂P = 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Predictable fields are adapted

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
A field measurable for the predictable sigma-algebra has, at every time t≥0 and space point x, an F t-measurable sample section. Every predictable L² class has such an adapted predictable representative.
```

**In Lean.** `WalshIntegral.Predictable.measurable_timeSection` in [WalshIntegralChallenge/Reference/WalshIntegral/Predictable.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/Predictable.lean#L167): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem measurable_timeSection (F : Filtration ℝ≥0 mΩ)
    {f : ℝ × ℝ × Ω → ℝ} (hf : Measurable[predictableSigma F] f)
    (t : ℝ≥0) (x : ℝ) :
    Measurable[F t] (fun ω => f ((t : ℝ), x, ω))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### walshT sub eLpNorm

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Difference L2 isometry for totalized representatives on their explicit genuine integration domains.
```

**In Lean.** `WalshIntegral.IntegralIncrements.walshT_sub_eLpNorm` in [WalshIntegralChallenge/Reference/WalshIntegral/IntegralIncrements.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/IntegralIncrements.lean#L53): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem walshT_sub_eLpNorm [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsWhiteNoise P F W)
    (G G' : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G) (hG' : InDomain F P G') :
    eLpNorm (fun ω => walshT hW G ω - walshT hW G' ω) 2 P =
      eLpNorm (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2 - G' q.1 q.2.1 q.2.2)
        2 (spaceTimeSample P)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### enorm sub sq eq iter

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Exact iterated weighted increment formula for actual predictable L2 class witnesses, with no additional field continuity or measurability premise.
```

**In Lean.** `WalshIntegral.IntegralIncrements.enorm_sub_sq_eq_iter` in [WalshIntegralChallenge/Reference/WalshIntegral/IntegralIncrements.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/IntegralIncrements.lean#L80): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem enorm_sub_sq_eq_iter [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W)
    (g k : PredL2 F P) (a b : ℝ × ℝ → ℝ) (Φ : ℝ → ℝ → Ω → ℝ)
    (hg : (fun q => (g : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P]
      (fun q => a (q.1,q.2.1)*Φ q.1 q.2.1 q.2.2))
    (hk : (fun q => (k : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P]
      (fun q => b (q.1,q.2.1)*Φ q.1 q.2.1 q.2.2)) :
    ‖walshL2 hW g - walshL2 hW k‖ₑ^2 =
      ∫⁻ s in Ioi 0, ∫⁻ y, ENNReal.ofReal ((a (s,y)-b (s,y))^2)*
        ∫⁻ ω, ‖Φ s y ω‖ₑ^2 ∂P
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### enorm sub sq eq prod

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Product-measure weighted increment formula for actual predictable L2 witnesses and explicit measurable scalar/moment weights.
```

**In Lean.** `WalshIntegral.IntegralIncrements.enorm_sub_sq_eq_prod` in [WalshIntegralChallenge/Reference/WalshIntegral/IntegralIncrements.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/IntegralIncrements.lean#L120): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem enorm_sub_sq_eq_prod [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W)
    (g k : PredL2 F P) (a b : ℝ × ℝ → ℝ) (Φ : ℝ → ℝ → Ω → ℝ)
    (hg : (fun q => (g : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P]
      (fun q => a (q.1,q.2.1)*Φ q.1 q.2.1 q.2.2))
    (hk : (fun q => (k : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P]
      (fun q => b (q.1,q.2.1)*Φ q.1 q.2.1 q.2.2))
    (ha : Measurable a) (hb : Measurable b)
    (hΦ : Measurable (fun q : ℝ × ℝ => ∫⁻ ω, ‖Φ q.1 q.2 ω‖ₑ^2 ∂P)) :
    ‖walshL2 hW g - walshL2 hW k‖ₑ^2 =
      ∫⁻ q, ENNReal.ofReal ((a q-b q)^2)*(∫⁻ ω, ‖Φ q.1 q.2 ω‖ₑ^2 ∂P) ∂timeSpaceVolume
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### l2 tendsto of summable differences

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Summable actual L2 differences and full-sequence pointwise a.e. convergence identify the same L2 limit on a finite measure space.
```

**In Lean.** `WalshIntegral.LpConvergence.l2_tendsto_of_summable_differences` in [WalshIntegralChallenge/Reference/WalshIntegral/LpConvergence.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/LpConvergence.lean#L29): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem l2_tendsto_of_summable_differences [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 P) (g : Ω → ℝ)
    (_hg : AEStronglyMeasurable g P)
    (hsum : (∑' n, eLpNorm (f (n + 1) - f n) 2 P) ≠ ⊤)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    MemLp g 2 P ∧ Tendsto (fun n => eLpNorm (f n - g) 2 P) atTop (𝓝 0)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### eLpNorm two le of moment bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Square-root moment envelope bounds the L2 seminorm, without division by the envelope.
```

**In Lean.** `WalshIntegral.LpConvergence.eLpNorm_two_le_of_moment_bound` in [WalshIntegralChallenge/Reference/WalshIntegral/LpConvergence.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/LpConvergence.lean#L59): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem eLpNorm_two_le_of_moment_bound {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) {a : ℝ} (ha : 0 ≤ a) {C : ℝ≥0∞}
    (hbound : ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal a * C) :
    eLpNorm f 2 P ≤ ENNReal.ofReal (a ^ (1 / 2 : ℝ)) * C ^ (1 / 2 : ℝ)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### tsum eLpNorm two lt top of moment bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Summable square-root coefficient envelopes bound the sum of L2 seminorms, including zero finite profile constant.
```

**In Lean.** `WalshIntegral.LpConvergence.tsum_eLpNorm_two_lt_top_of_moment_bound` in [WalshIntegralChallenge/Reference/WalshIntegral/LpConvergence.lean](https://github.com/chenle02/walsh-integral-lean/blob/b1ae611c8e9c4b9baf8904f07d442b3c8f32194a/WalshIntegralChallenge/Reference/WalshIntegral/LpConvergence.lean#L74): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem tsum_eLpNorm_two_lt_top_of_moment_bound (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hsum : Summable (fun n => a n ^ (1 / 2 : ℝ)))
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ n, ∫⁻ ω, ‖f n ω‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (a n) * C) :
    (∑' n, eLpNorm (f n) 2 P) < ⊤
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

## What the checks establish

- **Every proof is checked by Lean.** The package builds; no `sorry` (an unfinished proof) remains; the only axioms used are `Classical.choice`, `Quot.sound`, `propext` (allowed: `propext`, `Quot.sound`, `Classical.choice`).
- **The statements shown are the ones proved.** For 14 statement(s), a second checker (comparator) confirmed that the proof proves exactly the statement shown, with only the permitted axioms, and independent Lean kernels replayed the proof.
- **Not checked by any tool:** that a title or note describes its Lean statement. A definition listed under *Definitions checked by a person* is compared by name and type only.

The full account of what each check covers and what it takes on trust is lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

## How this was checked

- lean-pkg's claims ledger: **ready**, every required claim is closed by the recorded receipts; 14 of 14 required claim(s) verified (`sha256:ae8b2f6a8d79cc2b…`).
- Build check (`lean-pkg gate`) at commit `b1ae611c8e9c`: `sorry` count 0; axioms used: `Classical.choice`, `Quot.sound`, `propext`.
- Axioms of every claim: read from the built environment (Lean's `collectAxioms`) for all 14 claim(s) in `claims.yaml`, not only the theorems the build prints; none uses an axiom beyond `propext`, `Quot.sound` and `Classical.choice`.
- Statement comparison (comparator) at commit `b1ae611c8e9c`: 1 configuration(s), 14 theorem(s) compared (each Challenge statement against its Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definitions compared by name only: none.

### Receipts

| Receipt | Check | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/128b3637c14b-comparator.json` | statement comparison | `128b3637c14b` | 2026-10-19 | — | `f1b1928d7c24c874834c2133520598d0a43b14ce40ca993c5fbbbb31b71f93cd` |
| `.lean-receipts/128b3637c14b-systemd-user-walsh-final-cold-official2-20261019.service-9e3b6f62ab46485ca497dbb0b7ea9799-h-24e00fc5da6c.json` | build | `128b3637c14b` | 2026-10-19 | — | `597109e29fab5d70406061bc46c021aa6a13ff756b3e0389852cb00dda841f11` |
| `.lean-receipts/35bc9935bea9-comparator.json` | statement comparison | `35bc9935bea9` | 2026-10-26 | — | `2511d8a1221034e4b904702d5cb9858bff387a3e7c0b06f2c195fe8e5fa0a8aa` |
| `.lean-receipts/35bc9935bea9-systemd-user-walsh-integral-v080-p14s.service-87df036883fc45e9b3360eb42299fc1b-h-2db2e0fa6029.json` | build | `35bc9935bea9` | 2026-10-26 | — | `676d8f28aabca4c2c6bff0116561da1d0f17fdf408078444229a9daa3d378bf1` |
| `.lean-receipts/76a84faf9b08-comparator.json` | statement comparison | `76a84faf9b08` | 2026-10-26 | — | `46d53d051da35fcb74578f5466e54148ee07b12ca5a4dbeec93cc8ddfd411dd5` |
| `.lean-receipts/76a84faf9b08-systemd-user-walsh-integral-v070-p14s-2.service-451c901e09a64116b71dec47c2a18723-h-2db2e0fa6029.json` | build | `76a84faf9b08` | 2026-10-26 | — | `27c8e710d348a29541ff9d1cdbf0cd6cd55ebe32edfa7af221d6333d0dbd2603` |
| `.lean-receipts/b1ae611c8e9c-comparator.json` (used here) | statement comparison | `b1ae611c8e9c` | 2026-10-29 | — | `845c54f1d1116ea7fd4db4b6152acda9c0e653d3f7614ea72dcd53667286a225` |
| `.lean-receipts/b1ae611c8e9c-systemd-user-walsh-integral-v090-homedell-202610290958.service-e768d78e244449ffac44c113f6098b1c-h-f985343177f7.json` (used here) | build | `b1ae611c8e9c` | 2026-10-29 | — | `490ac1697a9fb5c6bac75c8f53dc269506de5a872297ebf1b3ac2c3d31bf6872` |
| `.lean-receipts/cca30eeee631-comparator.json` | statement comparison | `cca30eeee631` | 2026-10-28 | — | `1aa88a16c1aedf8d3b960bbe512e8c61380d1b3d0975d4b51d082f0c9d70ef23` |
| `.lean-receipts/cca30eeee631-official-native.json` | build | `cca30eeee631` | 2026-10-28 | — | `95d0e5e60beb906464b8f43a76187fd71ea5c2623007907f3589b4a5a1b8fb7d` |
| `.lean-receipts/cca30eeee631-systemd-user-walsh-integral-coverage-20261028.service-fe797aaa92ab4664bda66251adeeeaef-h-2db2e0fa6029.json` | build | `cca30eeee631` | 2026-10-28 | — | `95d0e5e60beb906464b8f43a76187fd71ea5c2623007907f3589b4a5a1b8fb7d` |
| `.lean-receipts/e0547e67d6a0-comparator.json` | statement comparison | `e0547e67d6a0` | 2026-10-28 | — | `4031195f515adf152c7da084bd82597454bf148e3f4e0161a3b5e407b711c024` |
| `.lean-receipts/e0547e67d6a0-official-native.json` | build | `e0547e67d6a0` | 2026-10-28 | — | `4c59e2907dfe13349040e3b4322b449a6978f10ee9df435ad1ecac7d1754d0f6` |

*(used here)*: the receipt the lean-pkg registry holds for this package, which the lines above read. SHA-256 is of the file as committed.

### Reproduce

- Lean toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (lake-manifest.json).

```bash
git clone https://github.com/chenle02/walsh-integral-lean
cd walsh-integral-lean
git checkout b1ae611c8e9c4b9baf8904f07d442b3c8f32194a   # the commit the build check binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration above reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the build check records); `sorryAx` never appears.

## Citation

Le Chen. *WalshIntegral*. Version 0.9.0.

See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

<!-- lean-pkg:page:end -->
