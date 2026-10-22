import WalshIntegral.Rio
import WalshIntegral.Integral
import WalshIntegral.GaussianStein

/-!
# The Gaussian slab step with the linear constant `p - 1`.

Let `X` be measurable for the past `F s`, let `C` be bounded `F s`-measurable cell coefficients and
let `D = ∑ⱼ Cⱼ Zⱼ`, where `Z` is independent of `(X, C)` and every fixed linear combination
`∑ⱼ cⱼ Zⱼ` is centred Gaussian with variance `q(c)`. Then

`‖X + D‖_p² ≤ ‖X‖_p² + (p - 1) ‖q(C)‖_{p/2}` for every real `p ≥ 2`.

Proof: with `φ(a) = E|X + aD|^p`, Gaussian integration by parts (Stein's identity) conditionally on
`(X, C)` gives `φ'(a) = a p (p - 1) E[q(C) |X + aD|^(p-2)]`; Hölder's inequality bounds this by
`a p (p - 1) ‖q(C)‖_{p/2} φ(a)^(1 - 2/p)`, and the first-order comparison
`Rio.eLpNorm_add_sq_le_of_deriv_le` integrates the bound over `a ∈ [0, 1]`.

The step is first stated with Stein's identity as an explicit hypothesis `SteinIdentity` (the
`_of_stein` forms), then instantiated with
`GaussianStein.integral_mul_eq_variance_mul_integral_deriv`.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace WalshIntegral.GaussianStep

open WalshIntegral.WhiteNoise WalshIntegral.Predictable WalshIntegral.Integral

/-- One-dimensional Gaussian integration by parts, in the exact form of the statement of
`GaussianStein.integral_mul_eq_variance_mul_integral_deriv`, packaged as a proposition. -/
def SteinIdentity : Prop :=
  ∀ (v : ℝ≥0) (g g' : ℝ → ℝ), (∀ y, HasDerivAt g (g' y) y) → Continuous g' →
    (∃ C : ℝ, ∃ n : ℕ, ∀ y, |g y| ≤ C * (1 + |y|) ^ n ∧ |g' y| ≤ C * (1 + |y|) ^ n) →
    ∫ y, y * g y ∂(gaussianReal 0 v) = (v : ℝ) * ∫ y, g' y ∂(gaussianReal 0 v)

/-- Stein's identity holds. -/
theorem steinIdentity : SteinIdentity := fun v _ _ hg hg' hpoly =>
  GaussianStein.integral_mul_eq_variance_mul_integral_deriv v hg hg' hpoly

private theorem abs_line_rpow_le {r : ℝ} {N : ℕ} (hr : 0 ≤ r) (hrN : r ≤ N) (x a y : ℝ) :
    |x + a * y| ^ r ≤ (|x| + |a| + 1) ^ r * (1 + |y|) ^ N := by
  have hy : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hM : 0 ≤ |x| + |a| + 1 := by positivity
  have hline : |x + a * y| ≤ (|x| + |a| + 1) * (1 + |y|) := by
    have h := abs_add_le x (a * y)
    rw [abs_mul] at h
    nlinarith [abs_nonneg x, abs_nonneg a, abs_nonneg y, mul_nonneg (abs_nonneg a) (abs_nonneg y)]
  calc
    |x + a * y| ^ r ≤ ((|x| + |a| + 1) * (1 + |y|)) ^ r :=
      Real.rpow_le_rpow (abs_nonneg _) hline hr
    _ = (|x| + |a| + 1) ^ r * (1 + |y|) ^ r := Real.mul_rpow hM (by linarith)
    _ ≤ (|x| + |a| + 1) ^ r * (1 + |y|) ^ (N : ℝ) := by
      gcongr
    _ = (|x| + |a| + 1) ^ r * (1 + |y|) ^ N := by rw [Real.rpow_natCast]

/-- The one-dimensional Gaussian step: for `ψ(u) = |u|^(p-2) u` and `Y ~ N(0, v)`,
`E[ψ(x + aY) Y] = a (p - 1) v E|x + aY|^(p-2)`. -/
theorem integral_weight_mul_gaussian_of_stein (hstein : SteinIdentity) {p : ℝ} (hp : 2 ≤ p)
    (v : ℝ≥0) (x a : ℝ) :
    ∫ y, |x + a * y| ^ (p - 2) * (x + a * y) * y ∂(gaussianReal 0 v) =
      a * (p - 1) * (v : ℝ) * ∫ y, |x + a * y| ^ (p - 2) ∂(gaussianReal 0 v) := by
  have hp2 : 0 ≤ p - 2 := by linarith
  have hd (y : ℝ) : HasDerivAt (fun y => |x + a * y| ^ (p - 2) * (x + a * y))
      ((p - 1) * |x + a * y| ^ (p - 2) * a) y := by
    have h := (Rio.hasDerivAt_weight_of_two_le hp (x + a * y)).comp y
      (((hasDerivAt_id y).const_mul a).const_add x)
    convert h using 1 <;> first | rfl | ring
  have hc : Continuous fun y => (p - 1) * |x + a * y| ^ (p - 2) * a := by
    have : Continuous fun y : ℝ => |x + a * y| ^ (p - 2) :=
      (continuous_const.add (continuous_const.mul continuous_id)).abs.rpow_const
        (fun _ => Or.inr hp2)
    exact (continuous_const.mul this).mul continuous_const
  have hpoly : ∃ C : ℝ, ∃ n : ℕ, ∀ y,
      |(fun y => |x + a * y| ^ (p - 2) * (x + a * y)) y| ≤ C * (1 + |y|) ^ n ∧
      |(fun y => (p - 1) * |x + a * y| ^ (p - 2) * a) y| ≤ C * (1 + |y|) ^ n := by
    set M := |x| + |a| + 1
    refine ⟨M ^ (p - 1) + (p - 1) * |a| * M ^ (p - 2), ⌈p⌉₊, fun y => ⟨?_, ?_⟩⟩
    · have h1 := abs_line_rpow_le (N := ⌈p⌉₊) (by linarith : (0 : ℝ) ≤ p - 1)
        ((sub_le_self p zero_le_one).trans (Nat.le_ceil p)) x a y
      have heq : |(fun y => |x + a * y| ^ (p - 2) * (x + a * y)) y| = |x + a * y| ^ (p - 1) := by
        simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 2 + 1 ≠ 0)]
        ring_nf
      rw [heq]
      have hpos : 0 ≤ (p - 1) * |a| * M ^ (p - 2) * (1 + |y|) ^ ⌈p⌉₊ :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (abs_nonneg _))
          (Real.rpow_nonneg (by positivity) _)) (by positivity)
      nlinarith
    · have h2 := abs_line_rpow_le (N := ⌈p⌉₊) hp2
        ((by linarith : p - 2 ≤ p).trans (Nat.le_ceil p)) x a y
      have heq : |(fun y => (p - 1) * |x + a * y| ^ (p - 2) * a) y| =
          (p - 1) * |a| * |x + a * y| ^ (p - 2) := by
        simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ p - 1)]
        ring
      rw [heq]
      have hM : 0 ≤ M ^ (p - 1) * (1 + |y|) ^ ⌈p⌉₊ := by positivity
      have hk : 0 ≤ (p - 1) * |a| := mul_nonneg (by linarith) (abs_nonneg _)
      have := mul_le_mul_of_nonneg_left h2 hk
      nlinarith
  have h := hstein v _ _ hd hc hpoly
  calc
    ∫ y, |x + a * y| ^ (p - 2) * (x + a * y) * y ∂(gaussianReal 0 v) =
        ∫ y, y * (|x + a * y| ^ (p - 2) * (x + a * y)) ∂(gaussianReal 0 v) := by
      congr 1
      ext y
      ring
    _ = (v : ℝ) * ∫ y, (p - 1) * |x + a * y| ^ (p - 2) * a ∂(gaussianReal 0 v) := h
    _ = a * (p - 1) * (v : ℝ) * ∫ y, |x + a * y| ^ (p - 2) ∂(gaussianReal 0 v) := by
      rw [integral_mul_const, integral_const_mul]
      ring

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Fubini through independence: if `U` and `Z` are independent, the expectation of
`H(U, Z)` is the iterated integral over the laws of `U` and `Z`. -/
theorem integral_indep_eq_integral_integral {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {U : Ω → α} {Z : Ω → β} (hU : Measurable U) (hZ : Measurable Z)
    (hind : IndepFun U Z P) {H : α → β → ℝ} (hH : Measurable (Function.uncurry H))
    (hi : Integrable (fun ω => H (U ω) (Z ω)) P) :
    ∫ ω, H (U ω) (Z ω) ∂P = ∫ u, ∫ z, H u z ∂(P.map Z) ∂(P.map U) := by
  have hUZ : Measurable (fun ω => (U ω, Z ω)) := hU.prodMk hZ
  have hmap : P.map (fun ω => (U ω, Z ω)) = (P.map U).prod (P.map Z) :=
    hind.map_prod_eq_prod_map_map hU.aemeasurable hZ.aemeasurable
  have hint : Integrable (Function.uncurry H) ((P.map U).prod (P.map Z)) := by
    rw [← hmap]
    exact (integrable_map_measure hH.aestronglyMeasurable hUZ.aemeasurable).mpr hi
  calc
    ∫ ω, H (U ω) (Z ω) ∂P = ∫ w, Function.uncurry H w ∂(P.map (fun ω => (U ω, Z ω))) :=
      (integral_map hUZ.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ w, Function.uncurry H w ∂((P.map U).prod (P.map Z)) := by rw [hmap]
    _ = _ := integral_prod _ hint

omit [IsProbabilityMeasure P] in
/-- Integrating a function of a fixed linear combination `∑ⱼ cⱼ zⱼ` against the law of `Z`
is integrating against the Gaussian law of that combination. -/
theorem integral_map_linear_combination {n : ℕ} {Z : Ω → Fin n → ℝ} (hZ : Measurable Z)
    {q : (Fin n → ℝ) → ℝ≥0}
    (hlaw : ∀ c : Fin n → ℝ, P.map (fun ω => ∑ j, c j * Z ω j) = gaussianReal 0 (q c))
    (c : Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ z, f (∑ j, c j * z j) ∂(P.map Z) = ∫ y, f y ∂(gaussianReal 0 (q c)) := by
  have hm : Measurable (fun z : Fin n → ℝ => ∑ j, c j * z j) := by fun_prop
  calc
    ∫ z, f (∑ j, c j * z j) ∂(P.map Z) =
        ∫ y, f y ∂((P.map Z).map (fun z : Fin n → ℝ => ∑ j, c j * z j)) :=
      (integral_map hm.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [Measure.map_map hm hZ, ← hlaw c]
      rfl

/-- The conditional Stein step on `Ω`: with `D = ∑ⱼ Cⱼ Zⱼ`, `Z` independent of `(X, C)` and
`∑ⱼ cⱼ Zⱼ ~ N(0, q(c))`, one has `E[ψ(X + aD) D] = a (p - 1) E[q(C) |X + aD|^(p-2)]`. -/
theorem integral_weight_mul_eq_of_stein (hstein : SteinIdentity) {n : ℕ} {p : ℝ} (hp : 2 ≤ p)
    {X : Ω → ℝ} {C Z : Ω → Fin n → ℝ} {q : (Fin n → ℝ) → ℝ≥0}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hq : Measurable q)
    (hind : IndepFun (fun ω => (X ω, C ω)) Z P)
    (hlaw : ∀ c : Fin n → ℝ, P.map (fun ω => ∑ j, c j * Z ω j) = gaussianReal 0 (q c))
    (a : ℝ)
    (hi1 : Integrable (fun ω => |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) *
      (X ω + a * ∑ j, C ω j * Z ω j) * ∑ j, C ω j * Z ω j) P)
    (hi2 : Integrable (fun ω => (q (C ω) : ℝ) * |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2)) P) :
    ∫ ω, |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) *
        (X ω + a * ∑ j, C ω j * Z ω j) * ∑ j, C ω j * Z ω j ∂P =
      a * (p - 1) * ∫ ω, (q (C ω) : ℝ) * |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) ∂P := by
  have hU : Measurable (fun ω => (X ω, C ω)) := hX.prodMk hC
  let H1 : ℝ × (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun u z =>
    |u.1 + a * ∑ j, u.2 j * z j| ^ (p - 2) * (u.1 + a * ∑ j, u.2 j * z j) * ∑ j, u.2 j * z j
  let H2 : ℝ × (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun u z =>
    (q u.2 : ℝ) * |u.1 + a * ∑ j, u.2 j * z j| ^ (p - 2)
  have hH1 : Measurable (Function.uncurry H1) := by
    simp only [H1, Function.uncurry_def]
    fun_prop
  have hH2 : Measurable (Function.uncurry H2) := by
    simp only [H2, Function.uncurry_def]
    fun_prop
  have hinner (u : ℝ × (Fin n → ℝ)) :
      ∫ z, H1 u z ∂(P.map Z) = a * (p - 1) * ∫ z, H2 u z ∂(P.map Z) := by
    have e1 : ∫ z, H1 u z ∂(P.map Z) =
        ∫ y, |u.1 + a * y| ^ (p - 2) * (u.1 + a * y) * y ∂(gaussianReal 0 (q u.2)) :=
      integral_map_linear_combination hZ hlaw u.2
        (f := fun y => |u.1 + a * y| ^ (p - 2) * (u.1 + a * y) * y) (by fun_prop)
    have e2 : ∫ z, H2 u z ∂(P.map Z) =
        (q u.2 : ℝ) * ∫ y, |u.1 + a * y| ^ (p - 2) ∂(gaussianReal 0 (q u.2)) := by
      rw [← integral_map_linear_combination hZ hlaw u.2
        (f := fun y => |u.1 + a * y| ^ (p - 2)) (by fun_prop), ← integral_const_mul]
    rw [e1, e2, integral_weight_mul_gaussian_of_stein hstein hp]
    ring
  calc
    _ = ∫ u, ∫ z, H1 u z ∂(P.map Z) ∂(P.map (fun ω => (X ω, C ω))) :=
      integral_indep_eq_integral_integral hU hZ hind hH1 hi1
    _ = ∫ u, a * (p - 1) * ∫ z, H2 u z ∂(P.map Z) ∂(P.map (fun ω => (X ω, C ω))) := by
      congr 1
      ext u
      exact hinner u
    _ = a * (p - 1) * ∫ u, ∫ z, H2 u z ∂(P.map Z) ∂(P.map (fun ω => (X ω, C ω))) :=
      integral_const_mul _ _
    _ = _ := by
      rw [← integral_indep_eq_integral_integral hU hZ hind hH2 hi2]

/-- The abstract Gaussian step with the linear constant `p - 1`, for every real `p ≥ 2`:
`‖X + ∑ⱼ Cⱼ Zⱼ‖_p² ≤ ‖X‖_p² + (p - 1) ‖q(C)‖_{p/2}` when `Z` is independent of `(X, C)`, every
fixed combination `∑ⱼ cⱼ Zⱼ` is `N(0, q(c))`, `C` is bounded and `q ∘ C` is bounded. -/
theorem eLpNorm_add_gaussian_sq_le_of_stein (hstein : SteinIdentity) {n : ℕ} {p : ℝ}
    (hp : 2 ≤ p) {X : Ω → ℝ} {C Z : Ω → Fin n → ℝ} {q : (Fin n → ℝ) → ℝ≥0}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hq : Measurable q)
    (hCb : ∃ M : ℝ, ∀ ω j, |C ω j| ≤ M) (hqb : ∃ M : ℝ, ∀ ω, (q (C ω) : ℝ) ≤ M)
    (hXLp : MemLp X (ENNReal.ofReal p) P)
    (hind : IndepFun (fun ω => (X ω, C ω)) Z P)
    (hlaw : ∀ c : Fin n → ℝ, P.map (fun ω => ∑ j, c j * Z ω j) = gaussianReal 0 (q c)) :
    eLpNorm (fun ω => X ω + ∑ j, C ω j * Z ω j) (ENNReal.ofReal p) P ^ 2 ≤
      eLpNorm X (ENNReal.ofReal p) P ^ 2 +
        ENNReal.ofReal (p - 1) * eLpNorm (fun ω => (q (C ω) : ℝ)) (ENNReal.ofReal (p / 2)) P := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  obtain ⟨MC, hMC⟩ := hCb
  obtain ⟨Mq, hMq⟩ := hqb
  -- the Gaussian increment is in `L^p`
  have hZLp (j : Fin n) : MemLp (fun ω => Z ω j) (ENNReal.ofReal p) P := by
    have hl := hlaw (Pi.single j 1)
    have hfun : (fun ω => ∑ i, (Pi.single j 1 : Fin n → ℝ) i * Z ω i) = fun ω => Z ω j := by
      ext ω
      simp [Pi.single_apply]
    rw [hfun] at hl
    have hlaw' : HasLaw (fun ω => Z ω j) (gaussianReal 0 (q (Pi.single j 1))) P :=
      ⟨(by fun_prop : Measurable fun ω => Z ω j).aemeasurable, hl⟩
    exact hlaw'.memLp (memLp_id_gaussianReal' (ENNReal.ofReal p) ENNReal.ofReal_ne_top)
  have hCLp (j : Fin n) : MemLp (fun ω => C ω j) ∞ P :=
    memLp_top_of_bound (by fun_prop : Measurable fun ω => C ω j).aestronglyMeasurable MC
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hMC ω j)
  have hDLp : MemLp (fun ω => ∑ j, C ω j * Z ω j) (ENNReal.ofReal p) P := by
    have hprod (j : Fin n) : MemLp (fun ω => C ω j * Z ω j) (ENNReal.ofReal p) P :=
      (hCLp j).mul (hZLp j)
    have h := memLp_finsetSum' Finset.univ (fun j _ => hprod j)
    convert h using 1
    ext ω
    simp
  -- the conditional variance and its square root
  have hVm : Measurable (fun ω => (q (C ω) : ℝ)) := by fun_prop
  have hV0 (ω : Ω) : 0 ≤ (q (C ω) : ℝ) := NNReal.coe_nonneg _
  have hSm : Measurable (fun ω => Real.sqrt (q (C ω) : ℝ)) := by fun_prop
  have hSLp : MemLp (fun ω => Real.sqrt (q (C ω) : ℝ)) (ENNReal.ofReal p) P :=
    MemLp.of_bound hSm.aestronglyMeasurable (Real.sqrt Mq) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hMq ω))
  have hS2 (ω : Ω) : Real.sqrt (q (C ω) : ℝ) ^ 2 = (q (C ω) : ℝ) := Real.sq_sqrt (hV0 ω)
  set B : ℝ := (∫ ω, |Real.sqrt (q (C ω) : ℝ)| ^ p ∂P) ^ (2 / p) with hBdef
  have hB : 0 ≤ B :=
    Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _) _
  -- the derivative bound
  have hderiv : ∀ a ∈ Icc (0 : ℝ) 1,
      (∫ ω, p * (|X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) *
          (X ω + a * ∑ j, C ω j * Z ω j) * ∑ j, C ω j * Z ω j) ∂P) ≤
        a * (p * (p - 1) * B) *
          (∫ ω, |X ω + a * ∑ j, C ω j * Z ω j| ^ p ∂P) ^ (1 - 2 / p) := by
    intro a ha
    have hWLp : MemLp (fun ω => X ω + a * ∑ j, C ω j * Z ω j) (ENNReal.ofReal p) P :=
      hXLp.add (hDLp.const_mul a)
    have hWp : Integrable (fun ω => |X ω + a * ∑ j, C ω j * Z ω j| ^ p) P := by
      simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using
        hWLp.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
    have hWm : Measurable (fun ω => X ω + a * ∑ j, C ω j * Z ω j) := by fun_prop
    have hWq : Integrable (fun ω => |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2)) P := by
      refine ((integrable_const (1 : ℝ)).add hWp).mono' (by fun_prop)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      have hnn : 0 ≤ |X ω + a * ∑ j, C ω j * Z ω j| ^ p := Real.rpow_nonneg (abs_nonneg _) _
      rcases le_total |X ω + a * ∑ j, C ω j * Z ω j| 1 with h | h
      · have := Real.rpow_le_one (abs_nonneg _) h hp2
        simp only [Pi.add_apply]
        linarith
      · have := Real.rpow_le_rpow_of_exponent_le h (by linarith : p - 2 ≤ p)
        simp only [Pi.add_apply]
        linarith
    have hi1 := Rio.weight_integrable_mul hp hWLp hDLp
    have hi2 : Integrable (fun ω => (q (C ω) : ℝ) *
        |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2)) P :=
      hWq.bdd_mul hVm.aestronglyMeasurable (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hV0 ω)]
        exact hMq ω)
    have hid := integral_weight_mul_eq_of_stein hstein hp hX hC hZ hq hind hlaw a hi1 hi2
    -- Hölder
    have hhold : (∫ ω, (q (C ω) : ℝ) * |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) ∂P) ≤
        (∫ ω, |X ω + a * ∑ j, C ω j * Z ω j| ^ p ∂P) ^ (1 - 2 / p) * B := by
      rcases eq_or_lt_of_le hp with hpe | hpl
      · subst p
        have hl : (∫ ω, (q (C ω) : ℝ) * |X ω + a * ∑ j, C ω j * Z ω j| ^ ((2 : ℝ) - 2) ∂P) =
            ∫ ω, |Real.sqrt (q (C ω) : ℝ)| ^ (2 : ℝ) ∂P := by
          congr 1
          ext ω
          rw [sub_self, Real.rpow_zero, mul_one, Real.rpow_two, sq_abs, hS2]
        rw [hl, hBdef]
        norm_num
      · have h := Rio.curvature_integral_le hpl hWLp hSLp
        have hl : (∫ ω, (q (C ω) : ℝ) * |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) ∂P) =
            ∫ ω, |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) *
              Real.sqrt (q (C ω) : ℝ) ^ 2 ∂P := by
          congr 1
          ext ω
          rw [hS2, mul_comm]
        rw [hl, show 1 - 2 / p = (p - 2) / p by field_simp]
        exact h
    have ha0 : 0 ≤ a * (p - 1) * p := mul_nonneg (mul_nonneg ha.1 hp1) hp0.le
    calc
      (∫ ω, p * (|X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) *
          (X ω + a * ∑ j, C ω j * Z ω j) * ∑ j, C ω j * Z ω j) ∂P) =
          p * (a * (p - 1) *
            ∫ ω, (q (C ω) : ℝ) * |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) ∂P) := by
        rw [integral_const_mul, hid]
      _ = a * (p - 1) * p *
            ∫ ω, (q (C ω) : ℝ) * |X ω + a * ∑ j, C ω j * Z ω j| ^ (p - 2) ∂P := by ring
      _ ≤ a * (p - 1) * p *
            ((∫ ω, |X ω + a * ∑ j, C ω j * Z ω j| ^ p ∂P) ^ (1 - 2 / p) * B) :=
        mul_le_mul_of_nonneg_left hhold ha0
      _ = _ := by ring
  have hmain := Rio.eLpNorm_add_sq_le_of_deriv_le hp hXLp hDLp hB hderiv
  -- identify `(p - 1) B` with `(p - 1) ‖q(C)‖_{p/2}`
  have hexp : ENNReal.ofReal (p / 2) * ENNReal.ofReal 2 = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hVS : eLpNorm (fun ω => (q (C ω) : ℝ)) (ENNReal.ofReal (p / 2)) P =
      ENNReal.ofReal B := by
    have h := eLpNorm_norm_rpow (p := ENNReal.ofReal (p / 2))
      (fun ω => Real.sqrt (q (C ω) : ℝ)) hSm.aestronglyMeasurable
      (by norm_num : (0 : ℝ) < 2) (μ := P)
    have hfun : (fun ω => ‖Real.sqrt (q (C ω) : ℝ)‖ ^ (2 : ℝ)) = fun ω => (q (C ω) : ℝ) := by
      ext ω
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs, hS2]
    rw [hfun, hexp, ENNReal.rpow_two, Rio.eLpNorm_sq_eq_moment hp0 hSLp] at h
    exact h
  rw [hVS, ← ENNReal.ofReal_mul hp1]
  exact hmain

/-- The abstract Gaussian step with Stein's identity discharged. -/
theorem eLpNorm_add_gaussian_sq_le {n : ℕ} {p : ℝ}
    (hp : 2 ≤ p) {X : Ω → ℝ} {C Z : Ω → Fin n → ℝ} {q : (Fin n → ℝ) → ℝ≥0}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hq : Measurable q)
    (hCb : ∃ M : ℝ, ∀ ω j, |C ω j| ≤ M) (hqb : ∃ M : ℝ, ∀ ω, (q (C ω) : ℝ) ≤ M)
    (hXLp : MemLp X (ENNReal.ofReal p) P)
    (hind : IndepFun (fun ω => (X ω, C ω)) Z P)
    (hlaw : ∀ c : Fin n → ℝ, P.map (fun ω => ∑ j, c j * Z ω j) = gaussianReal 0 (q c)) :
    eLpNorm (fun ω => X ω + ∑ j, C ω j * Z ω j) (ENNReal.ofReal p) P ^ 2 ≤
      eLpNorm X (ENNReal.ofReal p) P ^ 2 +
        ENNReal.ofReal (p - 1) * eLpNorm (fun ω => (q (C ω) : ℝ)) (ENNReal.ofReal (p / 2)) P :=
  eLpNorm_add_gaussian_sq_le_of_stein steinIdentity hp hX hC hZ hq hCb hqb hXLp hind hlaw

end Abstract

section Slab

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}

/-- The squared norm of a combination of disjoint rectangles on a common slab `(s, t]`. -/
theorem slab_gram_eq {n : ℕ} (e : Fin n → Elementary F) (s t : ℝ≥0) (hst : s < t)
    (hdisj : Pairwise (fun i j => Disjoint (e i).A (e j).A)) (a : Fin n → ℝ) :
    ‖∑ j, a j • rectangle s t (e j).A (e j).measurableSet_A (e j).volume_A_ne_top‖ ^ 2 =
      ((t : ℝ) - (s : ℝ)) * ∑ j, (volume (e j).A).toReal * a j ^ 2 := by
  classical
  have hfin (j : Fin n) : timeSpaceVolume (Ioc (s : ℝ) (t : ℝ) ×ˢ (e j).A) ≠ ∞ := by
    rw [timeSpaceVolume, Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (ne_of_lt ((Measure.restrict_apply_le _ _).trans_lt (by simp))) (e j).volume_A_ne_top
  have hinner (i j : Fin n) : inner ℝ
      (rectangle s t (e i).A (e i).measurableSet_A (e i).volume_A_ne_top)
      (rectangle s t (e j).A (e j).measurableSet_A (e j).volume_A_ne_top) =
      if i = j then ((t : ℝ) - (s : ℝ)) * (volume (e i).A).toReal else 0 := by
    unfold rectangle
    rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _ (hfin i) (hfin j)]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, inter_self, Measure.real, timeSpaceVolume, Measure.prod_prod,
        ENNReal.toReal_mul, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioi,
        max_eq_left s.coe_nonneg, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst.le))]
    · simp [hij, prod_inter_prod, Disjoint.inter_eq (hdisj hij), Measure.real]
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hinner,
    conj_trivial, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Gaussian slab step with the linear constant `p - 1` (Stein's identity as a hypothesis).
For a past-measurable `X ∈ L^p` and a slab sum on `(s, t]` with disjoint cells,
`‖X + ∑ⱼ ∫ eⱼ dW‖_p² ≤ ‖X‖_p² + (p - 1) ‖V‖_{p/2}` for every real `p ≥ 2`, where
`V = (t - s) ∑ⱼ |Aⱼ| coeffⱼ²` is the slab variance (`MomentBound.slabVariance s t e`, written out
here because `MomentBound` imports this module). -/
theorem eLpNorm_add_gaussian_slab_sq_le_of_stein (hstein : SteinIdentity)
    (hW : IsWhiteNoise P F W) {p : ℝ} (hp : 2 ≤ p)
    {n : ℕ} (e : Fin n → Elementary F) (s t : ℝ≥0) (hst : s < t)
    (hs : ∀ j, (e j).s = s) (ht : ∀ j, (e j).t = t)
    (hdisj : Pairwise (fun i j => Disjoint (e i).A (e j).A))
    {X : Ω → ℝ} (hX : StronglyMeasurable[F s] X) (hXLp : MemLp X (ENNReal.ofReal p) P) :
    eLpNorm (fun ω => X ω + ∑ j, elementaryIntegral W (e j) ω) (ENNReal.ofReal p) P ^ 2 ≤
      eLpNorm X (ENNReal.ofReal p) P ^ 2 +
        ENNReal.ofReal (p - 1) * eLpNorm (fun ω => ((t : ℝ) - (s : ℝ)) *
          ∑ j, (volume (e j).A).toReal * (e j).coeff ω ^ 2) (ENNReal.ofReal (p / 2)) P := by
  classical
  let r (j : Fin n) := rectangle s t (e j).A (e j).measurableSet_A (e j).volume_A_ne_top
  let C : Ω → Fin n → ℝ := fun ω j => (e j).coeff ω
  let Z : Ω → Fin n → ℝ := fun ω j => W (r j) ω
  let q : (Fin n → ℝ) → ℝ≥0 := fun c => ‖∑ j, c j • r j‖₊ ^ 2
  have hCs : Measurable[F s] C := by
    apply @Measurable.of_eval Ω (Fin n) (fun _ => ℝ) (F s) _ C
    intro j
    have hj := (e j).measurable_coeff
    rw [hs j] at hj
    exact hj
  have hC : Measurable C := hCs.mono (F.le s) le_rfl
  have hXs : Measurable[F s] X := hX.measurable
  have hXm : Measurable X := hXs.mono (F.le s) le_rfl
  have hZ : Measurable Z :=
    Measurable.of_eval (fun j => (Lp.stronglyMeasurable (W (r j))).measurable)
  have hqc : Continuous q := by fun_prop
  have hUs : Measurable[F s] (fun ω => (X ω, C ω)) := hXs.prodMk hCs
  have hind : IndepFun (fun ω => (X ω, C ω)) Z P :=
    (indep_of_indep_of_le (hW.future_fin_indep s r
      (fun j => rectangle_supportedAfter s t _ _ _)) le_rfl hUs.comap_le).symm
  have hgram (c : Fin n → ℝ) :
      (q c : ℝ) = ((t : ℝ) - (s : ℝ)) * ∑ j, (volume (e j).A).toReal * c j ^ 2 := by
    simpa only [q, NNReal.coe_pow, coe_nnnorm, r] using slab_gram_eq e s t hst hdisj c
  have hV : (fun ω => (q (C ω) : ℝ)) = fun ω => ((t : ℝ) - (s : ℝ)) *
      ∑ j, (volume (e j).A).toReal * (e j).coeff ω ^ 2 := by
    funext ω
    rw [hgram]
  choose M hM using fun j => (e j).bounded_coeff
  have hMC (ω : Ω) (j : Fin n) : |C ω j| ≤ ∑ i, |M i| := by
    calc
      |C ω j| ≤ M j := by simpa only [Real.norm_eq_abs] using hM j ω
      _ ≤ |M j| := le_abs_self _
      _ ≤ ∑ i, |M i| :=
        Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hdt : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr (by exact_mod_cast hst.le)
  have hqb (ω : Ω) : (q (C ω) : ℝ) ≤
      ((t : ℝ) - (s : ℝ)) * ∑ j, (volume (e j).A).toReal * (∑ i, |M i|) ^ 2 := by
    rw [hgram]
    apply mul_le_mul_of_nonneg_left _ hdt
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    rw [← sq_abs (C ω j)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hMC ω j) 2
  have hlaw (c : Fin n → ℝ) :
      P.map (fun ω => ∑ j, c j * Z ω j) = gaussianReal 0 (q c) :=
    hW.linear_combination_law r c
  have hmain := eLpNorm_add_gaussian_sq_le_of_stein hstein hp hXm hC hZ hqc.measurable
    ⟨_, hMC⟩ ⟨_, hqb⟩ hXLp hind hlaw
  have hae : (fun ω => X ω + ∑ j, elementaryIntegral W (e j) ω) =ᵐ[P]
      (fun ω => X ω + ∑ j, C ω j * Z ω j) := by
    filter_upwards [ae_all_iff.mpr (fun j => elementaryIntegral_ae W (e j))] with ω hω
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simpa only [C, Z, r, hs j, ht j] using hω j
  rw [eLpNorm_congr_ae hae, ← hV]
  exact hmain

/-- **The Gaussian slab step** with the linear constant `p - 1`, for every real `p ≥ 2`:
`‖X + ∑ⱼ ∫ eⱼ dW‖_p² ≤ ‖X‖_p² + (p - 1) ‖V‖_{p/2}` for `X` measurable for the past `F s`, with
`V = (t - s) ∑ⱼ |Aⱼ| coeffⱼ²` (`MomentBound.slabVariance s t e`). Stein's identity is supplied
by `GaussianStein`. -/
theorem eLpNorm_add_gaussian_slab_sq_le (hW : IsWhiteNoise P F W) {p : ℝ} (hp : 2 ≤ p)
    {n : ℕ} (e : Fin n → Elementary F) (s t : ℝ≥0) (hst : s < t)
    (hs : ∀ j, (e j).s = s) (ht : ∀ j, (e j).t = t)
    (hdisj : Pairwise (fun i j => Disjoint (e i).A (e j).A))
    {X : Ω → ℝ} (hX : StronglyMeasurable[F s] X) (hXLp : MemLp X (ENNReal.ofReal p) P) :
    eLpNorm (fun ω => X ω + ∑ j, elementaryIntegral W (e j) ω) (ENNReal.ofReal p) P ^ 2 ≤
      eLpNorm X (ENNReal.ofReal p) P ^ 2 +
        ENNReal.ofReal (p - 1) * eLpNorm (fun ω => ((t : ℝ) - (s : ℝ)) *
          ∑ j, (volume (e j).A).toReal * (e j).coeff ω ^ 2) (ENNReal.ofReal (p / 2)) P :=
  eLpNorm_add_gaussian_slab_sq_le_of_stein steinIdentity hW hp e s t hst hs ht hdisj hX hXLp

end Slab

end WalshIntegral.GaussianStep
