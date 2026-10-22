import Mathlib

/-!
# Rio’s real-p martingale-difference moment inequality.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace WalshIntegral.Rio

private theorem integral_mul_eq_zero_of_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X Y : Ω → ℝ} (hX : StronglyMeasurable[m] X)
    (hXY : Integrable (X * Y) P) (hY : Integrable Y P)
    (hcentered : P[Y | m] =ᵐ[P] (0 : Ω → ℝ)) :
    ∫ ω, X ω * Y ω ∂P = 0 := by
  have h := condExp_mul_of_stronglyMeasurable_left hX hXY hY
  calc
    ∫ ω, X ω * Y ω ∂P = ∫ ω, P[X * Y | m] ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, (0 : ℝ) ∂P := by
      apply integral_congr_ae
      filter_upwards [h, hcentered] with ω hω hzero
      simp only [hω, Pi.mul_apply, hzero, Pi.zero_apply, mul_zero]
    _ = 0 := integral_zero _ _

private theorem eLpNorm_two_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) :
    eLpNorm X 2 P ^ 2 = ENNReal.ofReal (∫ ω, X ω ^ 2 ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
    (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω))]
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
    (by norm_num) hX.aestronglyMeasurable
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
    ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] using h

private theorem eLpNorm_add_two_sq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X Y : Ω → ℝ} (hX : StronglyMeasurable[m] X)
    (hXLp : MemLp X 2 P) (hYLp : MemLp Y 2 P)
    (hcentered : P[Y | m] =ᵐ[P] (0 : Ω → ℝ)) :
    eLpNorm (X + Y) 2 P ^ 2 = eLpNorm X 2 P ^ 2 + eLpNorm Y 2 P ^ 2 := by
  let : MeasurableSpace Ω := mΩ
  have hXY := hXLp.integrable_mul hYLp
  have hz := integral_mul_eq_zero_of_condExp P hm hX hXY
    (hYLp.integrable (by norm_num)) hcentered
  have hi : (∫ ω, (X ω + Y ω) ^ 2 ∂P) =
      (∫ ω, X ω ^ 2 ∂P) + (∫ ω, Y ω ^ 2 ∂P) := by
    simp_rw [add_sq, mul_assoc]
    have hadd := integral_add (μ := P) (hXLp.integrable_sq.add (hXY.const_mul 2))
      hYLp.integrable_sq
    have hadd' := integral_add (μ := P) hXLp.integrable_sq (hXY.const_mul 2)
    simp only [Pi.add_apply, Pi.mul_apply] at hadd hadd'
    rw [hadd, hadd']
    simp only [integral_const_mul, hz, mul_zero, add_zero]
  rw [eLpNorm_two_sq_eq_integral (hXLp.add hYLp),
    eLpNorm_two_sq_eq_integral hXLp, eLpNorm_two_sq_eq_integral hYLp]
  change ENNReal.ofReal (∫ ω, (X ω + Y ω) ^ 2 ∂P) = _
  rw [hi, ENNReal.ofReal_add (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)]

private theorem eLpNorm_sum_sq_le_of_step {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    {p : ℝ} (d : ℕ → Ω → ℝ)
    (hadapted : ∀ k, StronglyMeasurable[ℱ (k + 1)] (d k))
    (hLp : ∀ k, MemLp (d k) (ENNReal.ofReal p) P)
    (hcentered : ∀ k, P[d k | ℱ k] =ᵐ[P] (0 : Ω → ℝ))
    (hstep : ∀ (m : MeasurableSpace Ω), m ≤ mΩ → ∀ (X Y : Ω → ℝ),
      StronglyMeasurable[m] X → MemLp X (ENNReal.ofReal p) P →
      MemLp Y (ENNReal.ofReal p) P → P[Y | m] =ᵐ[P] (0 : Ω → ℝ) →
      eLpNorm (X + Y) (ENNReal.ofReal p) P ^ 2 ≤
        eLpNorm X (ENNReal.ofReal p) P ^ 2 +
          ENNReal.ofReal (p - 1) * eLpNorm Y (ENNReal.ofReal p) P ^ 2) (n : ℕ) :
    eLpNorm (fun ω => ∑ k ∈ Finset.range n, d k ω) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (p - 1) *
        ∑ k ∈ Finset.range n, eLpNorm (d k) (ENNReal.ofReal p) P ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hSm : StronglyMeasurable[ℱ n] (fun ω => ∑ k ∈ Finset.range n, d k ω) := by
      convert (Finset.range n).stronglyMeasurable_sum
        (fun k hk => (hadapted k).mono (ℱ.mono (by simpa using Finset.mem_range.mp hk))) using 1
      ext ω
      simp
    have hSLp := memLp_finsetSum (Finset.range n) (fun k _ => hLp k)
    have h := hstep (ℱ n) (ℱ.le n) _ _ hSm hSLp (hLp n) (hcentered n)
    simp only [Finset.sum_range_succ]
    exact h.trans (by simpa only [mul_add] using (add_le_add ih le_rfl))


private theorem weight_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p : ℝ} (hp : 2 ≤ p) {X : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) :
    MemLp (fun ω => |X ω| ^ (p - 2) * X ω) (ENNReal.ofReal (p / (p - 1))) P := by
  have hp1 : 0 < p - 1 := by linarith
  have hpow := hX.norm_rpow_div (ENNReal.ofReal (p - 1))
  rw [← ENNReal.ofReal_div_of_pos hp1] at hpow
  simp only [ENNReal.toReal_ofReal hp1.le, Real.norm_eq_abs] at hpow
  apply hpow.mono
  · exact ((hX.aestronglyMeasurable.norm.aemeasurable.pow_const _).mul
      hX.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ω
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 2 + 1 ≠ 0)]
    rw [show p - 2 + 1 = p - 1 by ring]

/-- Hölder integrability of the weighted product `(|X|^(p-2) X) Y` for `X, Y ∈ L^p`, `2 ≤ p`. -/
theorem weight_integrable_mul {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p : ℝ} (hp : 2 ≤ p) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal p) P) :
    Integrable (fun ω => (|X ω| ^ (p - 2) * X ω) * Y ω) P := by
  have hp1 : 1 < p := by linarith
  have hconj : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have := hconj.symm.ennrealOfReal
  exact (weight_memLp hp hX).integrable_mul hY

private theorem weighted_centering {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {p : ℝ} (hp : 2 ≤ p) {X Y : Ω → ℝ} (hX : StronglyMeasurable[m] X)
    (hXLp : MemLp X (ENNReal.ofReal p) P) (hYLp : MemLp Y (ENNReal.ofReal p) P)
    (hcentered : P[Y | m] =ᵐ[P] (0 : Ω → ℝ)) :
    ∫ ω, (|X ω| ^ (p - 2) * X ω) * Y ω ∂P = 0 := by
  let : MeasurableSpace Ω := mΩ
  have hXm : StronglyMeasurable[m] (fun ω => |X ω| ^ (p - 2) * X ω) :=
    by
      let : MeasurableSpace Ω := m
      exact ((hX.measurable.abs.pow_const _).mul hX.measurable).stronglyMeasurable
  have hXY := weight_integrable_mul hp hXLp hYLp
  have hY := hYLp.integrable (by rw [ENNReal.one_le_ofReal]; linarith)
  have h := condExp_mul_of_stronglyMeasurable_left hXm hXY hY
  calc
    ∫ ω, (|X ω| ^ (p - 2) * X ω) * Y ω ∂P =
        ∫ ω, P[(fun ω => |X ω| ^ (p - 2) * X ω) * Y | m] ω ∂P :=
      (integral_condExp hm).symm
    _ = ∫ ω, (0 : ℝ) ∂P := by
      apply integral_congr_ae
      filter_upwards [h, hcentered] with ω hω hzero
      simp only [hω, Pi.mul_apply, hzero, Pi.zero_apply, mul_zero]
    _ = 0 := integral_zero _ _

/-- Hölder bound for the curvature integral `∫ |X|^(p-2) Y²` when `2 < p`. -/
theorem curvature_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p : ℝ} (hp : 2 < p) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal p) P) :
    (∫ ω, |X ω| ^ (p - 2) * Y ω ^ 2 ∂P) ≤
      (∫ ω, |X ω| ^ p ∂P) ^ ((p - 2) / p) *
        (∫ ω, |Y ω| ^ p ∂P) ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hconj : (p / (p - 2)).HolderConjugate (p / 2) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · rw [one_lt_div hp2]
      linarith
    · field_simp
      ring
  have hXp := hX.norm_rpow_div (ENNReal.ofReal (p - 2))
  rw [← ENNReal.ofReal_div_of_pos hp2] at hXp
  simp only [ENNReal.toReal_ofReal hp2.le, Real.norm_eq_abs] at hXp
  have hYp := hY.norm_rpow_div (2 : ℝ≥0∞)
  have he : ENNReal.ofReal p / 2 = ENNReal.ofReal (p / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [he] at hYp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at hYp
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg (X ω)) (p - 2))
    (Eventually.of_forall fun ω => sq_nonneg (Y ω)) hXp hYp
  have hpowX (ω : Ω) : (|X ω| ^ (p - 2)) ^ (p / (p - 2)) = |X ω| ^ p := by
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  have hpowY (ω : Ω) : (Y ω ^ 2) ^ (p / 2) = |Y ω| ^ p := by
    rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  simpa only [hpowX, hpowY, one_div, inv_div] using h

/-- The derivative of the weight `u ↦ |u|^(p-2) u` is `(p-1)|u|^(p-2)` when `2 < p`. -/
theorem hasDerivAt_weight {p : ℝ} (hp : 2 < p) (x : ℝ) :
    HasDerivAt (fun u : ℝ => |u| ^ (p - 2) * u) ((p - 1) * |x| ^ (p - 2)) x := by
  by_cases hx : x = 0
  · subst x
    have hp2 : 0 < p - 2 := by linarith
    simp only [abs_zero, Real.zero_rpow hp2.ne', mul_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    have hc : ContinuousAt (fun u : ℝ => |u| ^ (p - 2)) 0 :=
      continuousAt_id.abs.rpow_const (Or.inr hp2.le)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simp only [abs_zero, Real.zero_rpow hp2.ne'] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := hu
    simp only [slope, vsub_eq_sub, sub_zero, smul_eq_mul, mul_zero]
    field_simp
  · have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
    have h := ((hasDerivAt_abs hx).rpow_const (p := p - 2)
      (Or.inl hxabs)).mul (hasDerivAt_id x)
    convert h using 1
    · ext u
      simp
    · rw [Real.rpow_sub_one hxabs]
      rcases lt_or_gt_of_ne hx with hx | hx
      · simp [hx, abs_of_neg hx]
        field_simp
        ring
      · simp [hx, abs_of_pos hx]
        field_simp
        ring

private theorem hasDerivAt_abs_rpow_line {p : ℝ} (hp : 2 < p) (x y a : ℝ) :
    HasDerivAt (fun t : ℝ => |x + t * y| ^ p)
      (p * (|x + a * y| ^ (p - 2) * (x + a * y) * y)) a := by
  have h := (hasDerivAt_abs_rpow (x + a * y) (by linarith : 1 < p)).comp a
    (((hasDerivAt_id a).mul_const y).const_add x)
  convert h using 1 <;> first | rfl | ring

/-- Pointwise second derivative along the line `t ↦ |x + t y|^p` when `2 < p`. -/
theorem hasDerivAt_abs_rpow_line_derivative {p : ℝ} (hp : 2 < p) (x y a : ℝ) :
    HasDerivAt (fun t : ℝ => p * (|x + t * y| ^ (p - 2) * (x + t * y) * y))
      (p * (p - 1) * (|x + a * y| ^ (p - 2) * y ^ 2)) a := by
  have h := (((hasDerivAt_weight hp (x + a * y)).comp a
    (((hasDerivAt_id a).mul_const y).const_add x)).mul_const y).const_mul p
  convert h using 1 <;> first | rfl | ring

private theorem rpow_mul_mul_le {p u v w B : ℝ} (hp : 2 < p)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (huB : u ≤ B) (hvB : v ≤ B) (hwB : w ≤ B) :
    u ^ (p - 2) * v * w ≤ B ^ p := by
  have hB : 0 ≤ B := hu.trans huB
  calc
    u ^ (p - 2) * v * w ≤ B ^ (p - 2) * B * B := by
      gcongr
    _ = B ^ p := by
      rw [mul_assoc, ← pow_two, ← Real.rpow_two,
        ← Real.rpow_add' hB (by linarith : p - 2 + 2 ≠ 0)]
      congr 1
      ring

/-- First and second derivatives of `t ↦ ∫ |X + t Y|^p` for `X, Y ∈ L^p` and `2 < p`. -/
theorem moment_derivatives {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p : ℝ} (hp : 2 < p) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal p) P) (a : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ ω, |X ω + t * Y ω| ^ p ∂P)
      (∫ ω, p * (|X ω + a * Y ω| ^ (p - 2) * (X ω + a * Y ω) * Y ω) ∂P) a ∧
    HasDerivAt (fun t : ℝ =>
      ∫ ω, p * (|X ω + t * Y ω| ^ (p - 2) * (X ω + t * Y ω) * Y ω) ∂P)
      (∫ ω, p * (p - 1) * (|X ω + a * Y ω| ^ (p - 2) * Y ω ^ 2) ∂P) a := by
  have hp0 : 0 < p := by linarith
  let B : Ω → ℝ := fun ω => |X ω| + (|a| + 1) * |Y ω|
  have hB (ω : Ω) : 0 ≤ B ω := by dsimp [B]; positivity
  have hBp : MemLp B (ENNReal.ofReal p) P :=
    hX.norm.add (hY.norm.const_mul (|a| + 1))
  have hBi : Integrable (fun ω => B ω ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs, abs_of_nonneg (hB _)] using
      hBp.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
  have hYB (ω : Ω) : |Y ω| ≤ B ω := by
    dsimp [B]
    nlinarith [abs_nonneg (X ω), abs_nonneg (Y ω), abs_nonneg a]
  have hZB (t : ℝ) (ht : t ∈ Metric.ball a 1) (ω : Ω) : |X ω + t * Y ω| ≤ B ω := by
    have hta : |t - a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
    have htB : |t| ≤ |a| + 1 := by
      have h := abs_add_le (t - a) a
      rw [sub_add_cancel] at h
      linarith
    calc
      |X ω + t * Y ω| ≤ |X ω| + |t| * |Y ω| := by simpa only [abs_mul] using abs_add_le (X ω) (t * Y ω)
      _ ≤ B ω := by dsimp [B]; gcongr
  have hmeas (t : ℝ) : AEStronglyMeasurable (fun ω => |X ω + t * Y ω| ^ p) P :=
    ((hX.aestronglyMeasurable.add (hY.aestronglyMeasurable.const_mul t)).norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hmeas' (t : ℝ) : AEStronglyMeasurable
      (fun ω => p * (|X ω + t * Y ω| ^ (p - 2) * (X ω + t * Y ω) * Y ω)) P := by
    have hz := hX.aestronglyMeasurable.add (hY.aestronglyMeasurable.const_mul t)
    exact ((((hz.norm.aemeasurable.pow_const _).mul hz.aemeasurable).mul
      hY.aestronglyMeasurable.aemeasurable).const_mul p).aestronglyMeasurable
  have hZa := hX.add (hY.const_mul a)
  have hint : Integrable (fun ω => |X ω + a * Y ω| ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs, Pi.add_apply] using
      hZa.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds a (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas) hint (hmeas' a)
    (Eventually.of_forall fun ω t ht => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hp0,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact mul_le_mul_of_nonneg_left (rpow_mul_mul_le hp (abs_nonneg _)
        (abs_nonneg _) (abs_nonneg _) (hZB t ht ω) (hZB t ht ω) (hYB ω)) hp0.le)
    (hBi.const_mul p)
    (Eventually.of_forall fun ω t _ => hasDerivAt_abs_rpow_line hp (X ω) (Y ω) t)
  refine ⟨hfirst.2, ?_⟩
  have hp1 : 0 < p - 1 := by linarith
  have hmsecond : AEStronglyMeasurable
      (fun ω => p * (p - 1) * (|X ω + a * Y ω| ^ (p - 2) * Y ω ^ 2)) P := by
    have hz := hX.aestronglyMeasurable.add (hY.aestronglyMeasurable.const_mul a)
    exact (((hz.norm.aemeasurable.pow_const _).mul
      (hY.aestronglyMeasurable.aemeasurable.pow_const 2)).const_mul (p * (p - 1))).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds a (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas') hfirst.1 hmsecond
    (Eventually.of_forall fun ω t ht => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hp0, abs_of_pos hp1,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), pow_two, ← mul_assoc]
      simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left
        (rpow_mul_mul_le hp (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
          (hZB t ht ω) (hYB ω) (hYB ω)) (mul_nonneg hp0.le hp1.le))
    (hBi.const_mul (p * (p - 1)))
    (Eventually.of_forall fun ω t _ =>
      hasDerivAt_abs_rpow_line_derivative hp (X ω) (Y ω) t)).2

private theorem quadratic_bound {f f' f'' : ℝ → ℝ} {K : ℝ}
    (hf : ∀ a, HasDerivAt f (f' a) a) (hf' : ∀ a, HasDerivAt f' (f'' a) a)
    (hzero : f' 0 = 0) (hbound : ∀ a, f'' a ≤ K) :
    f 1 ≤ f 0 + K / 2 := by
  have hm : Monotone (fun a => K * a - f' a) :=
    monotone_of_hasDerivAt_nonneg
      (fun a => ((hasDerivAt_id a).const_mul K).sub (hf' a))
      (fun a => by simpa using sub_nonneg.mpr (hbound a))
  have hfirst (a : ℝ) (ha : 0 ≤ a) : f' a ≤ K * a := by
    have h := hm ha
    simp only [mul_zero, hzero, sub_zero] at h
    linarith
  have hd (a : ℝ) : HasDerivAt (fun t => K / 2 * t ^ 2 - f t) (K * a - f' a) a := by
    convert (((hasDerivAt_id a).pow 2).const_mul (K / 2)).sub (hf a) using 1
    · ext t
      simp
    · simp only [id_eq]
      ring
  have hn : MonotoneOn (fun a => K / 2 * a ^ 2 - f a) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun a _ => (hd a).continuousAt.continuousWithinAt)
      (fun a _ => (hd a).hasDerivWithinAt)
    intro a ha
    exact sub_nonneg.mpr (hfirst a (interior_subset ha))
  have h := hn (by simp : (0 : ℝ) ∈ Ici 0) (by simp : (1 : ℝ) ∈ Ici 0) (by norm_num)
  norm_num at h
  linarith

private theorem regularized_power_bound {f f' f'' : ℝ → ℝ} {q C ε : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C) (hε : 0 < ε)
    (hf0 : ∀ a, 0 ≤ f a) (hf : ∀ a, HasDerivAt f (f' a) a)
    (hf' : ∀ a, HasDerivAt f' (f'' a) a) (hzero : f' 0 = 0)
    (hbound : ∀ a, f'' a ≤ C * (f a) ^ (1 - q)) :
    (f 1 + ε) ^ q ≤ (f 0 + ε) ^ q + q * C / 2 := by
  have hpos (a : ℝ) : 0 < f a + ε := by linarith [hf0 a]
  have hd (a : ℝ) : HasDerivAt (fun t => (f t + ε) ^ q)
      (q * (f a + ε) ^ (q - 1) * f' a) a := by
    convert ((hf a).add_const ε).rpow_const (p := q) (Or.inl (hpos a).ne') using 1
    ring
  have hdd (a : ℝ) : HasDerivAt (fun t => q * (f t + ε) ^ (q - 1) * f' t)
      (q * (q - 1) * (f a + ε) ^ (q - 2) * (f' a) ^ 2 +
        q * (f a + ε) ^ (q - 1) * f'' a) a := by
    have h := ((((hf a).add_const ε).rpow_const (p := q - 1)
      (Or.inl (hpos a).ne')).const_mul q).mul (hf' a)
    convert h using 1
    rw [show q - 1 - 1 = q - 2 by ring]
    ring
  have hcurv (a : ℝ) :
      q * (q - 1) * (f a + ε) ^ (q - 2) * (f' a) ^ 2 +
        q * (f a + ε) ^ (q - 1) * f'' a ≤ q * C := by
    have hneg : q * (q - 1) * (f a + ε) ^ (q - 2) * (f' a) ^ 2 ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      apply mul_nonpos_of_nonpos_of_nonneg _ (Real.rpow_nonneg (hpos a).le _)
      exact mul_nonpos_of_nonneg_of_nonpos hq0.le (by linarith)
    have hpow : (f a) ^ (1 - q) ≤ (f a + ε) ^ (1 - q) :=
      Real.rpow_le_rpow (hf0 a) (by linarith) (by linarith)
    have hprod : (f a + ε) ^ (q - 1) * (f a + ε) ^ (1 - q) = 1 := by
      rw [← Real.rpow_add (hpos a), show q - 1 + (1 - q) = 0 by ring, Real.rpow_zero]
    have hb := mul_le_mul_of_nonneg_left (hbound a)
      (mul_nonneg hq0.le (Real.rpow_nonneg (hpos a).le (q - 1)))
    have hp := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (mul_nonneg hq0.le hC) (Real.rpow_nonneg (hpos a).le (q - 1)))
    have he : q * C * (f a + ε) ^ (q - 1) * (f a + ε) ^ (1 - q) = q * C := by
      rw [mul_assoc, hprod, mul_one]
    nlinarith
  have h := quadratic_bound hd hdd (by simp [hzero]) hcurv
  exact h

private theorem power_bound {f f' f'' : ℝ → ℝ} {q C : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hf0 : ∀ a, 0 ≤ f a) (hf : ∀ a, HasDerivAt f (f' a) a)
    (hf' : ∀ a, HasDerivAt f' (f'' a) a) (hzero : f' 0 = 0)
    (hbound : ∀ a, f'' a ≤ C * (f a) ^ (1 - q)) :
    (f 1) ^ q ≤ (f 0) ^ q + q * C / 2 := by
  have ht (a : ℝ) : Tendsto (fun ε : ℝ => (f a + ε) ^ q) (𝓝[>] 0) (𝓝 ((f a) ^ q)) := by
    have hc : ContinuousAt (fun ε : ℝ => (f a + ε) ^ q) 0 :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inr hq0.le)
    simpa only [add_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  apply le_of_tendsto_of_tendsto (ht 1) ((ht 0).add_const (q * C / 2))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact regularized_power_bound hq0 hq1 hC hε hf0 hf hf' hzero hbound

/-- The squared `L^p` norm as the real moment `(∫ |X|^p)^(2/p)`, for `0 < p`. -/
theorem eLpNorm_sq_eq_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p : ℝ} (hp : 0 < p) {X : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) :
    eLpNorm X (ENNReal.ofReal p) P ^ 2 =
      ENNReal.ofReal ((∫ ω, |X ω| ^ p ∂P) ^ (2 / p)) := by
  rw [hX.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (integral_nonneg fun _ =>
    Real.rpow_nonneg (abs_nonneg _) _) _)]
  rw [← Real.rpow_two, ← Real.rpow_mul (integral_nonneg fun _ =>
    Real.rpow_nonneg (abs_nonneg _) _)]
  congr 2
  ring

private theorem eLpNorm_add_sq_le_of_two_lt {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {p : ℝ} (hp : 2 < p) {X Y : Ω → ℝ} (hX : StronglyMeasurable[m] X)
    (hXLp : MemLp X (ENNReal.ofReal p) P) (hYLp : MemLp Y (ENNReal.ofReal p) P)
    (hcentered : P[Y | m] =ᵐ[P] (0 : Ω → ℝ)) :
    eLpNorm (X + Y) (ENNReal.ofReal p) P ^ 2 ≤
      eLpNorm X (ENNReal.ofReal p) P ^ 2 +
        ENNReal.ofReal (p - 1) * eLpNorm Y (ENNReal.ofReal p) P ^ 2 := by
  let : MeasurableSpace Ω := mΩ
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  let φ : ℝ → ℝ := fun a => ∫ ω, |X ω + a * Y ω| ^ p ∂P
  let φ' : ℝ → ℝ := fun a =>
    ∫ ω, p * (|X ω + a * Y ω| ^ (p - 2) * (X ω + a * Y ω) * Y ω) ∂P
  let φ'' : ℝ → ℝ := fun a =>
    ∫ ω, p * (p - 1) * (|X ω + a * Y ω| ^ (p - 2) * Y ω ^ 2) ∂P
  let B : ℝ := (∫ ω, |Y ω| ^ p ∂P) ^ (2 / p)
  have hB : 0 ≤ B := Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _) _
  have hφ (a : ℝ) : 0 ≤ φ a := integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hd (a : ℝ) : HasDerivAt φ (φ' a) a ∧ HasDerivAt φ' (φ'' a) a :=
    moment_derivatives hp hXLp hYLp a
  have hzero : φ' 0 = 0 := by
    simp only [φ', zero_mul, add_zero, integral_const_mul,
      weighted_centering P hm hp.le hX hXLp hYLp hcentered, mul_zero]
  have hb (a : ℝ) : φ'' a ≤ (p * (p - 1) * B) * (φ a) ^ (1 - 2 / p) := by
    have h := curvature_integral_le hp (hXLp.add (hYLp.const_mul a)) hYLp
    simp only [Pi.add_apply] at h
    dsimp only [φ'']
    rw [integral_const_mul]
    calc
      p * (p - 1) * (∫ ω, |X ω + a * Y ω| ^ (p - 2) * Y ω ^ 2 ∂P) ≤
          p * (p - 1) * ((φ a) ^ ((p - 2) / p) * B) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hp0.le hp1)
      _ = _ := by
        rw [show (p - 2) / p = 1 - 2 / p by field_simp]
        ring
  have hpow := power_bound (div_pos (by norm_num) hp0)
    ((div_lt_one hp0).mpr hp) (mul_nonneg (mul_nonneg hp0.le hp1) hB)
    hφ (fun a => (hd a).1) (fun a => (hd a).2) hzero hb
  have hc : (2 / p) * (p * (p - 1) * B) / 2 = (p - 1) * B := by
    field_simp
  rw [hc] at hpow
  simp only [φ, zero_mul, add_zero, one_mul] at hpow
  rw [eLpNorm_sq_eq_moment hp0 (hXLp.add hYLp), eLpNorm_sq_eq_moment hp0 hXLp,
    eLpNorm_sq_eq_moment hp0 hYLp, ← ENNReal.ofReal_mul hp1,
    ← ENNReal.ofReal_add (Real.rpow_nonneg (integral_nonneg fun _ =>
      Real.rpow_nonneg (abs_nonneg _) _) _) (mul_nonneg hp1 hB)]
  exact ENNReal.ofReal_le_ofReal hpow


/-- Rio's inequality for real martingale differences on a probability space.
The increment `d k` is observed at time `k + 1` and is centered given time `k`.

Reference: E. Rio, *Moment Inequalities for Sums of Dependent Random Variables
under Projective Conditions*, J. Theoret. Probab. 22 (2009), 146-163,
doi:10.1007/s10959-008-0155-9. This is The martingale-difference estimate. -/
theorem eLpNorm_sum_sq_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    {p : ℝ} (hp : 2 ≤ p) (d : ℕ → Ω → ℝ)
    (hadapted : ∀ k, StronglyMeasurable[ℱ (k + 1)] (d k))
    (hLp : ∀ k, MemLp (d k) (ENNReal.ofReal p) P)
    (hcentered : ∀ k, P[d k | ℱ k] =ᵐ[P] (0 : Ω → ℝ)) (n : ℕ) :
    eLpNorm (fun ω => ∑ k ∈ Finset.range n, d k ω) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (p - 1) *
        ∑ k ∈ Finset.range n, eLpNorm (d k) (ENNReal.ofReal p) P ^ 2 := by
  apply eLpNorm_sum_sq_le_of_step P ℱ d hadapted hLp hcentered ?_ n
  intro m hm X Y hX hXLp hYLp hzero
  let : MeasurableSpace Ω := mΩ
  rcases eq_or_lt_of_le hp with hp | hp
  · subst p
    norm_num at hXLp hYLp ⊢
    exact (eLpNorm_add_two_sq P hm hX hXLp hYLp hzero).le
  · exact eLpNorm_add_sq_le_of_two_lt P hm hp hX hXLp hYLp hzero

/-! ## First-order comparison for the Gaussian slab step

The lemmas below are additive. They extend the first moment derivative to `p = 2` and replace
the second-order comparison `power_bound` by a first-order one, which is what a conditionally
Gaussian increment needs: there the first derivative of `a ↦ ∫ |X + a Y|^p` is computed exactly
by Gaussian integration by parts, and no centring at `a = 0` is used. -/

/-- The weight `u ↦ |u|^(p-2) u` has derivative `(p-1)|u|^(p-2)` for every `2 ≤ p`.
At `p = 2` the weight is the identity, since `|u|^0 = 1` for every real `u`. -/
theorem hasDerivAt_weight_of_two_le {p : ℝ} (hp : 2 ≤ p) (x : ℝ) :
    HasDerivAt (fun u : ℝ => |u| ^ (p - 2) * u) ((p - 1) * |x| ^ (p - 2)) x := by
  rcases eq_or_lt_of_le hp with hp | hp
  · subst p
    convert hasDerivAt_id x using 1
    · ext u
      simp
    · norm_num
  · exact hasDerivAt_weight hp x

private theorem rpow_mul_mul_le_of_two_le {p u v w B : ℝ} (hp : 2 ≤ p)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (huB : u ≤ B) (hvB : v ≤ B) (hwB : w ≤ B) :
    u ^ (p - 2) * v * w ≤ B ^ p := by
  have hB : 0 ≤ B := hu.trans huB
  have hp2 : 0 ≤ p - 2 := by linarith
  have h1 : u ^ (p - 2) ≤ B ^ (p - 2) := Real.rpow_le_rpow hu huB hp2
  have h2 : u ^ (p - 2) * v ≤ B ^ (p - 2) * B :=
    mul_le_mul h1 hvB hv (Real.rpow_nonneg hB _)
  calc
    u ^ (p - 2) * v * w ≤ B ^ (p - 2) * B * B :=
      mul_le_mul h2 hwB hw (mul_nonneg (Real.rpow_nonneg hB _) hB)
    _ = B ^ p := by
      rw [mul_assoc, ← pow_two, ← Real.rpow_two,
        ← Real.rpow_add' hB (by linarith : p - 2 + 2 ≠ 0)]
      congr 1
      ring

/-- First derivative of `t ↦ ∫ |X + t Y|^p` for `X, Y ∈ L^p` and every `2 ≤ p`.
This is the first half of `moment_derivatives`, extended to `p = 2`. -/
theorem moment_hasDerivAt_of_two_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p : ℝ} (hp : 2 ≤ p) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal p) P) (a : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ ω, |X ω + t * Y ω| ^ p ∂P)
      (∫ ω, p * (|X ω + a * Y ω| ^ (p - 2) * (X ω + a * Y ω) * Y ω) ∂P) a := by
  have hp0 : 0 < p := by linarith
  let B : Ω → ℝ := fun ω => |X ω| + (|a| + 1) * |Y ω|
  have hB (ω : Ω) : 0 ≤ B ω := by dsimp [B]; positivity
  have hBp : MemLp B (ENNReal.ofReal p) P :=
    hX.norm.add (hY.norm.const_mul (|a| + 1))
  have hBi : Integrable (fun ω => B ω ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs, abs_of_nonneg (hB _)] using
      hBp.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
  have hYB (ω : Ω) : |Y ω| ≤ B ω := by
    dsimp [B]
    nlinarith [abs_nonneg (X ω), abs_nonneg (Y ω), abs_nonneg a]
  have hZB (t : ℝ) (ht : t ∈ Metric.ball a 1) (ω : Ω) : |X ω + t * Y ω| ≤ B ω := by
    have hta : |t - a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
    have htB : |t| ≤ |a| + 1 := by
      have h := abs_add_le (t - a) a
      rw [sub_add_cancel] at h
      linarith
    calc
      |X ω + t * Y ω| ≤ |X ω| + |t| * |Y ω| := by
        simpa only [abs_mul] using abs_add_le (X ω) (t * Y ω)
      _ ≤ B ω := by dsimp [B]; gcongr
  have hmeas (t : ℝ) : AEStronglyMeasurable (fun ω => |X ω + t * Y ω| ^ p) P :=
    ((hX.aestronglyMeasurable.add (hY.aestronglyMeasurable.const_mul t)).norm.aemeasurable.pow_const
      _).aestronglyMeasurable
  have hmeas' (t : ℝ) : AEStronglyMeasurable
      (fun ω => p * (|X ω + t * Y ω| ^ (p - 2) * (X ω + t * Y ω) * Y ω)) P := by
    have hz := hX.aestronglyMeasurable.add (hY.aestronglyMeasurable.const_mul t)
    exact ((((hz.norm.aemeasurable.pow_const _).mul hz.aemeasurable).mul
      hY.aestronglyMeasurable.aemeasurable).const_mul p).aestronglyMeasurable
  have hZa := hX.add (hY.const_mul a)
  have hint : Integrable (fun ω => |X ω + a * Y ω| ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs, Pi.add_apply] using
      hZa.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun t ω => p * (|X ω + t * Y ω| ^ (p - 2) * (X ω + t * Y ω) * Y ω))
    (Metric.ball_mem_nhds a (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas) hint (hmeas' a)
    (Eventually.of_forall fun ω t ht => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hp0,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact mul_le_mul_of_nonneg_left (rpow_mul_mul_le_of_two_le hp (abs_nonneg _)
        (abs_nonneg _) (abs_nonneg _) (hZB t ht ω) (hZB t ht ω) (hYB ω)) hp0.le)
    (hBi.const_mul p)
    (Eventually.of_forall fun ω t _ => by
      have h := (hasDerivAt_abs_rpow (X ω + t * Y ω) (by linarith : 1 < p)).comp t
        (((hasDerivAt_id t).mul_const (Y ω)).const_add (X ω))
      convert h using 1 <;> first | rfl | ring)
  exact hfirst.2

/-- First-order comparison, regularised by `ε > 0`: if `f ≥ 0` and
`f' a ≤ a K f(a)^(1-q)` on `[0,1]` with `0 < q ≤ 1` and `K ≥ 0`, then
`(f 1 + ε)^q ≤ (f 0 + ε)^q + q K / 2`. -/
theorem regularized_first_order_bound {f f' : ℝ → ℝ} {q K ε : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hK : 0 ≤ K) (hε : 0 < ε)
    (hf0 : ∀ a, 0 ≤ f a) (hf : ∀ a, HasDerivAt f (f' a) a)
    (hbound : ∀ a ∈ Icc (0 : ℝ) 1, f' a ≤ a * K * (f a) ^ (1 - q)) :
    (f 1 + ε) ^ q ≤ (f 0 + ε) ^ q + q * K / 2 := by
  have hpos (a : ℝ) : 0 < f a + ε := by linarith [hf0 a]
  have hd (a : ℝ) : HasDerivAt (fun t => q * K / 2 * t ^ 2 - (f t + ε) ^ q)
      (q * K * a - q * (f a + ε) ^ (q - 1) * f' a) a := by
    have h := (((hasDerivAt_id a).pow 2).const_mul (q * K / 2)).sub
      (((hf a).add_const ε).rpow_const (p := q) (Or.inl (hpos a).ne'))
    convert h using 1
    · ext t
      simp
    · simp only [id_eq]
      ring
  have hderiv (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      q * (f a + ε) ^ (q - 1) * f' a ≤ q * K * a := by
    have hpow : (f a) ^ (1 - q) ≤ (f a + ε) ^ (1 - q) :=
      Real.rpow_le_rpow (hf0 a) (by linarith) (by linarith)
    have hprod : (f a + ε) ^ (q - 1) * (f a + ε) ^ (1 - q) = 1 := by
      rw [← Real.rpow_add (hpos a), show q - 1 + (1 - q) = 0 by ring, Real.rpow_zero]
    have hw : 0 ≤ q * (f a + ε) ^ (q - 1) :=
      mul_nonneg hq0.le (Real.rpow_nonneg (hpos a).le _)
    have haK : 0 ≤ a * K := mul_nonneg ha.1 hK
    calc
      q * (f a + ε) ^ (q - 1) * f' a ≤
          q * (f a + ε) ^ (q - 1) * (a * K * (f a) ^ (1 - q)) :=
        mul_le_mul_of_nonneg_left (hbound a ha) hw
      _ ≤ q * (f a + ε) ^ (q - 1) * (a * K * (f a + ε) ^ (1 - q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow haK) hw
      _ = q * K * a * ((f a + ε) ^ (q - 1) * (f a + ε) ^ (1 - q)) := by ring
      _ = q * K * a := by rw [hprod, mul_one]
  have hm : MonotoneOn (fun t => q * K / 2 * t ^ 2 - (f t + ε) ^ q) (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun a _ => (hd a).continuousAt.continuousWithinAt)
      (fun a _ => (hd a).hasDerivWithinAt)
    intro a ha
    rw [interior_Icc] at ha
    exact sub_nonneg.mpr (hderiv a (Ioo_subset_Icc_self ha))
  have h := hm (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_sub,
    one_pow, mul_one] at h
  linarith

/-- First-order comparison: if `f ≥ 0` and `f' a ≤ a K f(a)^(1-q)` on `[0,1]` with
`0 < q ≤ 1` and `K ≥ 0`, then `f(1)^q ≤ f(0)^q + q K / 2`.
With `q = 2/p` and `K = p(p-1)B` the increment is `(p-1)B`. -/
theorem first_order_power_bound {f f' : ℝ → ℝ} {q K : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hK : 0 ≤ K)
    (hf0 : ∀ a, 0 ≤ f a) (hf : ∀ a, HasDerivAt f (f' a) a)
    (hbound : ∀ a ∈ Icc (0 : ℝ) 1, f' a ≤ a * K * (f a) ^ (1 - q)) :
    (f 1) ^ q ≤ (f 0) ^ q + q * K / 2 := by
  have ht (a : ℝ) : Tendsto (fun ε : ℝ => (f a + ε) ^ q) (𝓝[>] 0) (𝓝 ((f a) ^ q)) := by
    have hc : ContinuousAt (fun ε : ℝ => (f a + ε) ^ q) 0 :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inr hq0.le)
    simpa only [add_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  apply le_of_tendsto_of_tendsto (ht 1) ((ht 0).add_const (q * K / 2))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact regularized_first_order_bound hq0 hq1 hK hε hf0 hf hbound

/-- Moment form of the first-order comparison, for every `2 ≤ p`. If the first derivative of
`φ(a) = ∫ |X + a Y|^p` satisfies `φ'(a) ≤ a · p(p-1)B · φ(a)^(1-2/p)` on `[0,1]` with `B ≥ 0`,
then `‖X + Y‖_p² ≤ ‖X‖_p² + (p-1)B`. -/
theorem eLpNorm_add_sq_le_of_deriv_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p : ℝ} (hp : 2 ≤ p) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal p) P)
    {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ a ∈ Icc (0 : ℝ) 1,
      (∫ ω, p * (|X ω + a * Y ω| ^ (p - 2) * (X ω + a * Y ω) * Y ω) ∂P) ≤
        a * (p * (p - 1) * B) * (∫ ω, |X ω + a * Y ω| ^ p ∂P) ^ (1 - 2 / p)) :
    eLpNorm (X + Y) (ENNReal.ofReal p) P ^ 2 ≤
      eLpNorm X (ENNReal.ofReal p) P ^ 2 + ENNReal.ofReal ((p - 1) * B) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hφ (a : ℝ) : 0 ≤ ∫ ω, |X ω + a * Y ω| ^ p ∂P :=
    integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hpow := first_order_power_bound
    (f := fun a => ∫ ω, |X ω + a * Y ω| ^ p ∂P)
    (f' := fun a => ∫ ω, p * (|X ω + a * Y ω| ^ (p - 2) * (X ω + a * Y ω) * Y ω) ∂P)
    (div_pos two_pos hp0) ((div_le_one hp0).mpr hp)
    (mul_nonneg (mul_nonneg hp0.le hp1) hB) hφ
    (fun a => moment_hasDerivAt_of_two_le hp hX hY a) hderiv
  have hc : (2 / p) * (p * (p - 1) * B) / 2 = (p - 1) * B := by
    field_simp
  rw [hc] at hpow
  simp only [zero_mul, add_zero, one_mul] at hpow
  rw [eLpNorm_sq_eq_moment hp0 (hX.add hY), eLpNorm_sq_eq_moment hp0 hX,
    ← ENNReal.ofReal_add (Real.rpow_nonneg (integral_nonneg fun _ =>
      Real.rpow_nonneg (abs_nonneg _) _) _) (mul_nonneg hp1 hB)]
  exact ENNReal.ofReal_le_ofReal hpow

end WalshIntegral.Rio
