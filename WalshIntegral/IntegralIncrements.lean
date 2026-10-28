/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import WalshIntegral.Integral

/-!
# Difference isometries for predictable stochastic integrals

Actual predictable L² classes supply the finite integration domain. Differences
of integrals preserve L² seminorms, and deterministic weighted increments have
an exact lower-integral second-moment formula. No continuity of the random
field is required, and totalized integrals are used only with domain witnesses.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace WalshIntegral.IntegralIncrements
open MeasureTheory ProbabilityTheory Filter Set WhiteNoise Predictable Integral
open scoped ENNReal NNReal Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

private theorem lintegral_enorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ = ‖f‖ₑ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (Lp.aestronglyMeasurable f) (μ := μ)
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [Lp.enorm_def, h]

private theorem enorm_mul_sq (a b : ℝ) :
    ‖a*b‖ₑ ^ 2 = ENNReal.ofReal (a^2)*‖b‖ₑ^2 := by
  rw [enorm_mul,mul_pow,Real.enorm_eq_ofReal_abs,←ENNReal.ofReal_pow (abs_nonneg _),sq_abs]

private theorem lintegral_sample {f : ℝ × ℝ × Ω → ℝ≥0∞}
    (hf : AEMeasurable f (spaceTimeSample P)) [SFinite P] :
    ∫⁻ q, f q ∂spaceTimeSample P = ∫⁻ s in Ioi 0, ∫⁻ y, ∫⁻ ω, f (s,y,ω) ∂P := by
  have hm := hf.measurable_mk
  have hae : f =ᵐ[(volume.restrict (Ioi (0:ℝ))).prod (volume.prod P)] hf.mk f := hf.ae_eq_mk
  change ∫⁻ q, f q ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.prod P)) = _
  rw [lintegral_congr_ae hae,lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with s hs
  rw [lintegral_prod (fun z => hf.mk f (s,z)) (hm.comp measurable_prodMk_left).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with y hy
  exact lintegral_congr_ae (hy.mono fun ω h => h.symm)

/-- Difference isometry for the totalized representatives on their actual domains. -/
theorem walshT_sub_eLpNorm [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsWhiteNoise P F W)
    (G G' : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G) (hG' : InDomain F P G') :
    eLpNorm (fun ω => walshT hW G ω - walshT hW G' ω) 2 P =
      eLpNorm (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2 - G' q.1 q.2.1 q.2.2)
        2 (spaceTimeSample P) := by
  let a := toPredL2 G hG
  let b := toPredL2 G' hG'
  calc
    _ = eLpNorm (fun ω => (walshL2 hW a - walshL2 hW b) ω) 2 P := by
      apply eLpNorm_congr_ae
      filter_upwards [walshT_ae_eq hW G hG, walshT_ae_eq hW G' hG',
        Lp.coeFn_sub (walshL2 hW a) (walshL2 hW b)] with ω ha hb hab
      exact (congrArg₂ (· - ·) ha hb).trans hab.symm
    _ = ‖walshL2 hW (a - b)‖ₑ := by rw [map_sub, Lp.enorm_def]
    _ = ‖a - b‖ₑ := (walshL2 hW).enorm_map _
    _ = _ := by
      change ‖(a - b).val‖ₑ = _
      rw [Lp.enorm_def]
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub a.val b.val, toPredL2_ae G hG,
        toPredL2_ae G' hG'] with q hab ha hb
      exact hab.trans (congrArg₂ (· - ·) ha hb)

/-- The squared norm of an actual weighted integral increment, in iterated
positive-time, space, and probability form. The weight and field need no
additional measurability assumptions beyond the actual class equalities. -/
theorem enorm_sub_sq_eq_iter [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W)
    (g k : PredL2 F P) (a b : ℝ × ℝ → ℝ) (Φ : ℝ → ℝ → Ω → ℝ)
    (hg : (fun q => (g : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P]
      (fun q => a (q.1,q.2.1)*Φ q.1 q.2.1 q.2.2))
    (hk : (fun q => (k : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P]
      (fun q => b (q.1,q.2.1)*Φ q.1 q.2.1 q.2.2)) :
    ‖walshL2 hW g - walshL2 hW k‖ₑ^2 =
      ∫⁻ s in Ioi 0, ∫⁻ y, ENNReal.ofReal ((a (s,y)-b (s,y))^2)*
        ∫⁻ ω, ‖Φ s y ω‖ₑ^2 ∂P := by
  let d : ℝ × ℝ × Ω → ℝ := fun q => (a (q.1,q.2.1)-b (q.1,q.2.1))*Φ q.1 q.2.1 q.2.2
  have hd : (fun q => ((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P] d := by
    filter_upwards [Lp.coeFn_sub (g : Lp ℝ 2 (spaceTimeSample P))
      (k : Lp ℝ 2 (spaceTimeSample P)), hg,hk] with q hq hgq hkq
    change ((g : Lp ℝ 2 (spaceTimeSample P))-(k : Lp ℝ 2 (spaceTimeSample P))) q = _
    rw [hq,Pi.sub_apply,hgq,hkq]
    dsimp only [d]
    ring
  rw [←map_sub, (walshL2 hW).enorm_map]
  change ‖((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P))‖ₑ^2 = _
  rw [←lintegral_enorm_sq]
  let f : ℝ × ℝ × Ω → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((a (q.1,q.2.1)-b (q.1,q.2.1))^2)*‖Φ q.1 q.2.1 q.2.2‖ₑ^2
  have heq : (fun q => ‖((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) q‖ₑ^2) =ᵐ[spaceTimeSample P] f :=
    hd.mono fun q hq => by
      change ‖((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) q‖ₑ^2 = _
      change ((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) q = d q at hq
      rw [hq]
      exact enorm_mul_sq _ _
  have hf : AEMeasurable f (spaceTimeSample P) :=
    ((Lp.aestronglyMeasurable ((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P))).enorm.pow_const 2).congr heq
  rw [lintegral_congr_ae heq,lintegral_sample hf]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro y
  dsimp only [f]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Product-measure form of the actual weighted increment identity. -/
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
      ∫⁻ q, ENNReal.ofReal ((a q-b q)^2)*(∫⁻ ω, ‖Φ q.1 q.2 ω‖ₑ^2 ∂P) ∂timeSpaceVolume := by
  rw [enorm_sub_sq_eq_iter hW g k a b Φ hg hk]
  exact (lintegral_prod _ (((ha.sub hb).pow_const 2).ennreal_ofReal.mul hΦ).aemeasurable).symm

end WalshIntegral.IntegralIncrements
end
