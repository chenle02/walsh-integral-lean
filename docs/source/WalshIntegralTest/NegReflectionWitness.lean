import WalshIntegral.Integral

noncomputable section

open MeasureTheory WalshIntegral.WhiteNoise WalshIntegral.Integral
open scoped NNReal ENNReal

namespace WalshIntegralTest.NegReflection

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {W : H →L[ℝ] Lp ℝ 2 P}

def meanReflect (G : ℝ → ℝ → Ω → ℝ) : ℝ → ℝ → Ω → ℝ :=
  fun t x ω => 2 * (∫ η, G t x η ∂P) - G t x ω

omit [IsProbabilityMeasure P] in
theorem reflection_centered (e : Elementary F) (hc : ∫ ω, e.coeff ω ∂P = 0) :
    meanReflect (P := P) e.field = fun t x ω => (-1 : ℝ) • e.field t x ω := by
  funext t x ω
  simp [meanReflect, Elementary.field, integral_mul_const, hc]

theorem reflection_inDomain (e : Elementary F) (hc : ∫ ω, e.coeff ω ∂P = 0) :
    InDomain F P (meanReflect (P := P) e.field) := by
  rw [reflection_centered e hc]
  exact e.inDomain.smul (-1)

theorem reflected_disagrees (hW : IsWhiteNoise P F W) (e : Elementary F)
    (hc : ∫ ω, e.coeff ω ∂P = 0)
    (hsign : ∀ ω, e.coeff ω = 1 ∨ e.coeff ω = -1)
    (hr : rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top ≠ 0) :
    ¬ (walshT hW (meanReflect (P := P) e.field) =ᵐ[P]
      fun ω => e.coeff ω *
        W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top) ω) := by
  have he : walshT hW e.field =ᵐ[P] fun ω => e.coeff ω *
      W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top) ω := by
    have h := walshT_ae_eq hW e.field e.inDomain
    change walshT hW e.field =ᵐ[P] _ at h
    rw [show toPredL2 e.field e.inDomain = elementaryClass P e from rfl,
      walshL2_elementary] at h
    exact h.trans (elementaryIntegral_ae W e)
  rw [reflection_centered e hc]
  intro hagree
  have hneg := walshT_smul hW (-1) e.field e.inDomain
  have hz : W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top) = 0 := by
    apply Lp.ext
    filter_upwards [hagree, hneg, he, Lp.coeFn_zero ℝ 2 P] with ω ha hn he hz
    rw [hz]
    change W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top) ω = 0
    simp only [smul_eq_mul] at ha
    rw [he] at hn
    rcases hsign ω with hs | hs <;> rw [hs] at ha hn <;> linarith
  apply hr
  apply hW.isometry.injective
  simpa using hz

end WalshIntegralTest.NegReflection
