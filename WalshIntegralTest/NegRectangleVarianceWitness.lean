module

public import WalshIntegral

public section

open MeasureTheory ProbabilityTheory WalshIntegral.WhiteNoise
open scoped ENNReal NNReal

namespace WalshIntegralTest.NegRectangleVariance

theorem rectangle_law_correct {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W)
    (s t : ℝ≥0) (hst : s < t) (A : Set ℝ) (hA : MeasurableSet A)
    (hAfin : volume A ≠ ∞) :
    P.map (fun ω => W (rectangle s t A hA hAfin) ω) =
      gaussianReal 0 ((t - s) * (volume A).toNNReal) := by
  exact hW.rectangle_law s t hst A hA hAfin

theorem not_doubled_rectangle_law {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsWhiteNoise P F W) :
    ¬ ∀ (s t : ℝ≥0) (_hst : s < t) (A : Set ℝ)
        (hA : MeasurableSet A) (hAfin : volume A ≠ ∞),
      P.map (fun ω => W (rectangle s t A hA hAfin) ω) =
        gaussianReal 0 (2 * (t - s) * (volume A).toNNReal) := by
  intro hfalse
  have hAfin : volume (Set.Ioc (0 : ℝ) 1) ≠ ∞ := by simp
  have hbad := hfalse 0 1 (by norm_num) (Set.Ioc 0 1) measurableSet_Ioc hAfin
  rw [rectangle_law_correct hW 0 1 (by norm_num) (Set.Ioc 0 1)
    measurableSet_Ioc hAfin] at hbad
  have hvar := congrArg (fun μ : Measure ℝ => variance id μ) hbad
  simp only [variance_id_gaussianReal] at hvar
  norm_num [Real.volume_Ioc] at hvar

end WalshIntegralTest.NegRectangleVariance
