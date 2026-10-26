module

public import WalshIntegral

public section

open MeasureTheory WalshIntegral.Predictable
open scoped NNReal

namespace WalshIntegralTest.NegPredictableTrivial

theorem sigma_correct : predictableSigma (Filtration.const ℝ≥0 (inferInstance : MeasurableSpace Unit)
    le_rfl) = (Prod.instMeasurableSpace : MeasurableSpace (ℝ × ℝ × Unit)) := by
  exact predictableSigma_const_eq

end WalshIntegralTest.NegPredictableTrivial
