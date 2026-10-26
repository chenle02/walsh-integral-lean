module

public import WalshIntegral.Predictable

@[expose] public section

open MeasureTheory Set WalshIntegral.Predictable
open scoped NNReal

namespace WalshIntegralTest.NegPredictableMeasurable

scoped instance boolMeasurableSpace : MeasurableSpace Bool := ⊤

def F : Filtration ℝ≥0 (⊤ : MeasurableSpace Bool) := Filtration.const ℝ≥0 ⊥ bot_le

theorem section_measurable (t x : ℝ) :
    @Measurable Bool (ℝ × ℝ × Bool) ⊥ (predictableSigma F)
      (fun ω => (t, x, ω)) := by
  let : MeasurableSpace Bool := ⊥
  unfold predictableSigma
  apply measurable_generateFrom
  rintro S (⟨s, u, A, B, _, _, hB, rfl⟩ | ⟨C, A, B, _, _, _, hB, rfl⟩)
  · change MeasurableSet[⊥] B at hB
    exact (MeasurableSet.const (α := Bool) (t ∈ Ioc (s : ℝ) (u : ℝ))).inter
      ((MeasurableSet.const (α := Bool) (x ∈ A)).inter hB)
  · change MeasurableSet[⊥] B at hB
    exact (MeasurableSet.const (α := Bool) (t ∈ C)).inter
      ((MeasurableSet.const (α := Bool) (x ∈ A)).inter hB)

theorem bottom_constant {f : Bool → ℝ} (hf : Measurable[⊥] f) : f true = f false := by
  have h := MeasurableSpace.measurableSet_bot_iff.mp (hf (measurableSet_singleton (f true)))
  rcases h with h | h
  · have : true ∈ f ⁻¹' {f true} := by simp
    rw [h] at this
    exact this.elim
  · have : false ∈ f ⁻¹' {f true} := by rw [h]; trivial
    exact (mem_singleton_iff.mp this).symm

theorem ambient_measurable :
    Measurable (fun q : ℝ × ℝ × Bool => if q.2.2 then (1 : ℝ) else 0) := by
  exact (measurable_from_top (f := fun ω : Bool => if ω then (1 : ℝ) else 0)).comp
    measurable_snd.snd

theorem not_predictable :
    ¬ Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Bool => if q.2.2 then (1 : ℝ) else 0) := by
  intro h
  have hc := bottom_constant (h.comp (section_measurable 1 0))
  norm_num at hc

end WalshIntegralTest.NegPredictableMeasurable
