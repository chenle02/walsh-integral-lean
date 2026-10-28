/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# L² convergence and summable moment envelopes

Summable successive L² differences identify an almost-everywhere pointwise
limit with the complete-space L² limit. Square-root coefficient envelopes
also bound sums of L² seminorms, including zero profile constants.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace WalshIntegral.LpConvergence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Summable successive L² differences and full-sequence almost-everywhere
convergence identify the same limit in L² on a finite measure space. -/
theorem l2_tendsto_of_summable_differences [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 P) (g : Ω → ℝ)
    (_hg : AEStronglyMeasurable g P)
    (hsum : (∑' n, eLpNorm (f (n + 1) - f n) 2 P) ≠ ⊤)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    MemLp g 2 P ∧ Tendsto (fun n => eLpNorm (f n - g) 2 P) atTop (𝓝 0) := by
  let v : ℕ → Lp ℝ 2 P := fun n => (hf n).toLp (f n)
  have hc : CauchySeq v :=
    cauchySeq_of_edist_le_of_tsum_ne_top
      (fun n => eLpNorm (f (n + 1) - f n) 2 P)
      (fun n => by
        change edist ((hf n).toLp (f n)) ((hf (n + 1)).toLp (f (n + 1))) ≤ _
        rw [Lp.edist_toLp_toLp, eLpNorm_sub_comm]) hsum
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  have hmz : TendstoInMeasure P f atTop (fun ω => z ω) :=
    TendstoInMeasure.congr_left (fun n => (hf n).coeFn_toLp)
      (tendstoInMeasure_of_tendsto_Lp hz)
  have hmg : TendstoInMeasure P f atTop g :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hf n).aestronglyMeasurable) hae
  have heq : (fun ω => z ω) =ᵐ[P] g := tendstoInMeasure_ae_unique hmz hmg
  refine ⟨(memLp_congr_ae heq).mp (Lp.memLp z), ?_⟩
  have hn := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' v z).mp hz
  have hh : (fun n => eLpNorm (f n - g) 2 P) =
      (fun n => eLpNorm (⇑(v n) - ⇑z) 2 P) := by
    funext n
    exact (eLpNorm_congr_ae ((hf n).coeFn_toLp.sub heq)).symm
  rw [hh]
  exact hn

/-- Taking the square root of a genuine moment bound controls the L² seminorm. -/
theorem eLpNorm_two_le_of_moment_bound {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) {a : ℝ} (ha : 0 ≤ a) {C : ℝ≥0∞}
    (hbound : ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal a * C) :
    eLpNorm f 2 P ≤ ENNReal.ofReal (a ^ (1 / 2 : ℝ)) * C ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat]
  calc
    _ ≤ (ENNReal.ofReal a * C) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg ha (by norm_num)]

/-- A summable square-root coefficient envelope yields a finite sum of L² norms.
The profile constant may vanish; no division by it is used. -/
theorem tsum_eLpNorm_two_lt_top_of_moment_bound (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hsum : Summable (fun n => a n ^ (1 / 2 : ℝ)))
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ n, ∫⁻ ω, ‖f n ω‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (a n) * C) :
    (∑' n, eLpNorm (f n) 2 P) < ⊤ := by
  have hle : (∑' n, eLpNorm (f n) 2 P) ≤
      ∑' n, ENNReal.ofReal (a n ^ (1 / 2 : ℝ)) * C ^ (1 / 2 : ℝ) :=
    ENNReal.tsum_le_tsum fun n => eLpNorm_two_le_of_moment_bound (hf n) (ha n) (hbound n)
  rw [ENNReal.tsum_mul_right] at hle
  exact hle.trans_lt (ENNReal.mul_lt_top hsum.tsum_ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne))

end WalshIntegral.LpConvergence
end
