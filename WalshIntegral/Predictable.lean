module

public import Mathlib

@[expose] public section

/-!
# Real-time predictability and predictable causal parametric integration.
-/

open MeasureTheory Set
open scoped NNReal

namespace WalshIntegral.Predictable

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The predictable sigma-algebra with the corrected nonpositive-time
generators. All real time and space measurability uses the Borel structures. -/
@[instance_reducible]
def predictableSigma (F : Filtration ℝ≥0 mΩ) : MeasurableSpace (ℝ × ℝ × Ω) :=
  MeasurableSpace.generateFrom {S |
    (∃ (s t : ℝ≥0) (A : Set ℝ) (B : Set Ω),
      s < t ∧ MeasurableSet A ∧ MeasurableSet[F s] B ∧
        S = Ioc (s : ℝ) (t : ℝ) ×ˢ (A ×ˢ B)) ∨
    (∃ (C A : Set ℝ) (B : Set Ω),
      MeasurableSet C ∧ C ⊆ Iic 0 ∧ MeasurableSet A ∧ MeasurableSet[F 0] B ∧
        S = C ×ˢ (A ×ˢ B))}

/-- Predictable sets are measurable in the ambient product sigma-algebra. -/
theorem predictableSigma_le (F : Filtration ℝ≥0 mΩ) :
    predictableSigma F ≤ Prod.instMeasurableSpace := by
  apply MeasurableSpace.generateFrom_le
  rintro S (⟨s, t, A, B, _, hA, hB, rfl⟩ | ⟨C, A, B, hC, _, hA, hB, rfl⟩)
  · exact measurableSet_Ioc.prod (hA.prod (F.le s _ hB))
  · exact hC.prod (hA.prod (F.le 0 _ hB))

private theorem measurableSet_pos_tail (F : Filtration ℝ≥0 mΩ)
    (a : ℝ≥0) {A : Set ℝ} {B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet[F a] B) :
    MeasurableSet[predictableSigma F] (Ioi (a : ℝ) ×ˢ (A ×ˢ B)) := by
  have heq : Ioi (a : ℝ) ×ˢ (A ×ˢ B) =
      ⋃ n : ℕ, Ioc (a : ℝ) ((a + (n + 1) : ℝ≥0) : ℝ) ×ˢ (A ×ˢ B) := by
    ext q
    simp only [mem_prod, mem_Ioi, mem_Ioc, mem_iUnion, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_one]
    constructor
    · rintro ⟨ha, hAB⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (q.1 - a)
      exact ⟨n, ⟨ha, by linarith⟩, hAB⟩
    · rintro ⟨n, ⟨ha, _⟩, hAB⟩
      exact ⟨ha, hAB⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSpace.measurableSet_generateFrom
  exact Or.inl ⟨a, a + (n + 1), A, B, by simp, hA, hB, rfl⟩

private theorem measurableSet_nonpos (F : Filtration ℝ≥0 mΩ)
    {C A : Set ℝ} {B : Set Ω} (hC : MeasurableSet C) (hC0 : C ⊆ Iic 0)
    (hA : MeasurableSet A) (hB : MeasurableSet[F 0] B) :
    MeasurableSet[predictableSigma F] (C ×ˢ (A ×ˢ B)) :=
  MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨C, A, B, hC, hC0, hA, hB, rfl⟩)

private theorem measurableSet_all_time (F : Filtration ℝ≥0 mΩ)
    {A : Set ℝ} {B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet[F 0] B) :
    MeasurableSet[predictableSigma F] (univ ×ˢ (A ×ˢ B)) := by
  have h := (measurableSet_nonpos F measurableSet_Iic Subset.rfl hA hB).union
    (measurableSet_pos_tail F 0 hA hB)
  simpa only [NNReal.coe_zero, ← union_prod, Iic_union_Ioi] using h

private theorem measurableSet_time_tail (F : Filtration ℝ≥0 mΩ) (a : ℝ) :
    MeasurableSet[predictableSigma F] (Ioi a ×ˢ (univ ×ˢ (univ : Set Ω))) := by
  by_cases ha : 0 ≤ a
  · exact measurableSet_pos_tail F ⟨a, ha⟩ MeasurableSet.univ MeasurableSet.univ
  · have h := (measurableSet_nonpos F (C := Ioc a 0) measurableSet_Ioc
      (fun _ hx => hx.2) MeasurableSet.univ MeasurableSet.univ).union
      (measurableSet_pos_tail F 0 MeasurableSet.univ MeasurableSet.univ)
    have heq : Ioc a 0 ∪ Ioi 0 = Ioi a := by
      ext t
      simp only [mem_union, mem_Ioc, mem_Ioi]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith
      · intro h
        by_cases ht : t ≤ 0
        · exact Or.inl ⟨h, ht⟩
        · exact Or.inr (lt_of_not_ge ht)
    simpa only [NNReal.coe_zero, ← union_prod, heq] using h

/-- Every deterministic Borel time-space function is predictable by composition. -/
theorem measurable_coord (F : Filtration ℝ≥0 mΩ) :
    Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => (q.1, q.2.1)) := by
  let : MeasurableSpace (ℝ × ℝ × Ω) := predictableSigma F
  have ht : Measurable (fun q : ℝ × ℝ × Ω => q.1) := by
    apply measurable_of_Ioi
    intro a
    convert measurableSet_time_tail F a using 1
    ext q
    simp
  have hx : Measurable (fun q : ℝ × ℝ × Ω => q.2.1) := by
    intro A hA
    convert measurableSet_all_time F hA (B := univ) MeasurableSet.univ using 1
    ext q
    simp
  exact ht.prodMk hx

/-- Enlarging the filtration enlarges the predictable sigma-algebra. -/
theorem predictableSigma_mono {F G : Filtration ℝ≥0 mΩ} (hFG : F ≤ G) :
    predictableSigma F ≤ predictableSigma G := by
  apply MeasurableSpace.generateFrom_le
  rintro S (⟨s, t, A, B, hst, hA, hB, rfl⟩ | ⟨C, A, B, hC, hC0, hA, hB, rfl⟩)
  · exact MeasurableSpace.measurableSet_generateFrom
      (Or.inl ⟨s, t, A, B, hst, hA, hFG s _ hB, rfl⟩)
  · exact measurableSet_nonpos G hC hC0 hA (hFG 0 _ hB)

/-- For the full constant filtration, predictability is product measurability. -/
theorem predictableSigma_const_eq :
    predictableSigma (Filtration.const ℝ≥0 mΩ le_rfl) =
      (Prod.instMeasurableSpace : MeasurableSpace (ℝ × ℝ × Ω)) := by
  apply le_antisymm (predictableSigma_le _)
  let F : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  let : MeasurableSpace (ℝ × ℝ × Ω) := predictableSigma F
  have hω : Measurable (fun q : ℝ × ℝ × Ω => q.2.2) := by
    intro B hB
    convert measurableSet_all_time F MeasurableSet.univ hB using 1
    ext q
    simp
  have h := (measurable_coord F).fst.prodMk ((measurable_coord F).snd.prodMk hω)
  exact h

/-- A jointly Borel strictly causal kernel preserves predictability under
parametric Bochner integration against time-space Lebesgue measure. No
integrability or moment bound is required: the integral is zero when its
integrand is not integrable. Values at negative input times are allowed.

For a causal drift integral, take `K t x s y` to be the heat kernel times the
indicator of `0 < s ∧ s < t`. Checking generator preimages on `{s < t}` supplies
predictable output tails for the causal restriction. -/
theorem isPredictable_parametric_integral (F : Filtration ℝ≥0 mΩ)
    (K : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hK : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      K q.1.1 q.1.2 q.2.1 q.2.2))
    (hcausal : ∀ t x s y, t ≤ s → K t x s y = 0)
    (b : ℝ → ℝ → ℝ) (hb : Measurable (fun q : ℝ × ℝ => b q.1 q.2))
    (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) :
    Measurable[predictableSigma F] (fun z : ℝ × ℝ × Ω =>
      ∫ q : ℝ × ℝ, K z.1 z.2.1 q.1 q.2 * b q.1 (Φ q.1 q.2 z.2.2)
        ∂(volume : Measure (ℝ × ℝ))) := by
  classical
  let : MeasurableSpace (ℝ × ℝ × Ω) := predictableSigma F
  let D : Set ((ℝ × ℝ) × (ℝ × ℝ × Ω)) := {z | z.1.1 < z.2.1}
  have ht : Measurable (fun z : ℝ × ℝ × Ω => z.1) := (measurable_coord F).fst
  have hD : MeasurableSet D :=
    measurableSet_lt measurable_fst.fst (ht.comp measurable_snd)
  have hmap : Measurable (fun z : D => (z.val.1.1, z.val.1.2, z.val.2.2.2)) := by
    apply measurable_generateFrom
    rintro S (⟨a, c, A, B, _, hA, hB, rfl⟩ | ⟨C, A, B, hC, _, hA, hB, rfl⟩)
    · have hm := ((measurableSet_Ioc (a := (a : ℝ)) (b := (c : ℝ))).prod hA).prod
        (measurableSet_pos_tail F a MeasurableSet.univ hB)
      convert hm.preimage measurable_subtype_coe using 1
      ext z
      simp only [mem_preimage, mem_prod, mem_Ioc, mem_Ioi, mem_univ, true_and]
      constructor
      · rintro ⟨hac, hA', hB'⟩
        exact ⟨⟨hac, hA'⟩, lt_trans hac.1 z.property, hB'⟩
      · rintro ⟨⟨hac, hA'⟩, _, hB'⟩
        exact ⟨hac, hA', hB'⟩
    · have hm := (hC.prod hA).prod
        (measurableSet_all_time F MeasurableSet.univ hB)
      convert hm.preimage measurable_subtype_coe using 1
      ext z
      simp only [mem_preimage, mem_prod, mem_univ, true_and]
      tauto
  have hbD : Measurable (fun z : D => b z.val.1.1
      (Φ z.val.1.1 z.val.1.2 z.val.2.2.2)) :=
    hb.comp ((measurable_fst.fst.comp measurable_subtype_coe).prodMk (hΦ.comp hmap))
  have hG : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ × Ω) =>
      if z.1.1 < z.2.1 then b z.1.1 (Φ z.1.1 z.1.2 z.2.2.2) else 0) :=
    hbD.dite measurable_const hD
  have hKG : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ × Ω) =>
      K z.2.1 z.2.2.1 z.1.1 z.1.2 *
        (if z.1.1 < z.2.1 then b z.1.1 (Φ z.1.1 z.1.2 z.2.2.2) else 0)) :=
    (hK.comp (((measurable_coord F).comp measurable_snd).prodMk measurable_fst)).mul hG
  have heq : (fun z : (ℝ × ℝ) × (ℝ × ℝ × Ω) =>
      K z.2.1 z.2.2.1 z.1.1 z.1.2 *
        (if z.1.1 < z.2.1 then b z.1.1 (Φ z.1.1 z.1.2 z.2.2.2) else 0)) =
      (fun z => K z.2.1 z.2.2.1 z.1.1 z.1.2 * b z.1.1 (Φ z.1.1 z.1.2 z.2.2.2)) := by
    funext z
    by_cases h : z.1.1 < z.2.1
    · simp [h]
    · simp [h, hcausal _ _ _ _ (le_of_not_gt h)]
  rw [heq] at hKG
  exact (hKG.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable

end WalshIntegral.Predictable
