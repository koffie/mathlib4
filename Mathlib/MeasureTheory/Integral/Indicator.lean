/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Results about indicator functions and measures

## Main results

The section "IndicatorConstMeasurable" contains simple results showing that if the indicator
function of a set is a pointwise limit (resp. a.e.-limit) of indicators of measurable
(resp. null-measurable) sets, then the set itself is measurable (resp. null-measurable).

The section "Limits of measures of sets from limits of indicators" contains simple results showing
that the pointwise convergence of indicator functions of sets implies the convergence of measures:
limᵢ Aᵢ.indicator = A.indicator implies limᵢ μ(Aᵢ) = μ(A).

## Tags

indicator function, measure, dominated convergence of measure

-/

/-
Where should these results live? Should they be put in different files or should a new file
devoted to measure-theoretic lemmas about indicators be created?

I believe those in section IndicatorConstMeasurable only have prerequisites
 * `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`
 * `Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic`
   (for the ones using `AEStronglyMeasurable`)

Those in section TendstoMeasureOfTendstoIndicator (except to the extent they rely on measurability)
only have prerequisites
 * `Mathlib.MeasureTheory.Integral.Lebesgue`
 -/

open MeasureTheory Set Filter Topology ENNReal NNReal BigOperators

section IndicatorConstMeasurable

-- I didn't find the following lemma, the closest variants were around `indicator_const_preimage`.
--#check indicator_const_preimage

/-- The measurability of a set `A` is equivalent to the measurability of the indicator function
which takes a constant value `b ≠ 0` on a set `A` and `0` elsewhere. -/
lemma measurable_indicator_const_iff [MeasurableSpace α] (A : Set α) [Zero β] [MeasurableSpace β]
  [MeasurableSingletonClass β] (b : β) [NeZero b] :
    Measurable (A.indicator (fun _ ↦ b)) ↔ MeasurableSet A := by
  constructor <;> intro h
  · convert h (MeasurableSet.singleton (0 : β)).compl
    ext a
    simp [‹NeZero b›.ne]
  · have A_mble : MeasurableSet A := by simpa only [‹NeZero b›.ne, false_or] using h
    intro B _
    rcases indicator_const_preimage A B b with ⟨hB⟩ | ⟨hB | ⟨hB | (hB : _ = _)⟩⟩ <;>
    simp [hB, A_mble]

-- #find_home measurable_indicator_const_iff
-- Gives: `Mathlib.MeasureTheory.Integral.Indicator`, i.e., this file itself...
-- But why? Could be in `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`!

#check aemeasurable_indicator_iff₀

/-- A characterization of the a.e.-measurability of the indicator function which takes a constant
value `b` on a set `A` and `0` elsewhere. -/
lemma aemeasurable_indicator_const_iff₀ [MeasurableSpace α] (A : Set α) [DecidableEq β]
  [Zero β] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : Measure α) (b : β) [NeZero b] :
    AEMeasurable (A.indicator (fun _ ↦ b)) μ ↔ NullMeasurableSet A μ := by
  constructor <;> intro h
  · convert h.nullMeasurable (MeasurableSet.singleton (0 : β)).compl
    rw [indicator_const_preimage_eq_union A {0}ᶜ b]
    simp [NeZero.ne b]
  · exact (aemeasurable_indicator_iff₀ h).mpr aemeasurable_const

end IndicatorConstMeasurable

section TendstoMeasureOfTendstoIndicator
/-!
### Limits of measures of sets from limits of indicators

This section contains results showing that the pointwise convergence of indicator functions of
sets implies the convergence of measures: limᵢ Aᵢ.indicator = A.indicator implies
limᵢ μ(Aᵢ) = μ(A).
-/

variable {α : Type _} [MeasurableSpace α] {A : Set α}
variable {ι : Type _} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicator functions of measurable sets `Aᵢ` converge to the indicator function of
a set `A` along a nontrivial countably generated filter, then `A` is also measurable. -/
lemma measurableSet_of_tendsto_indicator [NeBot L] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    MeasurableSet A := by
  simp_rw [← measurable_indicator_const_iff _ (1 : ℝ≥0∞)] at As_mble ⊢
  exact measurable_of_tendsto_ennreal' L As_mble h_lim

/-- If the indicator functions of a.e.-measurable sets `Aᵢ` converge a.e. to the indicator function
of a set `A` along a nontrivial countably generated filter, then `A` is also a.e.-measurable. -/
lemma nullMeasurableSet_of_tendsto_indicator [NeBot L] (μ : Measure α)
    (As_mble : ∀ i, NullMeasurableSet (As i) μ)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    NullMeasurableSet A μ := by
  simp_rw [← aemeasurable_indicator_const_iff₀ _ μ (1 : ℝ≥0∞)] at As_mble ⊢
  exact aemeasurable_of_tendsto_metrizable_ae L As_mble h_lim

/-- If the indicators of measurable sets `Aᵢ` tend pointwise almost everywhere to the indicator
of a measurable set `A` and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then
the measures of `Aᵢ` tend to the measure of `A`. -/
lemma tendsto_measure_of_ae_tendsto_indicator (μ : Measure α) (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (fun _ ↦ (1 : ℝ≥0∞)))
          (eventually_of_forall ?_) ?_ ?_ h_lim
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    exact eventually_of_forall (fun x ↦ indicator_le_indicator_of_subset hi (by simp) x)
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas

--#find_home tendsto_measure_of_tendsto_indicator'
-- Gives: `Mathlib.MeasureTheory.Integral.Lebesgue`.

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise
almost everywhere to the indicator of a measurable set `A`, then the measures `μ Aᵢ` tend to
the measure `μ A`. -/
lemma tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure [IsCountablyGenerated L]
    (μ : Measure α) [IsFiniteMeasure μ] (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) :=
  tendsto_measure_of_ae_tendsto_indicator L μ A_mble As_mble MeasurableSet.univ
    (measure_ne_top μ univ) (eventually_of_forall (fun i ↦ subset_univ (As i))) h_lim

/-- If the indicators of measurable sets `Aᵢ` tend pointwise to the indicator of a set `A`
and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then the measures of `Aᵢ`
tend to the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator [NeBot L] (μ : Measure α)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator L μ ?_ As_mble B_mble B_finmeas As_le_B
  · apply eventually_of_forall
    simpa only [tendsto_pi_nhds] using h_lim
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise to
the indicator of a set `A`, then the measures `μ Aᵢ` tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure [NeBot L]
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L μ ?_ As_mble
  · apply eventually_of_forall
    simpa only [tendsto_pi_nhds] using h_lim
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim

end TendstoMeasureOfTendstoIndicator
