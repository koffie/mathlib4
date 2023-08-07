/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.RingTheory.RootsOfUnity.Basic

#align_import number_theory.number_field.units from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# Units of a number field
We prove results about the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K`.

## Main results
* `isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if `|norm ℚ x| = 1`

## Tags
number field, units
 -/

-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

open scoped NumberField

noncomputable section

open NumberField Units

section Rat

theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl
#align rat.ring_of_integers.is_unit_iff Rat.RingOfIntegers.isUnit_iff

end Rat

variable (K : Type _) [Field K]

section IsUnit

attribute [local instance] NumberField.ringOfIntegersAlgebra

variable {K}

theorem isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]
#align is_unit_iff_norm isUnit_iff_norm

end IsUnit

namespace NumberField.Units

section coe

theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ → K) :=
  fun _ _ h => by rwa [SetLike.coe_eq_coe, Units.eq_iff] at h

variable {K}

 theorem coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : (x ^ n : K) = (x : K) ^ n := by
   rw [← SubmonoidClass.coe_pow, ← val_pow_eq_pow_val]

 theorem coe_zpow (x : (𝓞 K)ˣ) (n : ℤ) : (x ^ n : K) = (x : K) ^ n := by
   change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
   exact map_zpow _ x n

 theorem coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl

 theorem coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) ≠ 0 :=
   Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

end coe

open NumberField.InfinitePlace

section torsion

/-- The torsion subgroup of the group of units. -/
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

theorem mem_torsion {x : (𝓞 K)ˣ} [NumberField K] :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, h_pos, h_eq⟩ φ => ?_, fun h => ?_⟩
  · refine norm_map_one_of_pow_eq_one φ.toMonoidHom (k := ⟨n, h_pos⟩) ?_
    rw [PNat.mk_coe, ← coe_pow, h_eq, coe_one]
  · obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.prop h
    exact ⟨n, hn, by ext; rwa [coe_pow, coe_one]⟩

instance : Nonempty (torsion K) := ⟨1⟩

/-- The torsion subgroup is finite. -/
instance [NumberField K] : Fintype (torsion K) := by
  refine @Fintype.ofFinite _ (Set.finite_coe_iff.mpr ?_)
  refine Set.Finite.of_finite_image ?_ ((coe_injective K).injOn _)
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

/-- The torsion subgroup is cylic. -/
instance [NumberField K] : IsCyclic (torsion K) := subgroup_units_cyclic _

/-- The order of the torsion subgroup as positive integer. -/
def torsion_order [NumberField K] : ℕ+ := ⟨Fintype.card (torsion K), Fintype.card_pos⟩

/-- If `k` does not divide `torsion_order` then there are no nontrivial roots of unity of
  order dividing `k`. -/
theorem rootsOfUnity_eq_one [NumberField K] {k : ℕ+} (hc : Nat.coprime k (torsion_order K)) :
    ζ ∈ rootsOfUnity k (𝓞 K) ↔ ζ = 1 := by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ ∈ torsion K := by
      rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, k.prop, h⟩
    rw [orderOf_submonoid (⟨ζ, hζ⟩ : torsion K)]
    exact orderOf_dvd_card_univ

/-- The group of roots of unity of order dividing `torsion_order` is equal to the torsion
group. -/
theorem rootsOfUnity_eq_torsion [NumberField K] :
    rootsOfUnity (torsion_order K) (𝓞 K) = torsion K := by
  ext ζ
  rw [torsion, mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨↑(torsion_order K), (torsion_order K).prop, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one (torsion K) _ ⟨ζ, h⟩ _)

end torsion

namespace dirichlet
-- This section is devoted to the proof of Dirichlet's unit theorem
-- We define a group morphism from `(𝓞 K)ˣ` to `{w : InfinitePlace K // w ≠ w₀} → ℝ` where `w₀`
-- is a distinguished (arbitrary) infinite place, prove that its kernel is the torsion subgroup
-- (see `log_embedding_eq_zero_iff`) and that its image, called `unit_lattice`, is a full
-- `ℤ`-lattice. It follows that is a free `ℤ`-module (see `unit_lattice_moduleFree `) of
-- rank `card (InfinitePlaces K) - 1` (see `unit_lattice_rank`).
-- To prove that the `unit_lattice` is a full `ℤ`-lattice, we need to prove that it is discrete
-- (see `unit_lattice_inter_ball_finite`) and that it spans the full space over `ℝ`
-- (see ` unit_lattice_span_eq_top`); this is the main part of the proof, see the section
-- `span_top` below for more details.

open scoped Classical BigOperators

variable [NumberField K]

variable {K}

/-- The distinguished infinite place. -/
def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some

variable (K)

/-- The logarithmic embedding of the units (seen as an `Additive` group). -/
def log_embedding : Additive ((𝓞 K)ˣ) →+ ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
{ toFun := fun x w => mult w.val * Real.log (w.val (Additive.toMul x))
  map_zero' := by simp; rfl
  map_add' := by
    intro _ _
    simp [ne_eq, toMul_add, map_mul, map_eq_zero, coe_ne_zero, Real.log_mul, mul_add]
    rfl }

variable {K}

@[simp]
theorem log_embedding_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w ≠ w₀}) :
    (log_embedding K x) w = mult w.val * Real.log (w.val x) := rfl

theorem log_embedding_sum_component (x : (𝓞 K)ˣ) :
    ∑ w, log_embedding K x w = - mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K)) := by
  have h := congrArg Real.log (prod_eq_abs_norm (x : K))
  rw [show |(Algebra.norm ℚ) (x : K)| = 1 from isUnit_iff_norm.mp x.isUnit, Rat.cast_one,
    Real.log_one, Real.log_prod] at h
  · simp_rw [Real.log_pow] at h
    rw [← Finset.insert_erase (Finset.mem_univ w₀), Finset.sum_insert (Finset.not_mem_erase w₀
      Finset.univ), add_comm, add_eq_zero_iff_eq_neg] at h
    convert h using 1
    · refine (Finset.sum_subtype _ (fun w => ?_) (fun w => (mult w) * (Real.log (w (x : K))))).symm
      exact ⟨Finset.ne_of_mem_erase, fun h => Finset.mem_erase_of_ne_of_mem h (Finset.mem_univ w)⟩
    · norm_num
  · exact fun w _ => pow_ne_zero _ (AbsoluteValue.ne_zero _ (coe_ne_zero x))

theorem mult_log_place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} :
    mult w * Real.log (w x) = 0 ↔ w x = 1 := by
  rw [mul_eq_zero, or_iff_right, Real.log_eq_zero, or_iff_right, or_iff_left]
  · have : 0 ≤ w x := map_nonneg _ _
    linarith
  · simp only [ne_eq, map_eq_zero, coe_ne_zero x]
  · refine (ne_of_gt ?_)
    rw [mult]; split_ifs <;> norm_num

theorem log_embedding_eq_zero_iff (x : (𝓞 K)ˣ) :
    log_embedding K x = 0 ↔ x ∈ torsion K := by
  rw [mem_torsion]
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · by_cases hw : w = w₀
    · suffices - mult w₀ * Real.log (w₀ (x : K)) = 0 by
        rw [neg_mul, neg_eq_zero, ← hw] at this
        exact mult_log_place_eq_zero.mp this
      rw [← log_embedding_sum_component, Finset.sum_eq_zero]
      exact fun w _ => congrFun h w
    · exact mult_log_place_eq_zero.mp (congrFun h ⟨w, hw⟩)
  · ext w
    rw [log_embedding_component, h w.val, Real.log_one, mul_zero, Pi.zero_apply]

theorem log_embedding_component_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖log_embedding K x‖ ≤ r)
    (w : {w : InfinitePlace K // w ≠ w₀}) : |log_embedding K x w| ≤ r := by
  lift r to NNReal using hr
  simp_rw [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe] at h
  exact h w (Finset.mem_univ _)

theorem log_le_of_log_embedding_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖log_embedding K x‖ ≤ r)
    (w : InfinitePlace K) : |Real.log (w x)| ≤ (Fintype.card (InfinitePlace K)) * r := by
  have tool : ∀ x : ℝ, 0 ≤ x → x ≤ mult w * x := fun x hx => by
      nth_rw 1 [← one_mul x]
      refine mul_le_mul ?_ le_rfl hx ?_
      all_goals { rw [mult]; split_ifs <;> norm_num }
  by_cases hw : w = w₀
  · have hyp := congrArg (‖·‖) (log_embedding_sum_component x).symm
    replace hyp := (le_of_eq hyp).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · rw [← hw]
      exact tool _ (abs_nonneg _)
    · refine (Finset.sum_le_card_nsmul Finset.univ _  _
        (fun w _ => log_embedding_component_le hr h w)).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul ?_ le_rfl hr (Fintype.card (InfinitePlace K)).cast_nonneg
      simp [Finset.card_univ]
  · have hyp := log_embedding_component_le hr h ⟨w, hw⟩
    rw [log_embedding_component, abs_mul, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · exact tool _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul (Nat.one_le_cast.mpr Fintype.card_pos) (le_of_eq rfl) hr (Nat.cast_nonneg _)

variable (K)

/-- The lattice formed by the image of the logarithmic embedding. -/
noncomputable def unit_lattice : AddSubgroup ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
  AddSubgroup.map (log_embedding K) ⊤

theorem unit_lattice_inter_ball_finite (r : ℝ) :
    ((unit_lattice K : Set ({ w : InfinitePlace K // w ≠ w₀} → ℝ)) ∩
      Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_le r 0
  · convert Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices Set.Finite {x : (𝓞 K)ˣ | IsIntegral ℤ (x : K) ∧
        ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ Real.exp ((Fintype.card (InfinitePlace K)) * r)} by
      refine (Set.Finite.image (log_embedding K) this).subset ?_
      rintro _ ⟨⟨x, ⟨_, rfl⟩⟩, hx⟩
      refine ⟨x, ⟨x.val.prop, (le_iff_le _ _).mp (fun w => (Real.log_le_iff_le_exp ?_).mp ?_)⟩, rfl⟩
      · exact pos_iff.mpr (coe_ne_zero x)
      · rw [mem_closedBall_zero_iff] at hx
        exact (le_abs_self _).trans (log_le_of_log_embedding_le hr hx w)
    refine Set.Finite.of_finite_image ?_ ((coe_injective K).injOn _)
    refine (Embeddings.finite_of_norm_le K ℂ
        (Real.exp ((Fintype.card (InfinitePlace K)) * r))).subset ?_
    rintro _ ⟨x, ⟨⟨h_int, h_le⟩, rfl⟩⟩
    exact ⟨h_int, h_le⟩

section span_top
-- To prove that the span over `ℝ` of the `unit_lattice` is equal to the full space, we construct
-- for each infinite place `w₁ ≠ w₀` an unit `u_w₁` of `K` such that, for all infinite place
-- `w` such that `w ≠ w₁`, we have `Real.log w (u_w₁) < 0` (and thus `Real.log w₁ (u_w₁) > 0`).
-- It follows then from a determinant computation (using `Matrix.det_ne_zero_of_neg`) that the
-- image by `log_embedding` of these units is a `ℝ`-linearly independent family.
-- The unit `u_w₁` is obtained by construction a sequence `seq n` of nonzero algebraic integers
-- that is strictly decreasing at infinite places distinct from `w₁` and of norm `≤ B`. Since
-- there are finitely many ideals of norm `≤ B`, there exists two terms in the sequence defining
-- the same ideal and their quotient is the desired unit `u_w₁` (see `exists_unit`).

open NumberField.mixedEmbedding NNReal

variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowski_bound K < (constant_factor K) * B)

/-- This result shows that there always exists a next term of the sequence. -/
theorem seq.next {x : 𝓞 K} (hx : x ≠ 0) :
    ∃ y : 𝓞 K, y ≠ 0 ∧ (∀ w, w ≠ w₁ → w y < w x) ∧ |Algebra.norm ℚ (y : K)| ≤ B := by
  let f : InfinitePlace K → ℝ≥0 :=
    fun w => ⟨(w x) / 2, div_nonneg (AbsoluteValue.nonneg _ _) (by norm_num)⟩
  suffices ∀ w, w ≠ w₁ → f w ≠ 0 by
    obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
    obtain ⟨y, h_ynz, h_yle⟩ := exists_ne_zero_mem_ringOfIntegers_lt (f := g)
      (by rw [convex_body_volume]; convert hB; exact congrArg ((↑): NNReal → ENNReal) h_gprod)
    refine ⟨y, h_ynz, fun w hw => (h_geqf w hw ▸ h_yle w).trans ?_, ?_⟩
    · rw [← Rat.cast_le (K := ℝ), Rat.cast_coe_nat]
      calc
        _ = ∏ w : InfinitePlace K, w y ^ mult w       := (prod_eq_abs_norm (y : K)).symm
        _ ≤ ∏ w : InfinitePlace K, (g w : ℝ) ^ mult w := ?_
        _ ≤ (B : ℝ)                                   := ?_
      · refine Finset.prod_le_prod ?_ ?_
        exact fun _ _ => pow_nonneg (by positivity) _
        exact fun w _ => pow_le_pow_of_le_left (by positivity) (le_of_lt (h_yle w)) (mult w)
      · simp_rw [← NNReal.coe_pow, ← NNReal.coe_prod]
        exact le_of_eq (congrArg toReal h_gprod)
    · refine div_lt_self ?_ (by norm_num)
      simp only [pos_iff, ne_eq, ZeroMemClass.coe_eq_zero, hx]
  intro _ _
  rw [ne_eq, Nonneg.mk_eq_zero, div_eq_zero_iff, map_eq_zero, not_or, ZeroMemClass.coe_eq_zero]
  exact ⟨hx, by norm_num⟩

/-- An infinite sequence of nonzero algebraic integers of `K` satisfying the following properties:
• `seq n` is nonzero;
• for `w : InfinitePlace K`, `w ≠ w₁ → w (seq n+1) < w (seq n)`;
• `∣norm (seq n)∣ ≤ B`. -/
def seq : ℕ → { x : 𝓞 K // x ≠ 0 }
  | 0 => ⟨1, by norm_num⟩
  | n + 1 =>
    ⟨(seq.next K w₁ hB (seq n).prop).choose, (seq.next K w₁ hB (seq n).prop).choose_spec.1⟩

/-- The terms of the sequence are nonzero. -/
theorem seq.ne_zero (n : ℕ) : (seq K w₁ hB n : K) ≠ 0 := by
  refine (map_ne_zero_iff (algebraMap (𝓞 K) K) ?_).mpr (seq K w₁ hB n).prop
  exact IsFractionRing.injective { x // x ∈ 𝓞 K } K

/-- The sequence is strictly decreasing at infinite places different from `w₁`. -/
theorem seq.antitone {n m : ℕ} (h : n < m) :
    ∀ w : InfinitePlace K, w ≠ w₁ → w (seq K w₁ hB m) < w (seq K w₁ hB n) := by
  induction m with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero n h
  | succ m m_ih =>
      intro w hw
      cases eq_or_lt_of_le (Nat.le_of_lt_succ h) with
      | inl hr =>
          rw [hr]
          exact (seq.next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw
      | inr hr =>
          refine lt_trans ?_ (m_ih hr w hw)
          exact (seq.next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw

/-- The terms of the sequence have bounded norms. -/
theorem seq.norm_bdd (n : ℕ) :
    1 ≤ Int.natAbs (Algebra.norm ℤ (seq K w₁ hB n : 𝓞 K)) ∧
      Int.natAbs (Algebra.norm ℤ (seq K w₁ hB n : 𝓞 K)) ≤ B := by
  cases n with
  | zero =>
      have : 1 ≤ B := by
        contrapose! hB
        simp only [Nat.lt_one_iff.mp hB, CharP.cast_eq_zero, mul_zero, zero_le]
      simp only [ne_eq, seq, _root_.map_one, Int.natAbs_one, le_refl, this, and_self]
  | succ n =>
      refine ⟨Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr ?_), ?_⟩
      · exact Algebra.norm_ne_zero_iff.mpr (seq K w₁ hB n.succ).prop
      · rw [← Nat.cast_le (α := ℚ), Int.cast_natAbs, Int.cast_abs]
        change |algebraMap ℤ ℚ _| ≤ _
        rw [← Algebra.norm_localization ℤ (Sₘ := K) (nonZeroDivisors ℤ)]
        exact (seq.next K w₁ hB (seq K w₁ hB n).prop).choose_spec.2.2

/-- Construct an unit associated to the place `w₁`. The family, for `w₁ ≠ w₀`, formed by the
image by the `log_embedding` of these units  is `ℝ`-linearly independent, see
`unit_lattice_span_eq_top`. -/
theorem exists_unit (w₁ : InfinitePlace K ) :
    ∃ u : (𝓞 K)ˣ, (∀ w : InfinitePlace K, w ≠ w₁ → Real.log (w u) < 0) := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, minkowski_bound K < (constant_factor K) * B := by
    simp_rw [mul_comm]
    refine ENNReal.exists_nat_mul_gt ?_ ?_
    exact ne_of_gt (constant_factor_pos K)
    exact ne_of_lt (minkowski_bound_lt_top K)
  rsuffices ⟨n, m, hnm, h⟩ : ∃ n m, n < m ∧
      (Ideal.span ({ (seq K w₁ hB n : 𝓞 K) }) = Ideal.span ({ (seq K w₁ hB m : 𝓞 K) }))
  · have hu := Ideal.span_singleton_eq_span_singleton.mp h
    refine ⟨hu.choose, fun w hw => Real.log_neg ?_ ?_⟩
    · simp only [pos_iff, ne_eq, ZeroMemClass.coe_eq_zero, ne_zero]
    · calc
        _ = w ((seq K w₁ hB m : K) * (seq K w₁ hB n : K)⁻¹) := ?_
        _ = w (seq K w₁ hB m) * w (seq K w₁ hB n)⁻¹         := _root_.map_mul _ _ _
        _ < 1                                               := ?_
      · rw [← congrArg ((↑) : (𝓞 K) → K) hu.choose_spec, mul_comm, Submonoid.coe_mul, ← mul_assoc,
          inv_mul_cancel (seq.ne_zero K w₁ hB n), one_mul]
      · rw [map_inv₀, mul_inv_lt_iff (pos_iff.mpr (seq.ne_zero K w₁ hB n)), mul_one]
        exact seq.antitone K w₁ hB hnm w hw
  refine Set.Finite.exists_lt_map_eq_of_forall_mem
    (t := { I : Ideal (𝓞 K) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ B })
    (fun n => ?_) ?_
  · rw [Set.mem_setOf_eq, Ideal.absNorm_span_singleton]
    exact seq.norm_bdd K w₁ hB n
  · rw [show { I : Ideal (𝓞 K) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ B } =
          (⋃ n ∈ Set.Icc 1 B, { I : Ideal (𝓞 K) | Ideal.absNorm I = n }) by ext; simp]
    exact Set.Finite.biUnion (Set.finite_Icc _ _) (fun n hn => Ideal.finite_setOf_absNorm_eq hn.1)

theorem unit_lattice_span_eq_top :
    Submodule.span ℝ (unit_lattice K : Set ({w : InfinitePlace K // w ≠ w₀} → ℝ)) = ⊤ := by
  refine le_antisymm (le_top) ?_
  -- The standard basis
  let B := Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}
  -- The family of units constructed above
  let v := fun w : { w : InfinitePlace K // w ≠ w₀ } => log_embedding K ((exists_unit K w).choose)
  -- To prove the result, it is enough to prove that the family `v` is linearly independent
  suffices B.det v ≠ 0 by
    rw [← isUnit_iff_ne_zero, ← is_basis_iff_det] at this
    rw [← this.2]
    exact Submodule.span_monotone (fun _ ⟨w, hw⟩ =>
      ⟨(exists_unit K w).choose, trivial, by rw [← hw]⟩)
  rw [Basis.det_apply]
  -- We use a specific lemma to prove that this determinant is nonzero
  refine Matrix.det_ne_zero_of_neg (fun i j hij => ?_) (fun j => ?_)
  · rw [Basis.coePiBasisFun.toMatrix_eq_transpose, Matrix.transpose_apply]
    refine mul_neg_of_pos_of_neg ?_ ((exists_unit K j).choose_spec i ?_)
    · rw [mult]; split_ifs <;> norm_num
    · exact Subtype.ext_iff_val.not.mp hij
  · simp_rw [Basis.coePiBasisFun.toMatrix_eq_transpose, Matrix.transpose_apply,
      log_embedding_sum_component]
    refine mul_pos_of_neg_of_neg ?_ ?_
    · rw [mult]; split_ifs <;> norm_num
    · exact (exists_unit K j).choose_spec _ j.prop.symm

end span_top

/-- The unit rank of the number field `K`, it is equal to `card (InfinitePlace K) - 1`. -/
def _root_.NumberField.Units.rank : ℕ := Fintype.card (InfinitePlace K) - 1

open FiniteDimensional

theorem rank_space :
    finrank ℝ ({w : InfinitePlace K // w ≠ w₀} → ℝ) = rank K := by
  simp only [finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_ofSubsingleton, rank]

theorem unit_lattice_moduleFree : Module.Free ℤ (unit_lattice K) :=
Zlattice.module_free ℝ ((unit_lattice_inter_ball_finite K)) (unit_lattice_span_eq_top K)

theorem unit_lattice_moduleFinite : Module.Finite ℤ (unit_lattice K) :=
Zlattice.module_finite ℝ ((unit_lattice_inter_ball_finite K)) (unit_lattice_span_eq_top K)

theorem unit_lattice_rank : finrank ℤ (unit_lattice K) = rank K := by
  rw [← rank_space]
  exact Zlattice.rank ℝ ((unit_lattice_inter_ball_finite K)) (unit_lattice_span_eq_top K)

end dirichlet

variable [NumberField K]

def basis_mod_torsion : Basis (Fin (rank K)) ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := by
  let f : (dirichlet.unit_lattice K) ≃ₗ[ℤ] Additive ((𝓞 K)ˣ ⧸ (torsion K)) := by
    refine AddEquiv.toIntLinearEquiv ?_
    rw [dirichlet.unit_lattice, ← AddMonoidHom.range_eq_map (dirichlet.log_embedding K)]
    refine (QuotientAddGroup.quotientKerEquivRange (dirichlet.log_embedding K)).symm.trans ?_
    refine (QuotientAddGroup.quotientAddEquivOfEq ?_).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (MonoidHom.toAdditive (QuotientGroup.mk' (torsion K))) (fun x => ?_))
    · ext
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, dirichlet.log_embedding_eq_zero_iff,
        MonoidHom.toAdditive_apply_apply, ofMul_eq_zero, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      rfl
    · refine ⟨Additive.ofMul x.out', ?_⟩
      simp only [MonoidHom.toAdditive_apply_apply, toMul_ofMul, QuotientGroup.mk'_apply,
        QuotientGroup.out_eq']
      rfl
  have : Module.Free ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) :=
      (dirichlet.unit_lattice_moduleFree K).of_equiv'  f
  have : Module.Finite ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := by
    have := dirichlet.unit_lattice_moduleFinite K
    exact Module.Finite.equiv f
  have : FiniteDimensional.finrank ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) = rank K := by
    rw [← LinearEquiv.finrank_eq f, dirichlet.unit_lattice_rank]
  refine Basis.reindex (Module.Free.chooseBasis ℤ _) (Fintype.equivOfCardEq ?_)
  rw [← FiniteDimensional.finrank_eq_card_chooseBasisIndex, this, Fintype.card_fin]

def fund_system : Fin (rank K) → (𝓞 K)ˣ :=
  fun i => Quotient.out' (Additive.toMul (basis_mod_torsion K i))

open BigOperators

theorem aux0 {x ζ : (𝓞 K)ˣ} {f : Fin (rank K) → ℤ} (hζ : ζ ∈ torsion K)
    (h : x = ζ * ∏ i, (fund_system K i) ^ (f i)) :
    f = (basis_mod_torsion K).repr (Additive.ofMul ↑x) := by
  suffices Additive.ofMul ↑x = ∑ i, (f i) • (basis_mod_torsion K i) by
    rw [← (basis_mod_torsion K).repr_sum_self f, ← this]
  calc
    Additive.ofMul ↑x = ∑ i, (f i) • Additive.ofMul ↑(fund_system K i) := by
                        rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hζ, one_mul,
                            QuotientGroup.mk_prod, ofMul_prod]; rfl
                    _ = ∑ i, (f i) • (basis_mod_torsion K i)             := by
                        simp_rw [fund_system, QuotientGroup.out_eq', ofMul_toMul]

theorem aux1 (x : (𝓞 K)ˣ) :
    x * (∏ i, (fund_system K i) ^ ((basis_mod_torsion K).repr (Additive.ofMul ↑x) i))⁻¹
      ∈ torsion K := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← ofMul_eq_zero,
    ofMul_mul, ofMul_inv]
  rw [QuotientGroup.mk_prod, ofMul_prod]
  simp_rw [QuotientGroup.mk_zpow, ofMul_zpow, fund_system, QuotientGroup.out_eq', ofMul_toMul]
  rw [add_eq_zero_iff_eq_neg, neg_neg]
  exact ((basis_mod_torsion K).sum_repr (Additive.ofMul ↑x)).symm

example (x : (𝓞 K)ˣ) : ∃! (ζ : torsion K) (e : Fin (rank K) → ℤ),
    x = ζ * ∏ i, (fund_system K i) ^ (e i) := by
  let ζ := x * (∏ i, (fund_system K i) ^ ((basis_mod_torsion K).repr (Additive.ofMul ↑x) i))⁻¹
  refine ⟨⟨ζ, aux1 K x⟩, ?_, ?_⟩
  · refine ⟨(basis_mod_torsion K).repr (Additive.ofMul ↑x), ?_, ?_⟩
    · simp only [_root_.inv_mul_cancel_right]
    · intro f hf
      exact aux0 K (aux1 K x) hf
  · rintro η ⟨f, hf, _⟩
    ext1
    dsimp only
    nth_rewrite 1 [hf]
    have := aux0 K η.prop hf
    simp_rw [this]
    rw [mul_assoc, mul_right_inv, mul_one]

end NumberField.Units
