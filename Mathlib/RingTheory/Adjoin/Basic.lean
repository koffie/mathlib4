/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module ring_theory.adjoin.basic
! leanprover-community/mathlib commit a35ddf20601f85f78cd57e7f5b09ed528d71b7af
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Finsupp

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of subalgebras of an R-algebra generated
by a set of elements. A basic interface for `adjoin` is set up.

## Tags

adjoin, algebra

-/


universe u v w

open Pointwise

open Submodule Subsemiring

variable {R : Type u} {A : Type v} {B : Type w}

namespace Algebra

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B]

variable [Algebra R A] [Algebra R B] {s t : Set A}

theorem subset_adjoin : s ⊆ adjoin R s :=
  Algebra.gc.le_u_l s
#align algebra.subset_adjoin Algebra.subset_adjoin

theorem adjoin_le {S : Subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
  Algebra.gc.l_le H
#align algebra.adjoin_le Algebra.adjoin_le

theorem adjoin_eq_sInf : adjoin R s = sInf { p : Subalgebra R A | s ⊆ p } :=
  le_antisymm (le_sInf fun _ h => adjoin_le h) (sInf_le subset_adjoin)
#align algebra.adjoin_eq_Inf Algebra.adjoin_eq_sInf

theorem adjoin_le_iff {S : Subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S :=
  Algebra.gc _ _
#align algebra.adjoin_le_iff Algebra.adjoin_le_iff

theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  Algebra.gc.monotone_l H
#align algebra.adjoin_mono Algebra.adjoin_mono

theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ adjoin R s) : adjoin R s = S :=
  le_antisymm (adjoin_le h₁) h₂
#align algebra.adjoin_eq_of_le Algebra.adjoin_eq_of_le

theorem adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S :=
  adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin
#align algebra.adjoin_eq Algebra.adjoin_eq

theorem adjoin_iUnion {α : Type _} (s : α → Set A) :
    adjoin R (Set.iUnion s) = ⨆ i : α, adjoin R (s i) :=
  (@Algebra.gc R A _ _ _).l_iSup
#align algebra.adjoin_Union Algebra.adjoin_iUnion

theorem adjoin_attach_biUnion [DecidableEq A] {α : Type _} {s : Finset α} (f : s → Finset A) :
    adjoin R (s.attach.biUnion f : Set A) = ⨆ x, adjoin R (f x) := by simp [adjoin_iUnion]
#align algebra.adjoin_attach_bUnion Algebra.adjoin_attach_biUnion

@[elab_as_elim]
theorem adjoin_induction {p : A → Prop} {x : A} (h : x ∈ adjoin R s) (Hs : ∀ x ∈ s, p x)
    (Halg : ∀ r, p (algebraMap R A r)) (Hadd : ∀ x y, p x → p y → p (x + y))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  let S : Subalgebra R A :=
    { carrier := p
      mul_mem' := Hmul _ _
      add_mem' := Hadd _ _
      algebraMap_mem' := Halg }
  adjoin_le (show s ≤ S from Hs) h
#align algebra.adjoin_induction Algebra.adjoin_induction

/-- Induction principle for the algebra generated by a set `s`: show that `p x y` holds for any
`x y ∈ adjoin R s` given that that it holds for `x y ∈ s` and that it satisfies a number of
natural properties. -/
@[elab_as_elim]
theorem adjoin_induction₂ {p : A → A → Prop} {a b : A} (ha : a ∈ adjoin R s) (hb : b ∈ adjoin R s)
    (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (Halg : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂))
    (Halg_left : ∀ (r), ∀ x ∈ s, p (algebraMap R A r) x)
    (Halg_right : ∀ (r), ∀ x ∈ s, p x (algebraMap R A r))
    (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p a b := by
  refine' adjoin_induction hb _ (fun r => _) (Hadd_right a) (Hmul_right a)
  · exact adjoin_induction ha Hs Halg_left
      (fun x y Hx Hy z hz => Hadd_left x y z (Hx z hz) (Hy z hz))
      fun x y Hx Hy z hz => Hmul_left x y z (Hx z hz) (Hy z hz)
  · exact adjoin_induction ha (Halg_right r) (fun r' => Halg r' r)
      (fun x y => Hadd_left x y ((algebraMap R A) r))
      fun x y => Hmul_left x y ((algebraMap R A) r)
#align algebra.adjoin_induction₂ Algebra.adjoin_induction₂

/-- The difference with `Algebra.adjoin_induction` is that this acts on the subtype. -/
@[elab_as_elim]
theorem adjoin_induction' {p : adjoin R s → Prop} (Hs : ∀ (x) (h : x ∈ s), p ⟨x, subset_adjoin h⟩)
    (Halg : ∀ r, p (algebraMap R _ r)) (Hadd : ∀ x y, p x → p y → p (x + y))
    (Hmul : ∀ x y, p x → p y → p (x * y)) (x : adjoin R s) : p x :=
  Subtype.recOn x fun x hx => by
    refine' Exists.elim _ fun (hx : x ∈ adjoin R s) (hc : p ⟨x, hx⟩) => hc
    exact adjoin_induction hx (fun x hx => ⟨subset_adjoin hx, Hs x hx⟩)
      (fun r => ⟨Subalgebra.algebraMap_mem _ r, Halg r⟩)
      (fun x y hx hy =>
        Exists.elim hx fun hx' hx =>
          Exists.elim hy fun hy' hy => ⟨Subalgebra.add_mem _ hx' hy', Hadd _ _ hx hy⟩)
      fun x y hx hy =>
        Exists.elim hx fun hx' hx =>
          Exists.elim hy fun hy' hy => ⟨Subalgebra.mul_mem _ hx' hy', Hmul _ _ hx hy⟩
#align algebra.adjoin_induction' Algebra.adjoin_induction'

@[simp]
theorem adjoin_adjoin_coe_preimage {s : Set A} : adjoin R (((↑) : adjoin R s → A) ⁻¹' s) = ⊤ := by
  refine'
    eq_top_iff.2 fun x =>
      -- porting note: Lean could no longer infer the motive
      adjoin_induction' (p := fun y => y ∈ adjoin R (((↑) : adjoin R s → A) ⁻¹' s))
      (fun a ha => _) (fun r => _) (fun _ _ => _) (fun _ _ => _) x
  · exact subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _
#align algebra.adjoin_adjoin_coe_preimage Algebra.adjoin_adjoin_coe_preimage

theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s ⊔ adjoin R t :=
  (Algebra.gc : GaloisConnection _ ((↑) : Subalgebra R A → Set A)).l_sup
#align algebra.adjoin_union Algebra.adjoin_union

variable (R A)

@[simp]
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥ by
    apply GaloisConnection.l_bot
    exact Algebra.gc
#align algebra.adjoin_empty Algebra.adjoin_empty

@[simp]
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ :=
  eq_top_iff.2 fun _x => subset_adjoin <| Set.mem_univ _
#align algebra.adjoin_univ Algebra.adjoin_univ

variable {A} (s)

theorem adjoin_eq_span : Subalgebra.toSubmodule (adjoin R s) = span R (Submonoid.closure s) := by
  apply le_antisymm
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction' L with hd tl ih
    · exact zero_mem _
    rw [List.forall_mem_cons] at HL
    rw [List.map_cons, List.sum_cons]
    refine' Submodule.add_mem _ _ (ih HL.2)
    replace HL := HL.1
    clear ih tl
    suffices ∃ (z r : _) (_hr : r ∈ Submonoid.closure s), z • r = List.prod hd by
      rcases this with ⟨z, r, hr, hzr⟩
      rw [← hzr]
      exact smul_mem _ _ (subset_span hr)
    induction' hd with hd tl ih
    · exact ⟨1, 1, (Submonoid.closure s).one_mem', one_smul _ _⟩
    rw [List.forall_mem_cons] at HL
    rcases ih HL.2 with ⟨z, r, hr, hzr⟩
    rw [List.prod_cons, ← hzr]
    rcases HL.1 with (⟨hd, rfl⟩ | hs)
    · refine' ⟨hd * z, r, hr, _⟩
      rw [Algebra.smul_def, Algebra.smul_def, (algebraMap _ _).map_mul, _root_.mul_assoc]
    · exact
        ⟨z, hd * r, Submonoid.mul_mem _ (Submonoid.subset_closure hs) hr,
          (mul_smul_comm _ _ _).symm⟩
  refine' span_le.2 _
  change Submonoid.closure s ≤ (adjoin R s).toSubsemiring.toSubmonoid
  exact Submonoid.closure_le.2 subset_adjoin
#align algebra.adjoin_eq_span Algebra.adjoin_eq_span

theorem span_le_adjoin (s : Set A) : span R s ≤ Subalgebra.toSubmodule (adjoin R s) :=
  span_le.mpr subset_adjoin
#align algebra.span_le_adjoin Algebra.span_le_adjoin

theorem adjoin_toSubmodule_le {s : Set A} {t : Submodule R A} :
    Subalgebra.toSubmodule (adjoin R s) ≤ t ↔ ↑(Submonoid.closure s) ⊆ (t : Set A) := by
  rw [adjoin_eq_span, span_le]
#align algebra.adjoin_to_submodule_le Algebra.adjoin_toSubmodule_le

theorem adjoin_eq_span_of_subset {s : Set A} (hs : ↑(Submonoid.closure s) ⊆ (span R s : Set A)) :
    Subalgebra.toSubmodule (adjoin R s) = span R s :=
  le_antisymm ((adjoin_toSubmodule_le R).mpr hs) (span_le_adjoin R s)
#align algebra.adjoin_eq_span_of_subset Algebra.adjoin_eq_span_of_subset

@[simp]
theorem adjoin_span {s : Set A} : adjoin R (Submodule.span R s : Set A) = adjoin R s :=
  le_antisymm (adjoin_le (span_le_adjoin _ _)) (adjoin_mono Submodule.subset_span)
#align algebra.adjoin_span Algebra.adjoin_span

theorem adjoin_image (f : A →ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R s).map f :=
  le_antisymm (adjoin_le <| Set.image_subset _ subset_adjoin) <|
    Subalgebra.map_le.2 <| adjoin_le <| Set.image_subset_iff.1 <| by
      -- porting note: I don't understand how this worked in Lean 3 with just `subset_adjoin`
      simp only [Set.image_id', coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        Subalgebra.coe_comap]
      exact fun x hx => subset_adjoin ⟨x, hx, rfl⟩
#align algebra.adjoin_image Algebra.adjoin_image

@[simp]
theorem adjoin_insert_adjoin (x : A) : adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s) :=
  le_antisymm
    (adjoin_le
      (Set.insert_subset_iff.mpr
        ⟨subset_adjoin (Set.mem_insert _ _), adjoin_mono (Set.subset_insert _ _)⟩))
    (Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin))
#align algebra.adjoin_insert_adjoin Algebra.adjoin_insert_adjoin

theorem adjoin_prod_le (s : Set A) (t : Set B) :
    adjoin R (s ×ˢ t) ≤ (adjoin R s).prod (adjoin R t) :=
  adjoin_le <| Set.prod_mono subset_adjoin subset_adjoin
#align algebra.adjoin_prod_le Algebra.adjoin_prod_le

theorem mem_adjoin_of_map_mul {s} {x : A} {f : A →ₗ[R] B} (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
    (h : x ∈ adjoin R s) : f x ∈ adjoin R (f '' (s ∪ {1})) := by
  refine'
    @adjoin_induction R A _ _ _ _ (fun a => f a ∈ adjoin R (f '' (s ∪ {1}))) x h
      (fun a ha => subset_adjoin ⟨a, ⟨Set.subset_union_left _ _ ha, rfl⟩⟩) (fun r => _)
      (fun y z hy hz => by simpa [hy, hz] using Subalgebra.add_mem _ hy hz) fun y z hy hz => by
      simpa [hy, hz, hf y z] using Subalgebra.mul_mem _ hy hz
  have : f 1 ∈ adjoin R (f '' (s ∪ {1})) :=
    subset_adjoin ⟨1, ⟨Set.subset_union_right _ _ <| Set.mem_singleton 1, rfl⟩⟩
  convert Subalgebra.smul_mem (adjoin R (f '' (s ∪ {1}))) this r
  rw [algebraMap_eq_smul_one]
  exact f.map_smul _ _
#align algebra.mem_adjoin_of_map_mul Algebra.mem_adjoin_of_map_mul

theorem adjoin_inl_union_inr_eq_prod (s) (t) :
    adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1})) =
      (adjoin R s).prod (adjoin R t) := by
  apply le_antisymm
  · simp only [adjoin_le_iff, Set.insert_subset_iff, Subalgebra.zero_mem, Subalgebra.one_mem,
      subset_adjoin,-- the rest comes from `squeeze_simp`
      Set.union_subset_iff,
      LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_self_iff, Set.union_singleton,
      Subalgebra.coe_prod]
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}))
    have Ha : (a, (0 : B)) ∈ adjoin R (LinearMap.inl R A B '' (s ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) ∈ adjoin R (LinearMap.inr R A B '' (t ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) ∈ P := adjoin_mono (Set.subset_union_left _ _) Ha
    replace Hb : ((0 : A), b) ∈ P := adjoin_mono (Set.subset_union_right _ _) Hb
    simpa using Subalgebra.add_mem _ Ha Hb
#align algebra.adjoin_inl_union_inr_eq_prod Algebra.adjoin_inl_union_inr_eq_prod

/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a commutative
semiring.  -/
def adjoinCommSemiringOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemiring (adjoin R s) :=
  { (adjoin R s).toSemiring with
    mul_comm := fun x y => by
      ext
      simp only [Subalgebra.coe_mul]
      exact adjoin_induction₂ x.prop y.prop hcomm (fun _ _ => by rw [commutes])
        (fun r x _hx => commutes r x) (fun r x _hx => (commutes r x).symm)
        (fun _ _ _ h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
        (fun _ _ _ h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
        (fun x₁ x₂ y₁ h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc y₁, ← h₁, mul_assoc x₁])
        fun x₁ x₂ y₁ h₁ h₂ => by rw [mul_assoc x₂, ← h₂, ← mul_assoc x₂, ← h₁, ← mul_assoc] }
#align algebra.adjoin_comm_semiring_of_comm Algebra.adjoinCommSemiringOfComm

theorem adjoin_singleton_one : adjoin R ({1} : Set A) = ⊥ :=
  eq_bot_iff.2 <| adjoin_le <| Set.singleton_subset_iff.2 <| SetLike.mem_coe.2 <| one_mem _
#align algebra.adjoin_singleton_one Algebra.adjoin_singleton_one

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)
#align algebra.self_mem_adjoin_singleton Algebra.self_mem_adjoin_singleton

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A]

variable [Algebra R A] {s t : Set A}

variable (R s t)

theorem adjoin_union_eq_adjoin_adjoin :
    adjoin R (s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R :=
  le_antisymm
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r, rfl⟩)
        (Set.union_subset_union_left _ fun _x hxs => ⟨⟨_, subset_adjoin hxs⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono (Set.subset_union_left _ _) x.2)
        (Set.Subset.trans (Set.subset_union_right _ _) subset_adjoin))
#align algebra.adjoin_union_eq_adjoin_adjoin Algebra.adjoin_union_eq_adjoin_adjoin

theorem adjoin_union_coe_submodule :
    Subalgebra.toSubmodule (adjoin R (s ∪ t)) =
      Subalgebra.toSubmodule (adjoin R s) * Subalgebra.toSubmodule (adjoin R t) := by
  rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span]
  congr 1 with z; simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]
#align algebra.adjoin_union_coe_submodule Algebra.adjoin_union_coe_submodule

theorem adjoin_adjoin_of_tower [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (s : Set B) : adjoin A (adjoin R s : Set B) = adjoin A s := by
  apply le_antisymm (adjoin_le _)
  · exact adjoin_mono subset_adjoin
  · change adjoin R s ≤ (adjoin A s).restrictScalars R
    refine' adjoin_le _
    -- porting note: unclear why this was broken
    have : (Subalgebra.restrictScalars R (adjoin A s) : Set B) = adjoin A s := rfl
    rw [this]
    exact subset_adjoin
#align algebra.adjoin_adjoin_of_tower Algebra.adjoin_adjoin_of_tower

variable {R}

theorem pow_smul_mem_of_smul_subset_of_mem_adjoin [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (r : A) (s : Set B) (B' : Subalgebra R B) (hs : r • s ⊆ B') {x : B}
    (hx : x ∈ adjoin R s) (hr : algebraMap A B r ∈ B') : ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ B' := by
  -- porting note: use `replace` because we don't have `change ... at` yet
  replace hx : x ∈ Subalgebra.toSubmodule (adjoin R s) := hx
  rw [adjoin_eq_span, Finsupp.mem_span_iff_total] at hx
  rcases hx with ⟨l, rfl : (l.sum fun (i : Submonoid.closure s) (c : R) => c • (i : B)) = x⟩
  choose n₁ n₂ using fun x : Submonoid.closure s => Submonoid.pow_smul_mem_closure_smul r s x.prop
  use l.support.sup n₁
  intro n hn
  rw [Finsupp.smul_sum]
  refine' B'.toSubmodule.sum_mem _
  intro a ha
  have : n ≥ n₁ a := le_trans (Finset.le_sup ha) hn
  dsimp only
  rw [← tsub_add_cancel_of_le this, pow_add, ← smul_smul, ←
    IsScalarTower.algebraMap_smul A (l a) (a : B), smul_smul (r ^ n₁ a), mul_comm, ← smul_smul,
    smul_def, map_pow, IsScalarTower.algebraMap_smul]
  apply Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) _
  refine' Subalgebra.smul_mem _ _ _
  change _ ∈ B'.toSubmonoid
  rw [← Submonoid.closure_eq B'.toSubmonoid]
  apply Submonoid.closure_mono hs (n₂ a)
#align algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin

theorem pow_smul_mem_adjoin_smul (r : R) (s : Set A) {x : A} (hx : x ∈ adjoin R s) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ adjoin R (r • s) :=
  pow_smul_mem_of_smul_subset_of_mem_adjoin r s _ subset_adjoin hx (Subalgebra.algebraMap_mem _ _)
#align algebra.pow_smul_mem_adjoin_smul Algebra.pow_smul_mem_adjoin_smul

end CommSemiring

section Ring

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_int (s : Set R) : adjoin ℤ s = subalgebraOfSubring (Subring.closure s) :=
  le_antisymm (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s ≤ (adjoin ℤ s).toSubring)
#align algebra.adjoin_int Algebra.adjoin_int

theorem mem_adjoin_iff {s : Set A} {x : A} :
    x ∈ adjoin R s ↔ x ∈ Subring.closure (Set.range (algebraMap R A) ∪ s) :=
  ⟨fun hx =>
    Subsemiring.closure_induction hx Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ => Subring.add_mem _) fun _ _ => Subring.mul_mem _,
    suffices Subring.closure (Set.range (algebraMap R A) ∪ s) ≤ (adjoin R s).toSubring
      from (show (_ : Set A) ⊆ _ from this) (a := x)
    -- porting note: Lean doesn't seem to recognize the defeq between the order on subobjects and
    -- subsets of their coercions to sets as easily as in Lean 3
    Subring.closure_le.2 Subsemiring.subset_closure⟩
#align algebra.mem_adjoin_iff Algebra.mem_adjoin_iff

theorem adjoin_eq_ring_closure (s : Set A) :
    (adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) ∪ s) :=
  Subring.ext fun _x => mem_adjoin_iff
#align algebra.adjoin_eq_ring_closure Algebra.adjoin_eq_ring_closure

variable (R)

/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a commutative
ring.  -/
def adjoinCommRingOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommRing (adjoin R s) :=
  { (adjoin R s).toRing, adjoinCommSemiringOfComm R hcomm with }
#align algebra.adjoin_comm_ring_of_comm Algebra.adjoinCommRingOfComm

end Ring

end Algebra

open Algebra Subalgebra

namespace AlgHom

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem map_adjoin (φ : A →ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ '' s) :=
  (adjoin_image _ _ _).symm
#align alg_hom.map_adjoin AlgHom.map_adjoin

theorem adjoin_le_equalizer (φ₁ φ₂ : A →ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂) :
    adjoin R s ≤ φ₁.equalizer φ₂ :=
  adjoin_le h
#align alg_hom.adjoin_le_equalizer AlgHom.adjoin_le_equalizer

theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂ : A →ₐ[R] B⦄
    (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂ :=
  ext fun _x => adjoin_le_equalizer φ₁ φ₂ hs <| h.symm ▸ trivial
#align alg_hom.ext_of_adjoin_eq_top AlgHom.ext_of_adjoin_eq_top

end AlgHom
