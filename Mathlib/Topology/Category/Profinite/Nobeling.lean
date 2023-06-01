import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Topology.Category.Profinite.InjectiveMap

namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {Z : Type _}

noncomputable
def equiv (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z :=
{ toFun := comap e.invFun
  invFun := comap e.toFun
  left_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_toFun e.continuous_invFun]
    simp
  right_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_invFun e.continuous_toFun]
    simp }

@[simp]
theorem coe_comap_apply (f : X → Y) (g : LocallyConstant Y Z) (hf : Continuous f) :
    ∀ x, comap f g x = g (f x) := by
  intro x
  rw [← @Function.comp_apply _ _ _ g f x]
  rw [← coe_comap _ _ hf]

lemma comap_injective (f : X → Y) (hf: Continuous f)
    (hfs : Function.Surjective f) : Function.Injective
    ((LocallyConstant.comap f) : (LocallyConstant Y Z) → (LocallyConstant X Z)) := by
  intro a b h
  rw [LocallyConstant.ext_iff] at h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  specialize h x
  rw [coe_comap_apply _ _ hf] at h
  rw [coe_comap_apply _ _ hf] at h
  rw [← hx]
  assumption

variable {R : Type _} [Ring R] [AddCommMonoid Z] [Module R Z]

noncomputable
def comapLinear (f : X → Y) (hf : Continuous f) : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z :=
{ toFun := comap f
  map_add' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl
  map_smul' := by
    intro r s
    dsimp
    ext x
    simp
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl }

lemma comapLinear_injective (f : X → Y) (hf : Continuous f) (hfs : Function.Surjective f) :
    LinearMap.ker (comapLinear f hf : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z) = ⊥ := by
  apply LinearMap.ker_eq_bot_of_injective
  dsimp [comapLinear]
  exact comap_injective _ hf hfs

noncomputable
def equivLinear (e : X ≃ₜ Y) : LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z :=
{ toFun := (equiv e).toFun
  map_smul' := (comapLinear _ e.continuous_invFun).map_smul'
  map_add' := by -- why doesn't (comapLinear _ e.continuous_invFun).map_add' work?
    intro r s
    ext x
    dsimp [equiv]
    have hf : Continuous ↑(e.symm) := e.continuous_invFun
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl
  invFun := (equiv e).invFun
  left_inv := (equiv e).left_inv
  right_inv := (equiv e).right_inv }

end LocallyConstant

namespace List
namespace Lex

variable {α : Type u} {r : α → α → Prop}

lemma singleton_iff (a b : α) : r a b ↔ List.Lex r [a] [b] := by
  refine' ⟨List.Lex.rel,_⟩
  intro h
  by_contra h'
  cases h
  · apply not_nil_right r []
    assumption
  · apply h'
    assumption

lemma nil_le (l : List α) : List.Lex r [] l ∨ [] = l := by
  induction l with
  | nil =>
    right
    rfl
  | cons a as _ =>
    left
    apply nil

end Lex
end List

namespace NobelingProof

variable {I : Type _} [LinearOrder I] [IsWellOrder I (·<·)] (C : Set ((WithTop I) → Bool))

def BoolToZ : Bool → ℤ := (if · then 1 else 0)

variable (I)

def r : (I → Bool) → (WithTop I) → Bool := fun f i ↦ if let some a := i then f a else false

lemma r.embedding : ClosedEmbedding (r I) := by
  apply Continuous.closedEmbedding
  · apply continuous_pi
    intro i
    dsimp [r]
    cases i
    · exact continuous_const
    · exact continuous_apply _
  · intros f g hfg
    ext i
    exact congr_fun hfg i

variable {I}

def e (μ : WithTop I) : LocallyConstant {i // i ∈ C} ℤ :=
{ toFun := fun f ↦ BoolToZ (f.1 μ)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    refine' @Continuous.comp _ _ _ _ _ _ BoolToZ _ continuous_of_discreteTopology _
    refine' Continuous.comp (continuous_apply μ) _
    exact continuous_induced_dom }

def Products (I : Type _) [LinearOrder I] := {l : List I // l.Chain' (·>·)}

noncomputable
instance : LinearOrder (Products (WithTop I)) :=
  inferInstanceAs (LinearOrder {l : List (WithTop I) // l.Chain' (·>·)})

lemma ltIffLex (l m : Products (WithTop I)) : l < m ↔ List.Lex (·<·) l.val m.val := by
  cases l
  cases m
  rw [Subtype.mk_lt_mk]
  simp
  exact Iff.rfl

lemma transLex (l m k : List (WithTop I)) (hlm : List.Lex (·<·) l m) (hmk : List.Lex (·<·) m k) :
    List.Lex (·<·) l k :=
  (inferInstance : IsTrans (List (WithTop I)) (List.Lex (·<·))).trans _ _ _ hlm hmk

def Products.eval (l : Products (WithTop I)) := (l.1.map (e C)).prod

def Products.isGood (l : Products (WithTop I)) : Prop :=
  l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})

def GoodProducts := {l : Products (WithTop I) | l.isGood C}

def GoodProducts.eval (l : {l : Products (WithTop I) // l.isGood C}) :
  LocallyConstant {i // i ∈ C} ℤ := Products.eval C l.1

lemma GoodProducts.injective : Function.Injective (eval C) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  dsimp [eval] at h
  have hab : a < b ∨ a = b ∨ b < a := trichotomous_of (·<·) a b
  apply Or.elim3 hab
  · intro h'
    exfalso
    apply hb
    rw [← h]
    apply Submodule.subset_span
    use a
    exact ⟨h',rfl⟩
  · exact fun h ↦ Subtype.eq h
  · intro h'
    exfalso
    apply ha
    rw [h]
    apply Submodule.subset_span
    use b
    exact ⟨h',rfl⟩

def ModProducts := Set.range (GoodProducts.eval C)

noncomputable
def GoodProducts.equiv_modProducts : GoodProducts C ≃ ModProducts C :=
Equiv.ofInjective (eval C) (injective C)

lemma GoodProducts.equiv_toFun_eq_eval : (equiv_modProducts C).toFun =
  Set.rangeFactorization (eval C) := by rfl

lemma GoodProducts.linear_independent_iff : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : ModProducts C) ↦ p.1) := by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C), ← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_modProducts C)

def Support : Set (WithTop I) := {i : WithTop I | ∃ f ∈ C, f i}

def P (i : WithTop I) : Prop :=
∀ C, IsClosed C → Support C ⊆ {j | j < i} → LinearIndependent ℤ (GoodProducts.eval C)

def Q (i : WithTop I) : Prop :=
∀ C, IsClosed C → Support C ⊆ {j | j < i} → ⊤ ≤ Submodule.span ℤ (Set.range (GoodProducts.eval C))

variable (I)

def ord (i : WithTop I) : Ordinal := Ordinal.typein ((·<·) : WithTop I → WithTop I → Prop) i

def P' (o : Ordinal) : Prop :=
∀ C, IsClosed C → Support C ⊆ {j : WithTop I | ord I j < o} →
  LinearIndependent ℤ (GoodProducts.eval C)

def Q' (o : Ordinal) : Prop :=
∀ C, IsClosed C → Support C ⊆ {j : WithTop I | ord I j < o} →
  ⊤ ≤ Submodule.span ℤ (Set.range (GoodProducts.eval C))

lemma PsetEq (i : WithTop I) : {j : WithTop I | ord I j < ord I i} = {j : WithTop I | j < i} := by
  ext x
  dsimp [ord]
  simp only [Ordinal.typein_lt_typein]

lemma PIffP (i : WithTop I) : P i ↔ P' I (ord I i) := by
  dsimp [P, P']
  rw [PsetEq]

lemma QIffQ (i : WithTop I) : Q i ↔ Q' I (ord I i) := by
  dsimp [Q, Q']
  rw [PsetEq]

variable {I}

instance : IsWellFounded (WithTop I) (·<·) := inferInstance

instance : IsEmpty { i // i ∈ (∅ : Set (WithTop I → Bool)) } := by
  simp only [Set.mem_empty_iff_false, isEmpty_subtype, forall_const]

instance : ¬ Nontrivial (LocallyConstant { i // i ∈ (∅ : Set (WithTop I → Bool)) } ℤ) := by
  rw [nontrivial_iff]
  push_neg
  intros f g
  ext x
  exact isEmptyElim x

instance : Subsingleton (LocallyConstant { i // i ∈ (∅ : Set (WithTop I → Bool)) } ℤ) := by
  rw [subsingleton_iff]
  intros f g
  ext x
  exact isEmptyElim x

instance GoodProducts.emptyEmpty :
    IsEmpty { l // Products.isGood (∅ : Set (WithTop I → Bool)) l } := by
  rw [isEmpty_iff]
  rintro ⟨l, hl⟩
  dsimp [Products.isGood] at hl
  apply hl
  have h : Products.eval ∅ l = 0 := subsingleton_iff.mp inferInstance _ 0
  rw [h]
  exact Submodule.zero_mem _

lemma GoodProducts.linearIndependentEmpty :
    LinearIndependent ℤ (eval (∅ : Set (WithTop I → Bool))) := by
  exact linearIndependent_empty_type

noncomputable
def el (o : Ordinal) : WithTop I := if h : o < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop)
  then Ordinal.enum _ o h else ⊤

lemma zeroLTTop : 0 < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop) := by
  rw [Ordinal.pos_iff_ne_zero]
  intro h
  simp only [Ordinal.type_eq_zero_iff_isEmpty, not_isEmpty_of_nonempty] at h

noncomputable
def ezero: Products (WithTop I) := ⟨[el 0], by simp only [List.chain'_singleton]⟩

def enil : Products (WithTop I) := ⟨[], by simp only [List.chain'_nil]⟩

lemma elZeroIsBot (i : WithTop I) : el 0 ≤ i := by
  have h₁ : 0 < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop)
  · rw [Ordinal.pos_iff_ne_zero]
    intro h
    rw [Ordinal.type_eq_zero_iff_isEmpty] at h
    simp only [not_isEmpty_of_nonempty] at h
  have : el 0 = Ordinal.enum ((·<·) : WithTop I → WithTop I → Prop) 0 h₁
  · dsimp [el]
    rw [dite_eq_iff]
    left
    use h₁
  · rw [this]
    have h := Ordinal.enum_zero_le h₁ i
    simp only [not_lt] at h
    assumption

lemma leEzeroSingleton : { m : Products (WithTop I) | m < ezero} = {⟨[], List.chain'_nil⟩ } := by
  ext ⟨m, hm⟩
  refine' ⟨_,_⟩
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [ltIffLex]
    dsimp [ezero]
    intro h
    apply Subtype.eq
    dsimp
    induction m with
    | nil => rfl
    | cons i m _ =>
      simp
      by_cases hi : el 0 = i
      · rw [hi, List.Lex.cons_iff] at h
        exact List.Lex.not_nil_right _ _ h
      · have : List.Lex (·<·) [el 0] [i]
        · rw [← List.Lex.singleton_iff]
          rw [lt_iff_le_and_ne]
          exact ⟨elZeroIsBot i, hi⟩
        · have ht : List.Lex (·<·) (i :: m) [i] := transLex _ _ _ h this
          rw [List.Lex.cons_iff] at ht
          exact List.Lex.not_nil_right _ _ ht
  · simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [ltIffLex]
    dsimp [ezero]
    intro h
    cases h
    exact List.nil_lt_cons _ _

lemma leEnilEmpty : { m : Products (WithTop I) | m < enil } = ∅ := by
  ext ⟨m, hm⟩
  refine' ⟨_,(by tauto)⟩
  rintro h
  · simp at h
    rw [ltIffLex] at h
    dsimp [enil] at h
    simp only [Set.mem_empty_iff_false]
    apply List.Lex.not_nil_right _ _ h

instance {α : Type _} [TopologicalSpace α] [Inhabited α] : Nontrivial (LocallyConstant α ℤ) := by
  use 0
  use 1
  intro h
  rw [LocallyConstant.ext_iff] at h
  apply @zero_ne_one ℤ
  exact h default

lemma evalEnilNeZero : Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) enil ≠ 0 := by
  dsimp [Products.eval]
  exact one_ne_zero

lemma nilIsGood : Products.isGood ({fun _ ↦ false} : Set (WithTop I → Bool)) enil:= by
  intro h
  rw [leEnilEmpty] at h
  simp at h
  apply evalEnilNeZero h

lemma nilSpanTop :
    Submodule.span ℤ (Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) '' {enil}) = ⊤ := by
  simp only [Set.image_singleton]
  dsimp [enil, Products.eval]
  rw [eq_top_iff]
  rintro f _
  rw [Submodule.mem_span]
  intro p h₁
  simp at h₁
  have : f = (f default) • (1 : LocallyConstant _ ℤ)
  · ext x
    have hd : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
    rw [hd]
    simp
    rfl
  rw [this]
  apply Submodule.smul_mem
  exact h₁

noncomputable
instance GoodProducts.singletonUnique :
  Unique { l // Products.isGood ({fun _ ↦ false} : Set (WithTop I → Bool)) l } :=
{ default := ⟨enil, nilIsGood⟩
  uniq := by
    rintro ⟨⟨l, hl⟩, hll⟩
    dsimp [default]
    ext
    dsimp [enil]
    apply Subtype.eq
    dsimp
    have : [] < l ∨ [] = l  := List.Lex.nil_le l
    cases this
    · exfalso
      apply hll
      have he : {enil} ⊆ {m | m < ⟨l,hl⟩ }
      · simp
        dsimp [enil]
        rw [Subtype.mk_lt_mk]
        assumption
      have hpe : Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) '' {enil} ⊆
        Products.eval _ '' {m | m < ⟨l,hl⟩ } := Set.image_subset _ he
      apply Submodule.span_mono hpe
      rw [nilSpanTop]
      exact Submodule.mem_top
    · exact Eq.symm (by assumption) }

instance (α : Type _) [TopologicalSpace α] : NoZeroSMulDivisors ℤ (LocallyConstant α ℤ) := by
  constructor
  intro c f h
  by_cases hc : c = 0
  · left
    assumption
  · right
    ext x
    rw [LocallyConstant.ext_iff] at h
    apply_fun fun (y : ℤ) ↦ c * y
    · simp at h
      simp
      exact h x
    · exact mul_right_injective₀ hc

lemma GoodProducts.linearIndependentSingleton :
    LinearIndependent ℤ (eval ({fun _ ↦ false} : Set (WithTop I → Bool))) :=
  linearIndependent_unique (eval ({fun _ ↦ false} : Set (WithTop I → Bool))) evalEnilNeZero

noncomputable
def ProjOrd (o : Ordinal) : (WithTop I → Bool) → (WithTop I → Bool) :=
  fun c i ↦ if ord I i < o then c i else false

lemma continuous_ProjOrd (o : Ordinal) :
    Continuous (ProjOrd o : (WithTop I → Bool) → (WithTop I → Bool)) := by
  refine' continuous_pi _
  intro i
  dsimp [ProjOrd]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma isClosedMap_projOrd (o : Ordinal) :
    IsClosedMap (ProjOrd o : (WithTop I → Bool) → (WithTop I → Bool)) :=
  fun _ hF ↦ (IsCompact.isClosed (hF.isCompact.image (continuous_ProjOrd o)))

def Res (o : Ordinal) : Set (WithTop I → Bool) := (ProjOrd o) '' C

lemma isClosed_Res (o : Ordinal) (hC : IsClosed C) : IsClosed (Res C o) :=
  isClosedMap_projOrd o C hC

lemma support_Res_le_o (o : Ordinal) : Support (Res C o) ⊆ {j | ord I j < o} := by
  intro j hj
  dsimp [Support, Res, ProjOrd] at hj
  simp only [Set.mem_image, exists_exists_and_eq_and, Bool.ite_eq_true_distrib] at hj
  simp only [Set.mem_setOf_eq]
  obtain ⟨_, ⟨_, h⟩⟩ := hj
  split_ifs at h
  assumption

noncomputable
def ResOnSubset (o : Ordinal) : {i // i ∈ C} → {i // i ∈ Res C o} :=
fun ⟨i, h⟩ ↦ ⟨ProjOrd o i, Set.mem_image_of_mem _ h⟩

lemma resOnSubset_eq (o : Ordinal) : Subtype.val ∘ ResOnSubset C o =
    (ProjOrd o : (WithTop I → Bool) → _) ∘ Subtype.val := by
  rfl

lemma continuous_val_comp_ResOnSubset (o : Ordinal) :
    Continuous (Subtype.val ∘ ResOnSubset C o) := by
  rw [resOnSubset_eq _]
  exact Continuous.comp (continuous_ProjOrd o) continuous_subtype_val

lemma continuous_ResOnSubset (o : Ordinal) : Continuous (ResOnSubset C o) := by
  rw [continuous_induced_rng]
  exact continuous_val_comp_ResOnSubset _ _

lemma surjective_ResOnSubset (o : Ordinal) : Function.Surjective (ResOnSubset C o) := by
  rintro ⟨i, h⟩
  obtain ⟨b, hb⟩ := h
  dsimp [ResOnSubset]
  use ⟨b, hb.1⟩
  simp_rw [← hb.2]

lemma ResMono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) {f : WithTop I → Bool}
    (hf : ProjOrd o₂ f ∈ Res C o₂) : ProjOrd o₁ f ∈ Res C o₁ := by
  obtain ⟨c,⟨_,hc⟩⟩  := hf
  dsimp [ProjOrd] at hc
  dsimp [Res, ProjOrd]
  use c
  refine' ⟨(by assumption),_⟩
  ext i
  dsimp
  have hc' := congr_fun hc i
  split_ifs
  · split_ifs at hc' with h₁
    · exact hc'
    · exfalso
      apply h₁ (lt_of_lt_of_le (by assumption) h)
  · rfl

-- noncomputable
-- def ResOnSubsetsLift (o : Ordinal) : {i // i ∈ Res C o} → {i // i ∈ C} :=
-- Function.surjInv (surjective_ResOnSubset C o)

-- noncomputable
-- def ProjOrdLift (o : Ordinal) (e : {i // i ∈ Res C o}) : (WithTop I → Bool) :=
-- Function.surjInv (surjective_ResOnSubset C o)

lemma ProjOrdSelf (o : Ordinal) {f : WithTop I → Bool} (hf : f ∈ Res C o) :
    ProjOrd o f = f := by
  dsimp [ProjOrd]
  ext i
  split_ifs
  · rfl
  · obtain ⟨c,hc⟩ := hf
    rw [←congr_fun hc.2 i]
    dsimp [ProjOrd]
    rw [eq_ite_iff]
    right
    exact ⟨(by assumption), (by rfl)⟩

lemma ResMono' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) {f : WithTop I → Bool}
    (hf : f ∈ Res C o₂) : ProjOrd o₁ f ∈ Res C o₁ := by
  rw [← ProjOrdSelf C o₂ hf] at hf
  exact ResMono C h hf

noncomputable
def ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : {i // i ∈ Res C o₂} → {i // i ∈ Res C o₁} :=
  fun e ↦ ⟨ProjOrd o₁ e.val, ResMono' C h e.property⟩

lemma resOnSubsets_eq {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : ResOnSubset C o₁ =
    ResOnSubsets C h ∘ ResOnSubset C o₂  := by
  ext e i
  dsimp [ResOnSubsets, ResOnSubset]
  dsimp [ProjOrd]
  split_ifs with h₁ h₂
  · rfl
  · exfalso
    apply h₂ (lt_of_lt_of_le h₁ h)
  · rfl

lemma continuous_ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : Continuous (ResOnSubsets C h) := by
  rw [continuous_induced_rng]
  exact continuous_val_comp_ResOnSubset (Res C o₂) o₁

lemma surjective_ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
    Function.Surjective (ResOnSubsets C h) := by
  apply @Function.Surjective.of_comp _ _ _ _ (ResOnSubset C o₂)
  rw [← resOnSubsets_eq C h]
  exact surjective_ResOnSubset _ _

-- lemma Products.isGoodMonoAux {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
--     eval (Res C o₁) '' {m | m < l} ⊆ eval (Res C o₂) '' {m | m < l} := by
--   sorry

lemma Products.isGoodMono {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : l.isGood (Res C o₂) := by
  have h' := lt_or_eq_of_le h
  cases h'
  · dsimp [isGood] at *
    intro h'
    apply hl
    obtain ⟨ll, lp⟩ := l
    induction ll with
    | nil =>
      · dsimp [eval]
        dsimp [eval] at h'
        sorry
    | cons a as ih => sorry
  · rw [(by assumption : o₁ = o₂)] at hl
    assumption

lemma GoodProducts.evalFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : eval (Res C o₂) ⟨l, (Products.isGoodMono C h hl)⟩ =
    eval (Res C o₁) ⟨l, hl⟩ ∘ ResOnSubsets C h := sorry

lemma GoodProducts.lin_smaller (o : Ordinal) : LinearIndependent ℤ (eval (Res C o)) ↔
    LinearIndependent ℤ ((LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o) : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ]
    LocallyConstant {i // i ∈ C} ℤ) ∘ (eval (Res C o))) :=
  (LinearMap.linearIndependent_iff (LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o))
    (LocallyConstant.comapLinear_injective _ _ (surjective_ResOnSubset C o))).symm

def ModProducts.smaller (o : Ordinal) : Set (LocallyConstant {i // i ∈ C} ℤ) :=
  (LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o) : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ]
    LocallyConstant {i // i ∈ C} ℤ) '' (ModProducts (Res C o))

lemma ModProducts.union {o : Ordinal} (ho : o.IsLimit) (hsC : Support C ⊆ {i | ord I i < o}) :
    ModProducts C = ⋃ (e : {o' // o' < o}), (smaller C e.val) := by
  ext p
  constructor <;>
  rintro hp
  · dsimp [smaller]
    dsimp [ModProducts] at *
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
    sorry
  · dsimp [ModProducts]
    simp at *
    obtain ⟨o', h⟩ := hp
    obtain ⟨f, hf⟩ := h.2
    obtain ⟨x, hx⟩ := hf.1
    rw [← hx] at hf
    rw [← hf.2]
    dsimp [LocallyConstant.comapLinear]
    have : Products.isGood C x := sorry
    use x
    use this
    ext y
    -- rw [LocallyConstant.coe_comap_apply]
    -- dsimp [ResOnSubset, GoodProducts.eval, Products.eval]
    sorry

def ModProducts.equiv {o : Ordinal} (ho : o.IsLimit) (hsC : Support C ⊆ {i | ord I i < o}) :
    ModProducts C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val) :=
  Equiv.Set.ofEq (union C ho hsC)

lemma ModProducts.equivFactorization {o : Ordinal} (ho : o.IsLimit)
    (hsC : Support C ⊆ {i | ord I i < o}) :
    (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) ∘ (equiv C ho hsC).toFun =
    (fun (p : ModProducts C) ↦ (p.1 : LocallyConstant {i // i ∈ C} ℤ)) := by
  rfl

lemma ModProducts.linear_independent_iff {o : Ordinal} (ho : o.IsLimit)
    (hsC : Support C ⊆ {i | ord I i < o}) : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) := by
  rw [GoodProducts.linear_independent_iff]
  rw [← equivFactorization C ho hsC]
  exact linearIndependent_equiv (equiv C ho hsC)

lemma ModProducts.smaller_linear_independent_iff (o : Ordinal) :
    LinearIndependent ℤ (GoodProducts.eval (Res C o)) ↔
    LinearIndependent ℤ (fun (p : ModProducts.smaller C o) ↦ p.1) := sorry

lemma ModProducts.smaller_mono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : smaller C o₁ ⊆ smaller C o₂ := by
  intro f hf
  dsimp [smaller, LocallyConstant.comapLinear] at *
  obtain ⟨g, hg⟩ := hf
  simp only [Set.mem_image]
  use LocallyConstant.comap (ResOnSubsets C h) g
  refine' ⟨_,_⟩
  · dsimp [ModProducts]
    dsimp [ModProducts] at hg
    obtain ⟨⟨l,gl⟩, hl⟩ := hg.1
    use ⟨l, Products.isGoodMono C h gl⟩
    ext x
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _), ← hl]
    exact congr_fun (GoodProducts.evalFac _ _ _) x
  · rw [← hg.2]
    ext x
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
    congr
    exact congr_fun (resOnSubsets_eq C h).symm x

lemma DirectedS {o : Ordinal} (ho : o.IsLimit) : Directed (· ⊆ ·) (fun e ↦ ModProducts.smaller C e.val :
    {o' // o' < o} → Set (LocallyConstant { i // i ∈ C } ℤ)) := by
  rintro ⟨o₁,h₁⟩ ⟨o₂,h₂⟩
  dsimp
  dsimp [Ordinal.IsLimit] at ho
  have h : o₁ ≤ o₂ ∨ o₂ ≤ o₁ :=
    (inferInstance : IsTotal Ordinal ((·≤·) : Ordinal → Ordinal → Prop)).total o₁ o₂
  cases h
  · use ⟨(Order.succ o₂), ho.2 o₂ h₂⟩
    have ho₁ : o₁ ≤ Order.succ o₂ := @le_trans _ _ _ o₂ _ (by assumption) (Order.le_succ _)
    have ho₂ : o₂ ≤ Order.succ o₂ := Order.le_succ _
    exact ⟨ModProducts.smaller_mono C ho₁, ModProducts.smaller_mono C ho₂⟩
  · use ⟨(Order.succ o₁), ho.2 o₁ h₁⟩
    have ho₁ : o₁ ≤ Order.succ o₁ := Order.le_succ _
    have ho₂ : o₂ ≤ Order.succ o₁ := @le_trans _ _ _ o₁ _ (by assumption) (Order.le_succ _)
    exact ⟨ModProducts.smaller_mono C ho₁, ModProducts.smaller_mono C ho₂⟩

lemma GoodProducts.linearIndependentAux (i : WithTop I) : P i := by
  rw [PIffP I i]
  apply Ordinal.limitRecOn
  · dsimp [P']
    intro C _ hsC
    dsimp [Support] at hsC
    have : C ⊆ {(fun a ↦ false)}
    · intro c hc
      simp
      ext x
      simp at hsC
      specialize hsC x c hc
      rw [Bool.eq_false_iff]
      intro ht
      apply Ordinal.not_lt_zero (ord I x)
      exact hsC ht
    rw [Set.subset_singleton_iff_eq] at this
    rcases this
    · subst C
      exact linearIndependentEmpty
    · subst C
      exact linearIndependentSingleton
  · sorry
  · intro o ho h
    dsimp [P'] at *
    intro C hC hsC
    rw [ModProducts.linear_independent_iff]
    refine' linearIndependent_iUnion_of_directed (DirectedS C ho) _
    rintro ⟨o', ho'⟩
    specialize h o' ho' (Res C o') (isClosed_Res C o' hC) (support_Res_le_o C o')
    rw [ModProducts.smaller_linear_independent_iff] at h
    exact h
    assumption -- why these new goals?
    assumption -- ?

lemma GoodProducts.spanAux (i : WithTop I) : Q i := sorry

variable {C₁ : Set (I → Bool)}

lemma isClosedInWithTop (hC₁ : IsClosed C₁) : IsClosed ((r I) '' C₁) :=
(r.embedding I).toEmbedding.toInducing.isClosedMap (r.embedding I).closed_range C₁ hC₁

lemma supportTop (C₁ : Set (I → Bool)) : Support ((r I) '' C₁) ⊆ {j | j < ⊤} := by
  dsimp [Support]
  intro i hi
  obtain ⟨f, hf⟩ := hi
  obtain ⟨c, hc⟩ := hf.1
  rw [← hc.2] at hf
  dsimp [r] at hf
  cases i
  · dsimp at hf
    exfalso
    exact Bool.not_false' hf.2
  · dsimp at hf
    dsimp
    rw [← WithTop.none_eq_top]
    exact WithTop.some_lt_none _

lemma GoodProducts.linearIndependent (hC₁ : IsClosed C₁) :
  LinearIndependent ℤ (GoodProducts.eval ((r I) '' C₁)) :=
GoodProducts.linearIndependentAux ⊤ ((r I) '' C₁) (isClosedInWithTop hC₁) (supportTop C₁)

lemma GoodProducts.span (hC₁ : IsClosed C₁) :
  ⊤ ≤ Submodule.span ℤ (Set.range (GoodProducts.eval ((r I) '' C₁))) :=
GoodProducts.spanAux ⊤ ((r I) '' C₁) (isClosedInWithTop hC₁) (supportTop C₁)

noncomputable
def GoodProducts.Basis (hC₁ : IsClosed C₁) : Basis (GoodProducts ((r I) '' C₁)) ℤ
  (LocallyConstant {i // i ∈ ((r I) '' C₁)} ℤ) :=
Basis.mk (GoodProducts.linearIndependent hC₁) (GoodProducts.span hC₁)

lemma closedFree (hC₁ : IsClosed C₁) : Module.Free ℤ (LocallyConstant {i // i ∈ ((r I) '' C₁)} ℤ) :=
Module.Free.of_basis $ GoodProducts.Basis hC₁

variable {S : Profinite} {ι : S → I → Bool} (hι : ClosedEmbedding ι)

noncomputable
def homeoClosed₁ : S ≃ₜ Set.range ι := Homeomorph.ofEmbedding ι hι.toEmbedding

def rι.embedding : ClosedEmbedding (r I ∘ ι) := ClosedEmbedding.comp (r.embedding I) hι

noncomputable
def homeoClosed₂ : S ≃ₜ Set.range (r I ∘ ι) :=
Homeomorph.ofEmbedding (r I ∘ ι) (rι.embedding hι).toEmbedding

def homeoRange : Set.range (r I ∘ ι) ≃ₜ r I '' Set.range ι := by
  rw [Set.range_comp]
  exact Homeomorph.refl _

def setHomeoSubtype {X : Type _} [TopologicalSpace X] (s : Set X) : s ≃ₜ {x // x ∈ s} :=
{ toFun := fun x ↦ ⟨x.val, x.prop⟩
  invFun := fun x ↦ x
  left_inv := by
    intro x
    dsimp
  right_inv := by
    intro x
    dsimp }

noncomputable
def homeoClosed : S ≃ₜ { i // i ∈ r I '' Set.range ι } :=
(homeoClosed₂ hι).trans (homeoRange.trans (setHomeoSubtype (r I '' Set.range ι)))

noncomputable
def locConstIso (hι : ClosedEmbedding ι) :
  (LocallyConstant S ℤ) ≃ₗ[ℤ] (LocallyConstant { i // i ∈ r I '' Set.range ι } ℤ) :=
LocallyConstant.equivLinear (homeoClosed hι)

lemma Nobeling : Module.Free ℤ (LocallyConstant S ℤ) := Module.Free.of_equiv'
  (closedFree hι.closed_range) (locConstIso hι).symm

end NobelingProof

variable (S : Profinite)

open Classical

noncomputable
def Nobeling.ι : S → ({C : Set S // IsClopen C} → Bool) := fun s C => decide (s ∈ C.1)

lemma Nobeling.embedding : ClosedEmbedding (Nobeling.ι S) := by
  apply Continuous.closedEmbedding
  · dsimp [ι]
    refine' continuous_pi _
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine' ((IsLocallyConstant.tfae _).out 0 3).mpr _
    rintro ⟨⟩
    · have : (fun a ↦ decide (a ∈ C.1)) ⁻¹' {false} = C.1ᶜ
      · ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff,
          decide_eq_false_iff_not, Set.mem_compl_iff]
      · rw [this]
        refine' IsClopen.isOpen _
        simp only [isClopen_compl_iff]
        exact C.2
    · have : (fun a ↦ decide (a ∈ C.1)) ⁻¹' {true} = C.1
      · ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
      · rw [this]
        refine' IsClopen.isOpen _
        exact C.2
  · intro a b hab
    by_contra hnab
    have h' := exists_clopen_of_totally_separated hnab
    obtain ⟨C, hC, h₁⟩ := h'
    apply h₁.2
    have ha : ι S a ⟨C, hC⟩ = decide (a ∈ C) := rfl
    have hb : ι S b ⟨C, hC⟩ = decide (b ∈ C) := rfl
    apply of_decide_eq_true
    rw [← hb, ← hab, ha]
    apply decide_eq_true
    exact h₁.1

theorem Nobeling : Module.Free ℤ (LocallyConstant S ℤ) :=
@NobelingProof.Nobeling {C : Set S // IsClopen C} (IsWellOrder.linearOrder WellOrderingRel)
  WellOrderingRel.isWellOrder S (Nobeling.ι S) (Nobeling.embedding S)
