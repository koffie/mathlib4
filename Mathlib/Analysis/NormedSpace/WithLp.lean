/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Real.ENNReal
import Mathlib.LinearAlgebra.FiniteDimensional

/-! # The `WithLp` type synonym

`WithLp p V` is the vector space `V`, but with the Lp norm.

This file defines the vector space structure for all types `V`; the norm structure is built for
different specializations of `V` in downstream files.
-/

open scoped ENNReal
set_option linter.uppercaseLean3 false

universe uK uK' uV

/-- A type synony for the given `V`, associated with the L`p` norm. Note that by default this just
forgets the norm structure on `V`; it is up to downstream users to implement the L`p` norm (for
instance, on `Prod` and finite `Pi` types). -/
@[nolint unusedArguments]
def WithLp (_p : ℝ≥0∞) (V : Type u) : Type u := V

variable (p : ℝ≥0∞) (K : Type uK) (V : Type uV)

namespace WithLp

/-- The canonical equivalence between `WithLp p V` and `V`. This should always be used to convert
back and forth between the representations. -/
protected def equiv : WithLp p V ≃ V := Equiv.refl _

variable [Semiring K] [Semiring K'] [AddCommGroup V]

/-! `WithLp p V` inherits various module-adjacent structures from `V`. -/

instance instAddCommGroup : AddCommGroup (WithLp p V) := ‹AddCommGroup V›
instance instModule [Module K V] : Module K (WithLp p V) := ‹Module K V›

instance instIsScalarTower [SMul K K'] [Module K V] [Module K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) :=
  ‹IsScalarTower K K' V›

instance instSmulCommClass [Module K V] [Module K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) :=
  ‹SMulCommClass K K' V›

instance instModuleFinite [Module K V] [Module.Finite K V] : Module.Finite K (WithLp p V) :=
  ‹Module.Finite K V›

variable {K V}
variable [Module K V]
variable (c : K) (x y : WithLp p V) (x' y' : V)

/-! `WithLp.equiv` preserves the module structure. -/

@[simp]
theorem equiv_zero : WithLp.equiv p V 0 = 0 :=
  rfl
#align pi_Lp.equiv_zero WithLp.equiv_zero

@[simp]
theorem equiv_symm_zero : (WithLp.equiv p V).symm 0 = 0 :=
  rfl
#align pi_Lp.equiv_symm_zero WithLp.equiv_symm_zero

@[simp]
theorem equiv_add : WithLp.equiv p V (x + y) = WithLp.equiv p V x + WithLp.equiv p V y :=
  rfl
#align pi_Lp.equiv_add WithLp.equiv_add

@[simp]
theorem equiv_symm_add :
    (WithLp.equiv p V).symm (x' + y') = (WithLp.equiv p V).symm x' + (WithLp.equiv p V).symm y' :=
  rfl
#align pi_Lp.equiv_symm_add WithLp.equiv_symm_add

@[simp]
theorem equiv_sub : WithLp.equiv p V (x - y) = WithLp.equiv p V x - WithLp.equiv p V y :=
  rfl
#align pi_Lp.equiv_sub WithLp.equiv_sub

@[simp]
theorem equiv_symm_sub :
    (WithLp.equiv p V).symm (x' - y') = (WithLp.equiv p V).symm x' - (WithLp.equiv p V).symm y' :=
  rfl
#align pi_Lp.equiv_symm_sub WithLp.equiv_symm_sub

@[simp]
theorem equiv_neg : WithLp.equiv p V (-x) = -WithLp.equiv p V x :=
  rfl
#align pi_Lp.equiv_neg WithLp.equiv_neg

@[simp]
theorem equiv_symm_neg : (WithLp.equiv p V).symm (-x') = -(WithLp.equiv p V).symm x' :=
  rfl
#align pi_Lp.equiv_symm_neg WithLp.equiv_symm_neg

@[simp]
theorem equiv_smul : WithLp.equiv p V (c • x) = c • WithLp.equiv p V x :=
  rfl
#align pi_Lp.equiv_smul WithLp.equiv_smul

@[simp]
theorem equiv_symm_smul : (WithLp.equiv p V).symm (c • x') = c • (WithLp.equiv p V).symm x' :=
  rfl
#align pi_Lp.equiv_symm_smul WithLp.equiv_symm_smul

variable (K V)

/-- `WithLp.equiv` as a linear equivalence. -/
@[simps (config := { fullyApplied := false })]
protected def linearEquiv : WithLp p V ≃ₗ[K] V :=
  { LinearEquiv.refl _ _ with
    toFun := WithLp.equiv _ _
    invFun := (WithLp.equiv _ _).symm }

end WithLp
