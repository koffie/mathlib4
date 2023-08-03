import Mathlib.GroupTheory.Torsion
import Mathlib.NumberTheory.NumberField.Basic

open NumberField BigOperators

variable (K : Type _) [Field K] (n : ℕ)

def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

set_option trace.profiler true in
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq true in
set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 100000 in
def Basis_additive : Basis (Fin n) ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := sorry

set_option trace.profiler true in
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq true in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
example {ι : Type _} [Fintype ι] (f : ι → (𝓞 K)ˣ) :
    ((∏ i, (f i) : (𝓞 K)ˣ) : (𝓞 K)ˣ ⧸ (torsion K)) = ∏ i, ↑(f i) := by
  simp_rw [← QuotientGroup.mk'_apply]
  convert map_prod (QuotientGroup.mk' (torsion K)) f Finset.univ
