import Mathlib.GroupTheory.Torsion
import Mathlib.NumberTheory.NumberField.Basic

open NumberField BigOperators

variable (K : Type _) [Field K] (n : ℕ)

def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 100000 in
def Basis_additive : Basis (Fin n) ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := sorry

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
example {ι : Type _} [Fintype ι] (f : ι → (𝓞 K)ˣ) :
  QuotientGroup.mk' (torsion K) (∏ i, (f i)) =
    ∏ i, QuotientGroup.mk' (torsion K) (f i) := by
  refine map_prod (QuotientGroup.mk' (torsion K)) _ _
