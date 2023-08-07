import Mathlib.GroupTheory.QuotientGroup

open BigOperators

@[to_additive (attr := simp)]
theorem QuotientGroup.mk_prod {G ι : Type _} [CommGroup G] (N : Subgroup G) [Subgroup.Normal N]
    [Fintype ι] {f : ι → G} :
    ((∏ i, (f i) : G) : G ⧸ N) = ∏ i, (f i : G ⧸ N) :=
  map_prod (QuotientGroup.mk' N) _ _
