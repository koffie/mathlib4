/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.FinCases

/-!
# The binominal distribution

This file defines the probability mass function of the binominal distribution, and proves
it to be equal to `Pmf.bernoulli` for `n = 1`.
-/

noncomputable section

namespace Pmf

/-- The binomial `Pmf`: The probability of that `i` out of `n` coins come up heads if the
probability of heads is `p`. -/
def binominal (p : ENNReal) (h : p ≤ 1) (n : ℕ) : Pmf (Fin (n + 1)) :=
  .ofFintype (fun i => p^(i : ℕ) * (1-p)^(n - (i : ℕ)) * (n.choose i : ℕ)) (by
    convert (add_pow p (1-p) n).symm
    . rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp at hi
      rw [dif_pos hi]
    . simp [h])

theorem binominal_apply : binominal p h n i =
  p^(i : ℕ) * (1-p)^(n - (i : ℕ)) * (n.choose i : ℕ) := rfl

@[simp]
theorem binominal_apply_0 : binominal p h n 0 = (1-p)^n :=
  by simp [binominal_apply]

@[simp]
theorem binominal_apply_n : binominal p h n n = p^n :=
  by simp [binominal_apply, Nat.mod_eq_of_lt]

/-- The binominal distribution on one coin is the bernoully distribution. -/
theorem binominal_one_eq_bernoulli :
  binominal p h 1 = (bernoulli p h).map (cond · 1 0) := by
    ext i; fin_cases i <;> simp [tsum_bool, binominal_apply]
