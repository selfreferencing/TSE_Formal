import SEKernel.PluralityCountFormula
open Finset
example (f : ℕ × ℕ → ℝ) : ∑ p ∈ antidiagonal 3, f p = f (0,3) + f (1,2) + f (2,1) + f (3,0) := by
  simp [Finset.Nat.sum_antidiagonal_succ]
  ring
example (f : ℕ × ℕ → ℝ) : ∑ p ∈ antidiagonal 3, f p = f (0,3) + f (1,2) + f (2,1) + f (3,0) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]
#check @Finset.mem_antidiagonal
