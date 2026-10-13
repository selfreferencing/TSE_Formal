import SEKernel.PluralityCountFormula
import SEKernel.EpistemicPayoff

namespace SEKernel.Closeout.BinaryVoting

open Finset
open scoped Nat

noncomputable def binaryVoteWeight (N j : ℕ) : ℝ :=
  if N < 2 * j then 1 else if 2 * j = N then 1 / 2 else 0

/-- Binomial point mass `C(n,j) p^j (1-p)^(n-j)` (zero when `j > n`). -/
noncomputable def binomTerm (p : ℝ) (n j : ℕ) : ℝ :=
  (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- The finite binary vote polynomial `Σ_j C(N,j) p^j (1-p)^(N-j) w_N(j)`. -/
noncomputable def binaryVotePoly (p : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), binomTerm p N j * binaryVoteWeight N j

theorem binomTerm_pascal (p : ℝ) (n j : ℕ) :
    binomTerm p (n + 1) (j + 1) = (1 - p) * binomTerm p n (j + 1) + p * binomTerm p n j := by
  unfold binomTerm
  rw [Nat.choose_succ_succ', Nat.cast_add]
  rcases Nat.lt_or_ge j n with h | h
  · have h1 : n + 1 - (j + 1) = n - j := by omega
    have h2 : n - j = (n - (j + 1)) + 1 := by omega
    rw [h1, h2]
    ring
  · have h0 : n.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : n + 1 - (j + 1) = n - j := by omega
    rw [h0, h1]
    ring

theorem binomTerm_zero_of_lt (p : ℝ) {n j : ℕ} (h : n < j) : binomTerm p n j = 0 := by
  unfold binomTerm
  rw [Nat.choose_eq_zero_of_lt h]
  ring

theorem weight_even_zero (m : ℕ) : binaryVoteWeight (2 * m + 2) 0 = 0 := by
  unfold binaryVoteWeight
  rw [if_neg (by omega), if_neg (by omega)]

theorem fair_tie_coefficient (p : ℝ) (m j : ℕ) :
    (1 - p) * binaryVoteWeight (2 * m + 2) j + p * binaryVoteWeight (2 * m + 2) (j + 1) -
        binaryVoteWeight (2 * m + 1) j =
      (if j = m + 1 then -(1 - p) / 2 else 0) + (if j = m then p / 2 else 0) := by
  unfold binaryVoteWeight
  rcases lt_trichotomy j m with h | h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  · subst h
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    ring
  · rcases Nat.lt_or_ge (m + 1) j with h' | h'
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
        if_neg (by omega)]
      ring
    · have hj : j = m + 1 := by omega
      subst hj
      rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_pos rfl, if_neg (by omega)]
      ring

/-- Fair ties, algebraic form: `V_{2m+2} = V_{2m+1}` for the binary vote polynomial. -/
theorem binaryVotePoly_fair_ties (p : ℝ) (m : ℕ) :
    binaryVotePoly p (2 * m + 2) = binaryVotePoly p (2 * m + 1) := by
  unfold binaryVotePoly
  rw [Finset.sum_range_succ', weight_even_zero, mul_zero, add_zero]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from rfl]
  have hp : ∀ j ∈ Finset.range (2 * m + 1 + 1),
      binomTerm p (2 * m + 1 + 1) (j + 1) * binaryVoteWeight (2 * m + 1 + 1) (j + 1) =
        (1 - p) * binomTerm p (2 * m + 1) (j + 1) * binaryVoteWeight (2 * m + 1 + 1) (j + 1) +
        p * binomTerm p (2 * m + 1) j * binaryVoteWeight (2 * m + 1 + 1) (j + 1) := by
    intro j _
    rw [binomTerm_pascal p (2 * m + 1) j]
    ring
  rw [Finset.sum_congr rfl hp, Finset.sum_add_distrib]
  -- shift the first sum back to index zero
  have hshift : ∑ j ∈ Finset.range (2 * m + 1 + 1),
      (1 - p) * binomTerm p (2 * m + 1) (j + 1) * binaryVoteWeight (2 * m + 1 + 1) (j + 1) =
      ∑ j ∈ Finset.range (2 * m + 1 + 1),
      (1 - p) * binomTerm p (2 * m + 1) j * binaryVoteWeight (2 * m + 1 + 1) j := by
    have h1 := Finset.sum_range_succ' (fun j =>
      (1 - p) * binomTerm p (2 * m + 1) j * binaryVoteWeight (2 * m + 1 + 1) j) (2 * m + 1 + 1)
    have h2 := Finset.sum_range_succ (fun j =>
      (1 - p) * binomTerm p (2 * m + 1) j * binaryVoteWeight (2 * m + 1 + 1) j) (2 * m + 1 + 1)
    rw [binomTerm_zero_of_lt p (show 2 * m + 1 < 2 * m + 1 + 1 by omega)] at h2
    have h0 : binaryVoteWeight (2 * m + 1 + 1) 0 = 0 := weight_even_zero m
    rw [h0] at h1
    simp only [mul_zero, add_zero, zero_mul] at h1 h2
    rw [← h1, h2]
  rw [hshift]
  have hdiff : (∑ j ∈ Finset.range (2 * m + 1 + 1),
      (1 - p) * binomTerm p (2 * m + 1) j * binaryVoteWeight (2 * m + 1 + 1) j) +
      (∑ j ∈ Finset.range (2 * m + 1 + 1),
      p * binomTerm p (2 * m + 1) j * binaryVoteWeight (2 * m + 1 + 1) (j + 1)) -
      (∑ j ∈ Finset.range (2 * m + 1 + 1), binomTerm p (2 * m + 1) j *
        binaryVoteWeight (2 * m + 1) j) =
      ∑ j ∈ Finset.range (2 * m + 1 + 1), (binomTerm p (2 * m + 1) j *
        (if j = m + 1 then -(1 - p) / 2 else 0) +
        binomTerm p (2 * m + 1) j * (if j = m then p / 2 else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_add, ← fair_tie_coefficient p m j]
    ring
  rw [Finset.sum_add_distrib] at hdiff
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
    show m + 1 < 2 * m + 1 + 1 by omega, show m < 2 * m + 1 + 1 by omega, if_true] at hdiff
  have hsym : binomTerm p (2 * m + 1) (m + 1) * (-(1 - p) / 2) +
      binomTerm p (2 * m + 1) m * (p / 2) = 0 := by
    unfold binomTerm
    rw [Nat.choose_symm_half m, show 2 * m + 1 - (m + 1) = m by omega,
      show 2 * m + 1 - m = m + 1 by omega]
    ring
  linarith

end SEKernel.Closeout.BinaryVoting
