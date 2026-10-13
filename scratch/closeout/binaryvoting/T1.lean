import SEKernel.PluralityCountFormula
import SEKernel.EpistemicPayoff

namespace SEKernel.Closeout.BinaryVoting

open Finset
open scoped Nat
open SEKernel.FiniteProbability
open SEKernel.Epistemic

def binaryProfile (a : Bool) (N j : ℕ) : Option Bool → ℕ
  | none => 0
  | some b => if b = a then j else N - j

noncomputable def binaryVoteWeight (N j : ℕ) : ℝ :=
  if N < 2 * j then 1 else if 2 * j = N then 1 / 2 else 0

noncomputable def binaryVoteWeight₀ (N j : ℕ) : ℝ :=
  if N < 2 * j then 1 else if 2 * j = N ∧ 0 < j then 1 / 2 else 0

theorem wrong_mass_of_no_abstention (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) : π.mass (some (!a)) = 1 - π.mass (some a) := by
  have ht := π.total
  rw [Fintype.sum_option, Fintype.sum_bool, hnone] at ht
  cases a <;> simp <;> linarith

theorem multinomial_binaryProfile (a : Bool) {N j : ℕ} (hj : j ≤ N) :
    Nat.multinomial Finset.univ (binaryProfile a N j) = N.choose j := by
  rw [Nat.multinomial, Fintype.sum_option, Fintype.prod_option, Fintype.sum_bool,
    Fintype.prod_bool]
  cases a
  · simp [binaryProfile, Nat.sub_add_cancel hj, Nat.choose_eq_factorial_div_factorial hj,
      mul_comm]
  · simp [binaryProfile, Nat.add_sub_of_le hj, Nat.choose_eq_factorial_div_factorial hj]

theorem prod_binaryProfile (π : Law (Option Bool)) (a : Bool) (hnone : π.mass none = 0)
    (N j : ℕ) :
    ∏ q, π.mass q ^ binaryProfile a N j q =
      π.mass (some a) ^ j * (1 - π.mass (some a)) ^ (N - j) := by
  rw [← wrong_mass_of_no_abstention π a hnone, Fintype.prod_option, Fintype.prod_bool]
  cases a <;> simp [binaryProfile, mul_comm]

theorem mem_readableModes_binaryProfile (a b : Bool) (N j : ℕ) :
    b ∈ readableModes (binaryProfile a N j) ↔
      (if b = a then 0 < j ∧ N - j ≤ j else 0 < N - j ∧ j ≤ N - j) := by
  simp only [readableModes, Finset.mem_filter, Finset.mem_univ, true_and, Bool.forall_bool,
    binaryProfile]
  cases a <;> cases b <;> simp

theorem tie_binaryProfile (a : Bool) {N j : ℕ} (hj : j ≤ N)
    (inst : Decidable (a ∈ readableModes (binaryProfile a N j))) :
    (if a ∈ readableModes (binaryProfile a N j) then
        1 / ((readableModes (binaryProfile a N j)).card : ℝ) else 0) =
      binaryVoteWeight₀ N j := by
  have hmem := fun b => mem_readableModes_binaryProfile a b N j
  unfold binaryVoteWeight₀
  by_cases h1 : N < 2 * j
  · have hs : readableModes (binaryProfile a N j) = {a} := by
      ext b
      rw [hmem b, Finset.mem_singleton]
      by_cases hb : b = a
      · simp [hb]; omega
      · simp [hb]; omega
    rw [if_pos (by rw [hs]; exact Finset.mem_singleton_self a), hs, if_pos h1]
    simp
  · by_cases h2 : 2 * j = N ∧ 0 < j
    · have hs : readableModes (binaryProfile a N j) = Finset.univ := by
        ext b
        rw [hmem b]
        by_cases hb : b = a
        · simp [hb]; omega
        · simp [hb]; omega
      rw [if_pos (by rw [hs]; exact Finset.mem_univ a), hs, if_neg h1, if_pos h2]
      simp
    · have hn : a ∉ readableModes (binaryProfile a N j) := by
        rw [hmem a]; simp; omega
      rw [if_neg hn, if_neg h1, if_neg h2]


theorem prod_eq_zero_of_none (π : Law (Option Bool)) (hnone : π.mass none = 0)
    (c : Option Bool → ℕ) (hc : c none ≠ 0) : ∏ q, π.mass q ^ c q = 0 := by
  rw [Fintype.prod_option, hnone, zero_pow hc, zero_mul]

theorem binaryProfile_injOn (a : Bool) (N : ℕ) :
    Set.InjOn (binaryProfile a N) (Finset.range (N + 1) : Set ℕ) := by
  intro i _ j _ h
  simpa [binaryProfile] using congrFun h (some a)

theorem sum_validCountProfiles_binary (a : Bool) (N : ℕ) (F : (Option Bool → ℕ) → ℝ)
    (hF : ∀ c, c none ≠ 0 → F c = 0) :
    ∑ c ∈ validCountProfiles Bool N, F c =
      ∑ j ∈ Finset.range (N + 1), F (binaryProfile a N j) := by
  classical
  rw [← Finset.sum_image (binaryProfile_injOn a N)]
  symm
  apply Finset.sum_subset
  · intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [validCountProfiles, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
      and_true]
    rw [Fintype.sum_option, Fintype.sum_bool]
    cases a <;> simp [binaryProfile] <;> omega
  · intro c hc hnot
    by_cases h0 : c none = 0
    · exfalso
      apply hnot
      have hsum : ∑ q, c q = N := by
        simpa [validCountProfiles, Finset.mem_piAntidiag] using hc
      rw [Fintype.sum_option, Fintype.sum_bool, h0] at hsum
      refine Finset.mem_image.2 ⟨c (some a), ?_, ?_⟩
      · rw [Finset.mem_range]; cases a <;> omega
      · funext q
        cases q with
        | none => simp [binaryProfile, h0]
        | some b =>
          cases a <;> cases b <;> simp [binaryProfile] <;> omega
    · exact hF c h0

/-- Binary vote accuracy for every `N` (including `N = 0`) on a readable binary law. -/
theorem binary_vote_formula₀ (π : Law (Option Bool)) (a : Bool) (hnone : π.mass none = 0)
    (N : ℕ) :
    voteAccuracy π N a = ∑ j ∈ Finset.range (N + 1),
      (N.choose j : ℝ) * π.mass (some a) ^ j * (1 - π.mass (some a)) ^ (N - j) *
        binaryVoteWeight₀ N j := by
  classical
  rw [plurality_multinomial_formula π a]
  rw [sum_validCountProfiles_binary a N]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [multinomial_binaryProfile a hj', prod_binaryProfile π a hnone,
      tie_binaryProfile a hj' _]
    ring
  · intro c hc
    rw [prod_eq_zero_of_none π hnone c hc]
    ring

theorem binaryVoteWeight₀_eq {N j : ℕ} (hN : 0 < N) :
    binaryVoteWeight₀ N j = binaryVoteWeight N j := by
  unfold binaryVoteWeight₀ binaryVoteWeight
  by_cases h1 : N < 2 * j
  · simp [h1]
  · by_cases h2 : 2 * j = N
    · have hj : 0 < j := by omega
      simp [h2, hj]
    · simp [h1, h2]

/-- Doc B A3.1, binary form: `V_N = Σ_j C(N,j) p^j (1-p)^(N-j) w_N(j)` for `N ≥ 1`. -/
theorem binary_vote_formula (π : Law (Option Bool)) (a : Bool) (hnone : π.mass none = 0)
    {N : ℕ} (hN : 0 < N) :
    voteAccuracy π N a = ∑ j ∈ Finset.range (N + 1),
      (N.choose j : ℝ) * π.mass (some a) ^ j * (1 - π.mass (some a)) ^ (N - j) *
        binaryVoteWeight N j := by
  rw [binary_vote_formula₀ π a hnone N]
  apply Finset.sum_congr rfl
  intro j _
  rw [binaryVoteWeight₀_eq hN]

end SEKernel.Closeout.BinaryVoting
