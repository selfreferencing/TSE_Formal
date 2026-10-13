/-
Close-out: binary vote accuracy, fair ties, the 10/5 hump on the actual law,
the union bound, prefix realizability, the nonmodal counterexamples, and Doc A's
chance-pickup example.

Every probability below is a probability of the actual IID ordered-word law
`iidWordLaw` under the actual first-appearance plurality rule; numbers are
obtained only by `norm_num`/`simp` after rewriting with proved formulas.
Doc B: A3.1, A3.5, A5.1 (with A5.2-A5.4); Doc A: A2, A3.5, A5.1; referee fixes
from PROOFCHECK_A0_A5 (fair ties, union bound, strengthened realizability).
-/
import SEKernel.PluralityCountExamples
import SEKernel.EpistemicPayoff

namespace SEKernel.Closeout.BinaryVoting

open Finset
open scoped Nat
open SEKernel.FiniteProbability
open SEKernel.Epistemic

/-! ## Binary vote accuracy (Doc B A3.1, binary specialization) -/

/-- The count profile of a readable binary word with `j` copies of `a` and
`N - j` copies of `!a`, and no abstentions. -/
def binaryProfile (a : Bool) (N j : ℕ) : Option Bool → ℕ
  | none => 0
  | some b => if b = a then j else N - j

/-- Binary first-appearance tie weight: `1` on a strict majority of the correct label,
`1/2` on an exact tie, `0` otherwise (the convention of the close-out target). -/
noncomputable def binaryVoteWeight (N j : ℕ) : ℝ :=
  if N < 2 * j then 1 else if 2 * j = N then 1 / 2 else 0

/-- The same weight with the empty word handled: an exact tie needs `j > 0`, so the
formula below also holds at `N = 0` (where `V_0 = 0`). -/
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

/-- The actual tie factor of the count formula on a binary profile. The decidability
proof is an explicit argument, so the lemma rewrites whichever one occurs. -/
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

/-- With no abstention mass, the count-profile sum reduces to a sum over the number
`j` of correct answers. -/
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


/-! ## Fair ties (Doc A A5.1; referee fix 4) -/

/-- Binomial point mass `C(n,j) p^j (1-p)^(n-j)` (zero when `j > n`). -/
noncomputable def binomTerm (p : ℝ) (n j : ℕ) : ℝ :=
  (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- The finite binary vote polynomial `Σ_j C(N,j) p^j (1-p)^(N-j) w_N(j)`. -/
noncomputable def binaryVotePoly (p : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), binomTerm p N j * binaryVoteWeight N j

/-- Pascal's rule for binomial point masses, valid for every `n, j`. -/
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

/-- Coefficient bookkeeping: after Pascal's rule the two vote polynomials differ only
at `j = m` and `j = m + 1`. -/
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


/-- The binary formula in polynomial form. -/
theorem voteAccuracy_eq_binaryVotePoly (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) {N : ℕ} (hN : 0 < N) :
    voteAccuracy π N a = binaryVotePoly (π.mass (some a)) N := by
  rw [binary_vote_formula π a hnone hN]
  rfl

/-- Doc A A5.1 fair ties: `V_{2k} = V_{2k-1}` for `k ≥ 1` on a readable binary law. -/
theorem binary_fair_ties (π : Law (Option Bool)) (a : Bool) (hnone : π.mass none = 0)
    {k : ℕ} (hk : 1 ≤ k) :
    voteAccuracy π (2 * k) a = voteAccuracy π (2 * k - 1) a := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (m + 1) = 2 * m + 2 by ring, show 2 * m + 2 - 1 = 2 * m + 1 by omega,
    voteAccuracy_eq_binaryVotePoly π a hnone (by omega),
    voteAccuracy_eq_binaryVotePoly π a hnone (by omega), binaryVotePoly_fair_ties]

/-- `V_9` is the kernel's existing `binaryVote9` polynomial. -/
theorem binaryVotePoly_nine (p : ℝ) :
    binaryVotePoly p 9 = SEKernel.EpistemicPayoff.binaryVote9 p := by
  simp only [binaryVotePoly, Finset.sum_range_succ, Finset.sum_range_zero, binomTerm,
    binaryVoteWeight, SEKernel.EpistemicPayoff.binaryVote9]
  norm_num [Nat.choose]

/-- Independent direct check: the ten-voter polynomial (with its `1/2` tie term) also
equals `binaryVote9`. -/
theorem binaryVotePoly_ten (p : ℝ) :
    binaryVotePoly p 10 = SEKernel.EpistemicPayoff.binaryVote9 p := by
  simp only [binaryVotePoly, Finset.sum_range_succ, Finset.sum_range_zero, binomTerm,
    binaryVoteWeight, SEKernel.EpistemicPayoff.binaryVote9]
  norm_num [Nat.choose]
  ring


/-! ## Union bound (Doc B Cor. A5.2; referee fix 7) -/

/-- A single coordinate of the IID word misses the correct answer with mass `1 - p`. -/
theorem coord_ne_probability {A : Type*} [Fintype A] (π : Law (Option A)) (N : ℕ)
    (i : Fin N) (a : A) :
    (iidWordLaw π N).prob (fun z => z i ≠ some a) = 1 - π.mass (some a) := by
  classical
  have h := Law.expect_pi_coord (fun _ : Fin N => π) i
    (fun x => if x ≠ some a then (1 : ℝ) else 0)
  rw [Law.expect_indicator π (fun x => x ≠ some a), prob_single_label_compl] at h
  rw [← h, ← Law.expect_indicator]
  rfl

/-- If every draw is the correct answer, the vote is correct (`N ≥ 1`). -/
theorem all_correct_vote {N : ℕ} {A : Type*} (z : OrderedWord N A) (a : A) (hN : 0 < N)
    (h : ∀ i, z i = some a) : correctVote z a :=
  plurality_unique_readable z a ⟨⟨0, hN⟩, h _⟩ (fun i => Or.inr (h i))

/-- Union bound: if every draw is correct the vote is correct, so
`1 - V_N ≤ N (1 - p)` for every law and every `N ≥ 1`. -/
theorem one_sub_voteAccuracy_le {A : Type*} [Fintype A] (π : Law (Option A)) (a : A)
    {N : ℕ} (hN : 0 < N) :
    1 - voteAccuracy π N a ≤ N * (1 - π.mass (some a)) := by
  classical
  unfold voteAccuracy
  rw [← Law.prob_compl]
  calc (iidWordLaw π N).prob (fun z => ¬ correctVote z a)
      ≤ (iidWordLaw π N).prob (fun z => ∃ i, z i ≠ some a) := by
        apply Law.prob_mono
        intro z hz
        by_contra hc
        push_neg at hc
        exact hz (all_correct_vote z a hN hc)
    _ ≤ ∑ i, (iidWordLaw π N).prob (fun z => z i ≠ some a) :=
        Law.prob_exists_le _ (fun (i : Fin N) (z : OrderedWord N A) => z i ≠ some a)
    _ = N * (1 - π.mass (some a)) := by
        simp only [coord_ne_probability, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- Ten-voter specialization: `1 - V_10 ≤ 10 (1 - p)`. -/
theorem ten_voter_union_bound {A : Type*} [Fintype A] (π : Law (Option A)) (a : A) :
    1 - voteAccuracy π 10 a ≤ 10 * (1 - π.mass (some a)) := by
  simpa using one_sub_voteAccuracy_le π a (N := 10) (by norm_num)

/-! ## Hump identification on the binary 10/5 law (Doc B A5.1) -/

open SEKernel.EpistemicPayoff in
/-- Doc B A5.1: on the binary 10-draw / 5-posted law, actual prefix reach minus
actual ten-voter accuracy is `hump10 p`. -/
theorem binary_hump_identification (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) :
    reachProbability π 10 5 a - voteAccuracy π 10 a = hump10 (π.mass (some a)) := by
  have hft := binary_fair_ties π a hnone (k := 5) (by norm_num)
  norm_num at hft
  rw [reach_prefix_probability π 10 5 (by norm_num) a, hft,
    voteAccuracy_eq_binaryVotePoly π a hnone (by norm_num), binaryVotePoly_nine,
    hump_reach_vote_polynomial]
  rfl

/-- `V_10 = V_9 = binaryVote9 p` on the binary law. -/
theorem binary_ten_vote_eq_nine (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) :
    voteAccuracy π 10 a = SEKernel.EpistemicPayoff.binaryVote9 (π.mass (some a)) ∧
      voteAccuracy π 9 a = SEKernel.EpistemicPayoff.binaryVote9 (π.mass (some a)) := by
  rw [voteAccuracy_eq_binaryVotePoly π a hnone (by norm_num), binaryVotePoly_ten,
    voteAccuracy_eq_binaryVotePoly π a hnone (by norm_num), binaryVotePoly_nine]
  exact ⟨rfl, rfl⟩

/-- Point-mass law. -/
def pointLaw {X : Type*} [Fintype X] [DecidableEq X] (x : X) : Law X where
  mass y := if y = x then 1 else 0
  nonneg y := by split_ifs <;> norm_num
  total := by simp

open SEKernel.EpistemicPayoff

/-- A prefix-only response kernel: the response law at a full comparator word is a
kernel applied to the actual posted prefix, so its output (and its internal
randomness) depends on the first `k` draws only. -/
def prefixLift {N k : ℕ} {A : Type*} [Fintype A] (hk : k ≤ N)
    (R : ResponseKernel (OrderedWord k A) A) : ResponseKernel (OrderedWord N A) A :=
  fun z => R (postedWord z k hk)

/-- The ideal recognizer on the posted prefix: it outputs the correct answer exactly
when the prefix contains it, and abstains otherwise. -/
noncomputable def idealRecognizer {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (a : A) :
    ResponseKernel (OrderedWord k A) A := by
  classical
  exact fun w => if reaches w k a then pointLaw (some a) else pointLaw none

open scoped Classical in
/-- Correctness of the lifted ideal recognizer is the reach indicator. -/
theorem idealRecognizer_correctness {N k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (hk : k ≤ N) (a : A) (z : OrderedWord N A) :
    correctness (prefixLift hk (idealRecognizer a)) a z =
      if reaches z k a then 1 else 0 := by
  classical
  unfold correctness prefixLift idealRecognizer
  by_cases h : reaches z k a
  · have h' : reaches (postedWord z k hk) k a := (postedWord_reaches_full z k hk a).2 h
    simp [h, h', pointLaw]
  · have h' : ¬ reaches (postedWord z k hk) k a := fun h'' =>
      h ((postedWord_reaches_full z k hk a).1 h'')
    simp [h, h', pointLaw]

/-- The ideal recognizer's accuracy is the actual prefix reach probability. -/
theorem idealRecognizer_accuracy {A : Type*} [Fintype A] [DecidableEq A]
    (π : Law (Option A)) {N k : ℕ} (hk : k ≤ N) (a : A) :
    (iidWordLaw π N).expect (correctness (prefixLift hk (idealRecognizer a)) a) =
      reachProbability π N k a := by
  classical
  have hc : correctness (prefixLift hk (idealRecognizer a)) a =
      fun z => if reaches z k a then (1 : ℝ) else 0 := by
    funext z; rw [idealRecognizer_correctness hk a z]
  rw [hc, Law.expect_indicator]
  rfl

/-- Doc B A5.1, premium form: the actual ideal prefix recognizer's premium over the
actual ten-voter comparator is exactly `hump10 p`. -/
theorem idealRecognizer_premium_hump (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) (default : Cell → ℝ) :
    (comparatorModel (iidWordLaw π 10)
      (fun z => correctVote z a) (fun z => reaches z 5 a)).premium
        (responseRates (iidWordLaw π 10)
          (fun z => correctVote z a) (fun z => reaches z 5 a)
          (prefixLift (by norm_num) (idealRecognizer (k := 5) a)) a default) =
      hump10 (π.mass (some a)) := by
  rw [ordered_response_premium_eq, idealRecognizer_accuracy,
    binary_hump_identification π a hnone]

/-- The hump polynomial is nonnegative on `[0,1]`. -/
theorem hump10_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ hump10 p := by
  rw [hump_forms_equal]
  unfold hump10Factored
  have hq : 0 ≤ 1 - p := by linarith
  positivity

/-- Doc B (A5.2) for the actual law: `0 ≤ D ≤ min (5p) (10(1-p))`. -/
theorem binary_hump_bounds (π : Law (Option Bool)) (a : Bool) (hnone : π.mass none = 0) :
    0 ≤ hump10 (π.mass (some a)) ∧ hump10 (π.mass (some a)) ≤ 5 * π.mass (some a) ∧
      hump10 (π.mass (some a)) ≤ 10 * (1 - π.mass (some a)) := by
  have hp := π.nonneg (some a)
  have hp' : π.mass (some a) ≤ 1 := Law1.coord_le_one π.nonneg π.total (some a)
  have hid := binary_hump_identification π a hnone
  have hV : 0 ≤ voteAccuracy π 10 a := (iidWordLaw π 10).prob_nonneg _
  have hU := ten_voter_union_bound π a
  have hR : reachProbability π 10 5 a = 1 - (1 - π.mass (some a)) ^ 5 :=
    reach_prefix_probability π 10 5 (by norm_num) a
  have hB := one_add_mul_le_pow (show (-2 : ℝ) ≤ -π.mass (some a) by linarith) 5
  have hq : 0 ≤ (1 - π.mass (some a)) ^ 5 := pow_nonneg (by linarith) 5
  refine ⟨hump10_nonneg hp hp', ?_, ?_⟩
  · have : (1 + -π.mass (some a)) = 1 - π.mass (some a) := by ring
    rw [this] at hB
    push_cast at hB
    linarith
  · linarith


/-- Answer law: the correct answer with probability `r`, abstention otherwise. -/
noncomputable def answerWithProb {A : Type*} [Fintype A] [DecidableEq A] (a : A) (r : ℝ)
    (hr : 0 ≤ r) (hr' : r ≤ 1) : Law (Option A) where
  mass x := if x = some a then r else if x = none then 1 - r else 0
  nonneg x := by split_ifs <;> linarith
  total := by
    rw [Fintype.sum_option]
    simp

/-- The `r`-recognizer of Doc B (A5.3): on a posted prefix containing the correct answer
it outputs that answer with probability `r`, and it abstains otherwise. -/
noncomputable def rRecognizer {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (a : A)
    (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1) : ResponseKernel (OrderedWord k A) A := by
  classical
  exact fun w => if reaches w k a then answerWithProb a r hr hr' else pointLaw none

/-- The `r`-recognizer's accuracy is `r` times the actual reach probability. -/
theorem rRecognizer_accuracy {A : Type*} [Fintype A] [DecidableEq A]
    (π : Law (Option A)) {N k : ℕ} (hk : k ≤ N) (a : A) (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1) :
    (iidWordLaw π N).expect (correctness (prefixLift hk (rRecognizer a r hr hr')) a) =
      r * reachProbability π N k a := by
  classical
  have hc : correctness (prefixLift hk (rRecognizer a r hr hr')) a =
      fun z => r * (if reaches z k a then (1 : ℝ) else 0) := by
    funext z
    unfold correctness prefixLift rRecognizer
    by_cases h : reaches z k a
    · have h' : reaches (postedWord z k hk) k a := (postedWord_reaches_full z k hk a).2 h
      simp [h, h', answerWithProb]
    · have h' : ¬ reaches (postedWord z k hk) k a := fun h'' =>
        h ((postedWord_reaches_full z k hk a).1 h'')
      simp [h, h', pointLaw]
  rw [hc, Law.expect_const_mul, Law.expect_indicator]
  rfl

/-- Doc B (A5.3)-(A5.4) on the binary 10/5 law: `D_r = r R - V`, and for `0 < p < 1`
the premium is positive exactly when `r > V/R`, where `V/R < 1`. -/
theorem rRecognizer_premium (π : Law (Option Bool)) (a : Bool) (hnone : π.mass none = 0)
    (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1) (default : Cell → ℝ) :
    (comparatorModel (iidWordLaw π 10)
      (fun z => correctVote z a) (fun z => reaches z 5 a)).premium
        (responseRates (iidWordLaw π 10)
          (fun z => correctVote z a) (fun z => reaches z 5 a)
          (prefixLift (by norm_num) (rRecognizer (k := 5) a r hr hr')) a default) =
      r * reachPolynomial 5 (π.mass (some a)) - binaryVote9 (π.mass (some a)) := by
  rw [ordered_response_premium_eq, rRecognizer_accuracy,
    reach_prefix_probability π 10 5 (by norm_num) a, (binary_ten_vote_eq_nine π a hnone).1]
  rfl

/-- Doc B (A5.4): for `0 < p < 1`, `D_r > 0 ↔ V/R < r`, and `V/R < 1`. -/
theorem rRecognizer_premium_pos_iff (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) (hp0 : 0 < π.mass (some a)) (hp1 : π.mass (some a) < 1)
    (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1) (default : Cell → ℝ) :
    (0 < (comparatorModel (iidWordLaw π 10)
      (fun z => correctVote z a) (fun z => reaches z 5 a)).premium
        (responseRates (iidWordLaw π 10)
          (fun z => correctVote z a) (fun z => reaches z 5 a)
          (prefixLift (by norm_num) (rRecognizer (k := 5) a r hr hr')) a default) ↔
      binaryVote9 (π.mass (some a)) / reachPolynomial 5 (π.mass (some a)) < r) ∧
      binaryVote9 (π.mass (some a)) / reachPolynomial 5 (π.mass (some a)) < 1 := by
  have hR : 0 < reachPolynomial 5 (π.mass (some a)) := by
    unfold reachPolynomial
    have h1 : (1 - π.mass (some a)) ^ 5 < 1 :=
      pow_lt_one₀ (by linarith) (by linarith) (by norm_num)
    linarith
  have hH := hump_positive hp0 hp1
  rw [hump_reach_vote_polynomial] at hH
  rw [rRecognizer_premium π a hnone r hr hr' default]
  refine ⟨recognizer_threshold _ _ _ hR, ?_⟩
  rw [div_lt_one hR]
  linarith

/-! ## Prefix realizability (Doc B A5.1 compatibility restriction, strengthened) -/

/-- Atom mass of the IID word law. -/
theorem iidWordLaw_mass {A : Type*} [Fintype A] (π : Law (Option A)) {N : ℕ}
    (z : OrderedWord N A) : (iidWordLaw π N).mass z = ∏ i, π.mass (z i) := rfl

/-- With no abstention mass, every positive-mass word is readable. -/
theorem readable_of_mass_pos {A : Type*} [Fintype A] (π : Law (Option A))
    (hnone : π.mass none = 0) {N : ℕ} (z : OrderedWord N A)
    (hz : 0 < (iidWordLaw π N).mass z) (i : Fin N) : z i ≠ none := by
  intro h
  have h0 : (iidWordLaw π N).mass z = 0 := by
    rw [iidWordLaw_mass]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, hnone])
  linarith

/-- An atom's mass bounds the probability of any event containing it. -/
theorem mass_le_prob {Ω : Type*} [Fintype Ω] (L : Law Ω) (E : Ω → Prop) (ω : Ω)
    (h : E ω) : L.mass ω ≤ L.prob E := by
  classical
  unfold Law.prob
  calc L.mass ω = if E ω then L.mass ω else 0 := by simp [h]
    _ ≤ ∑ ω', if E ω' then L.mass ω' else 0 :=
      Finset.single_le_sum (f := fun ω' => if E ω' then L.mass ω' else 0)
        (fun ω' _ => by dsimp only; split_ifs; exact L.nonneg ω'; rfl) (Finset.mem_univ ω)

/-- Full conditional mass on a cell forces the response to be one on its positive atoms. -/
theorem eq_one_of_responseMass_eq_cellMass {Ω C : Type*} [Fintype Ω] (L : Law Ω)
    (cell : Ω → C) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) (c : C)
    (h : responseMass L cell w c = cellMass L cell c) (ω : Ω) (hc : cell ω = c)
    (hm : 0 < L.mass ω) : w ω = 1 := by
  classical
  have hdiff : cellMass L cell c - responseMass L cell w c =
      ∑ ω', L.mass ω' * (if cell ω' = c then 1 - w ω' else 0) := by
    unfold cellMass responseMass Law.prob Law.expect Law1.mean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω' _
    dsimp only
    by_cases hc' : cell ω' = c
    · simp only [hc', if_true]; ring
    · simp only [hc', if_false]; ring
  have hz : ∑ ω', L.mass ω' * (if cell ω' = c then 1 - w ω' else 0) = 0 := by
    rw [← hdiff, h, sub_self]
  have hnn : ∀ ω' ∈ (Finset.univ : Finset Ω),
      0 ≤ L.mass ω' * (if cell ω' = c then 1 - w ω' else 0) := by
    intro ω' _
    apply mul_nonneg (L.nonneg ω')
    split_ifs
    · linarith [(hw ω').2]
    · exact le_refl 0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz ω (Finset.mem_univ ω)
  rw [if_pos hc] at hterm
  rcases mul_eq_zero.1 hterm with h1 | h1
  · linarith
  · linarith

/-- Conversely, a response equal to one on every positive atom of a cell has full mass there. -/
theorem responseMass_eq_cellMass_of_eq_one {Ω C : Type*} [Fintype Ω] (L : Law Ω)
    (cell : Ω → C) (w : Ω → ℝ) (c : C)
    (h : ∀ ω, cell ω = c → 0 < L.mass ω → w ω = 1) :
    responseMass L cell w c = cellMass L cell c := by
  classical
  unfold cellMass responseMass Law.prob Law.expect Law1.mean
  apply Finset.sum_congr rfl
  intro ω _
  dsimp only
  by_cases hc : cell ω = c
  · simp only [hc, if_true]
    rcases (L.nonneg ω).lt_or_eq with hm | hm
    · rw [h ω hc hm, mul_one]
    · rw [← hm, zero_mul]
  · simp only [hc, if_false, mul_zero]

/-- A strict readable count majority is the actual first-appearance winner. -/
theorem strict_count_winner {N : ℕ} {A : Type*} (z : OrderedWord N A) (a : A)
    (hpos : 0 < labelCount z (some a))
    (hstrict : ∀ b, b ≠ a → labelCount z (some b) < labelCount z (some a)) :
    correctVote z a := by
  classical
  unfold correctVote
  cases he : plurality z with
  | none =>
    have hall := (plurality_eq_none_iff z).1 he
    obtain ⟨i, hi⟩ := (labelCount_pos_iff z (some a)).1 hpos
    exact absurd hi (by rw [hall i]; simp)
  | some b =>
    by_cases h : b = a
    · rw [h]
    · have hd := plurality_dominates_readable z b he a
      have hs := hstrict b h
      omega

/-- Extend a posted prefix by correct answers in every suffix position. -/
def extendCorrect {N k : ℕ} {A : Type*} (a : A) (w : OrderedWord k A) : OrderedWord N A :=
  fun i => if h : i.val < k then w ⟨i.val, h⟩ else some a

/-- The posted prefix of the extension is the original prefix. -/
theorem postedWord_extendCorrect {N k : ℕ} {A : Type*} (hk : k ≤ N) (a : A)
    (w : OrderedWord k A) : postedWord (extendCorrect (N := N) a w) k hk = w := by
  funext i
  simp [postedWord, extendCorrect, i.isLt]

/-- There are `N - k` unposted positions. -/
theorem suffixPositions_card {N k : ℕ} (hk : k ≤ N) :
    (Finset.univ.filter (fun i : Fin N => ¬ i.val < k)).card = N - k := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun i : Fin N => i.val < k)
  rw [prefixPositions_card hk, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- The extension carries at least `N - k + 1` correct answers. -/
theorem extendCorrect_count {N k : ℕ} {A : Type*} (hk : k ≤ N) (a : A)
    (w : OrderedWord k A) (hw : reaches w k a) :
    N - k + 1 ≤ labelCount (extendCorrect (N := N) a w) (some a) := by
  classical
  obtain ⟨i0, hi0, hw0⟩ := hw
  let j0 : Fin N := ⟨i0.val, lt_of_lt_of_le i0.isLt hk⟩
  let S := Finset.univ.filter (fun i : Fin N => ¬ i.val < k)
  have hj0 : j0 ∉ S := by simp [S, j0, i0.isLt]
  have hsub : insert j0 S ⊆
      Finset.univ.filter (fun i => extendCorrect (N := N) a w i = some a) := by
    intro i hi
    rw [Finset.mem_insert] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with rfl | hi
    · simp [extendCorrect, j0, i0.isLt]
      exact hw0
    · have hik : ¬ i.val < k := by simpa [S] using hi
      simp [extendCorrect, hik]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hj0, suffixPositions_card hk] at hcard
  unfold labelCount
  exact hcard

/-- A readable prefix reaching the correct answer, followed by correct answers, wins
the full vote whenever `2k ≤ N + 1` (in particular at `N = 10`, `k = 5`). -/
theorem extendCorrect_vote {N k : ℕ} (hk : k ≤ N) (hNk : 2 * k ≤ N + 1) (a : Bool)
    (w : OrderedWord k Bool) (hw : reaches w k a) :
    correctVote (extendCorrect (N := N) a w) a := by
  have hc := extendCorrect_count hk a w hw
  apply strict_count_winner
  · omega
  · intro b hb
    have hd := labelCount_disjoint_sum_le_length (extendCorrect (N := N) a w) (some a) (some b)
      (by simpa using (Ne.symm hb))
    omega

/-- For `0 < p < 1`, the extension of a readable prefix has positive mass. -/
theorem extendCorrect_mass_pos {N k : ℕ} (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) (hp0 : 0 < π.mass (some a)) (hp1 : π.mass (some a) < 1)
    (w : OrderedWord k Bool) (hread : ∀ i, w i ≠ none) :
    0 < (iidWordLaw π N).mass (extendCorrect (N := N) a w) := by
  have hq : 0 < π.mass (some (!a)) := by
    rw [wrong_mass_of_no_abstention π a hnone]; linarith
  have hpos : ∀ x : Option Bool, x ≠ none → 0 < π.mass x := by
    intro x hx
    cases x with
    | none => exact absurd rfl hx
    | some b =>
      by_cases hb : b = a
      · rw [hb]; exact hp0
      · have : b = !a := by cases a <;> cases b <;> simp_all
        rw [this]; exact hq
  rw [iidWordLaw_mass]
  apply Finset.prod_pos
  intro i _
  apply hpos
  unfold extendCorrect
  split_ifs
  · exact hread _
  · simp


/-- The post cell is "vote fails, correct answer posted". -/
theorem cellOf_post_iff (v r : Prop) : cellOf v r = .post ↔ ¬ v ∧ r := by
  classical
  by_cases hv : v <;> by_cases hr : r <;> simp [cellOf, hv, hr]

/-- For `p > 0` and `N ≥ 1` the keep cell has positive mass (all-correct word). -/
theorem keep_cell_mass_pos {A : Type*} [Fintype A] (π : Law (Option A)) (a : A)
    (hp0 : 0 < π.mass (some a)) {N : ℕ} (k : ℕ) (hN : 0 < N) :
    0 < cellMass (iidWordLaw π N)
      (fun z => cellOf (correctVote z a) (reaches z k a)) .keep := by
  let zs : OrderedWord N A := fun _ => some a
  have hv : correctVote zs a := all_correct_vote zs a hN (fun _ => rfl)
  have hm : 0 < (iidWordLaw π N).mass zs := by
    rw [iidWordLaw_mass]
    exact Finset.prod_pos (fun i _ => hp0)
  exact lt_of_lt_of_le hm (mass_le_prob _ _ zs ((cellOf_keep_iff _ _).2 hv))

/-- One correct answer first, then only wrong answers: a positive-mass post-cell word. -/
def oneCorrectFirst {N : ℕ} (a : Bool) : OrderedWord N Bool :=
  fun i => if i.val = 0 then some a else some (!a)

/-- With `N ≥ 3` the vote fails on `oneCorrectFirst`. -/
theorem oneCorrectFirst_not_vote {N : ℕ} (a : Bool) (hN : 3 ≤ N) :
    ¬ correctVote (oneCorrectFirst (N := N) a) a := by
  classical
  intro hv
  have hd := plurality_dominates_readable _ a hv (!a)
  have h1 : labelCount (oneCorrectFirst (N := N) a) (some a) ≤ 1 := by
    unfold labelCount
    refine le_trans (Finset.card_le_card (t := ({⟨0, by omega⟩} : Finset (Fin N))) ?_)
      (by rw [Finset.card_singleton])
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Finset.mem_singleton]
    by_cases h0 : i.val = 0
    · exact Fin.ext h0
    · simp [oneCorrectFirst, h0] at hi
  have h2 : 2 ≤ labelCount (oneCorrectFirst (N := N) a) (some (!a)) := by
    unfold labelCount
    have hne : (⟨1, by omega⟩ : Fin N) ≠ ⟨2, by omega⟩ := by simp
    refine le_trans (le_of_eq (Finset.card_pair hne).symm)
      (Finset.card_le_card ?_)
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with rfl | rfl <;> simp [oneCorrectFirst]
  omega

/-- `oneCorrectFirst` reaches the correct answer in any nonempty prefix. -/
theorem oneCorrectFirst_reaches {N k : ℕ} (a : Bool) (hk1 : 1 ≤ k) (hN : 0 < N) :
    reaches (oneCorrectFirst (N := N) a) k a :=
  ⟨⟨0, hN⟩, by simp; omega, by simp [oneCorrectFirst]⟩

/-- For `0 < p < 1`, `k ≥ 1`, `N ≥ 3`, the post cell has positive mass. -/
theorem post_cell_mass_pos (π : Law (Option Bool)) (a : Bool) (hnone : π.mass none = 0)
    (hp0 : 0 < π.mass (some a)) (hp1 : π.mass (some a) < 1) {N k : ℕ} (hk1 : 1 ≤ k)
    (hN : 3 ≤ N) :
    0 < cellMass (iidWordLaw π N)
      (fun z => cellOf (correctVote z a) (reaches z k a)) .post := by
  have hq : 0 < π.mass (some (!a)) := by
    rw [wrong_mass_of_no_abstention π a hnone]; linarith
  have hm : 0 < (iidWordLaw π N).mass (oneCorrectFirst a) := by
    rw [iidWordLaw_mass]
    apply Finset.prod_pos
    intro i _
    unfold oneCorrectFirst
    split_ifs
    · exact hp0
    · exact hq
  exact lt_of_lt_of_le hm (mass_le_prob _ _ _ ((cellOf_post_iff _ _).2
    ⟨oneCorrectFirst_not_vote a hN, oneCorrectFirst_reaches a hk1 (by omega)⟩))

/-- Doc B A5.1 compatibility restriction (referee-strengthened), general binary form.
For a prefix-only response (`prefixLift`), conditional keep rate `1` forces
correctness `1` on every readable posted prefix containing the correct answer, hence
conditional post rate `1`. -/
theorem prefix_keep_one_forces_post_one (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) (hp0 : 0 < π.mass (some a)) (hp1 : π.mass (some a) < 1)
    {N k : ℕ} (hk : k ≤ N) (hk1 : 1 ≤ k) (hNk : 2 * k ≤ N + 1) (hN3 : 3 ≤ N)
    (R : ResponseKernel (OrderedWord k Bool) Bool) (default : Cell → ℝ)
    (hkeep : responseRates (iidWordLaw π N) (fun z => correctVote z a)
      (fun z => reaches z k a) (prefixLift hk R) a default .keep = 1) :
    (∀ w : OrderedWord k Bool, (∀ i, w i ≠ none) → reaches w k a →
        correctness R a w = 1) ∧
      responseRates (iidWordLaw π N) (fun z => correctVote z a)
        (fun z => reaches z k a) (prefixLift hk R) a default .post = 1 := by
  set L := iidWordLaw π N
  set cell : OrderedWord N Bool → Cell := fun z => cellOf (correctVote z a) (reaches z k a)
  set wf := correctness (prefixLift hk R) a
  have hkpos : 0 < cellMass L cell .keep := keep_cell_mass_pos π a hp0 k (by omega)
  have hrate : responseRates L (fun z => correctVote z a) (fun z => reaches z k a)
      (prefixLift hk R) a default .keep = responseMass L cell wf .keep / cellMass L cell .keep := by
    unfold responseRates conditionalRate
    rw [if_neg hkpos.ne']
  have hfull : responseMass L cell wf .keep = cellMass L cell .keep := by
    rw [hrate] at hkeep
    exact (div_eq_one_iff_eq hkpos.ne').1 hkeep
  have hone := eq_one_of_responseMass_eq_cellMass L cell wf
    (correctness_bounds (prefixLift hk R) a) .keep hfull
  have hprefix : ∀ w : OrderedWord k Bool, (∀ i, w i ≠ none) → reaches w k a →
      correctness R a w = 1 := by
    intro w hread hreach
    have hv := extendCorrect_vote hk hNk a w hreach
    have hcell : cell (extendCorrect (N := N) a w) = .keep := (cellOf_keep_iff _ _).2 hv
    have hm := extendCorrect_mass_pos (N := N) π a hnone hp0 hp1 w hread
    have h1 := hone _ hcell hm
    simpa only [wf, correctness, prefixLift, postedWord_extendCorrect] using h1
  refine ⟨hprefix, ?_⟩
  have hppos : 0 < cellMass L cell .post := post_cell_mass_pos π a hnone hp0 hp1 hk1 hN3
  have hpost : responseMass L cell wf .post = cellMass L cell .post := by
    apply responseMass_eq_cellMass_of_eq_one
    intro z hz hm
    have hr : reaches z k a := ((cellOf_post_iff _ _).1 hz).2
    have hread : ∀ i, postedWord z k hk i ≠ none := fun i =>
      readable_of_mass_pos π hnone z hm _
    exact hprefix _ hread ((postedWord_reaches_full z k hk a).2 hr)
  unfold responseRates conditionalRate
  rw [if_neg hppos.ne']
  exact (div_eq_one_iff_eq hppos.ne').2 hpost

/-- The 10-draw / 5-posted specialization of the realizability restriction. -/
theorem binary_10_5_keep_one_forces_post_one (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) (hp0 : 0 < π.mass (some a)) (hp1 : π.mass (some a) < 1)
    (R : ResponseKernel (OrderedWord 5 Bool) Bool) (default : Cell → ℝ)
    (hkeep : responseRates (iidWordLaw π 10) (fun z => correctVote z a)
      (fun z => reaches z 5 a) (prefixLift (by norm_num) R) a default .keep = 1) :
    (∀ w : OrderedWord 5 Bool, (∀ i, w i ≠ none) → reaches w 5 a →
        correctness R a w = 1) ∧
      responseRates (iidWordLaw π 10) (fun z => correctVote z a)
        (fun z => reaches z 5 a) (prefixLift (by norm_num) R) a default .post = 1 :=
  prefix_keep_one_forces_post_one π a hnone hp0 hp1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) R default hkeep

/-- Referee form: on the binary 10/5 law with `0 < p < 1`, no prefix-only response has
conditional keep rate `1` and conditional post rate below `1`. -/
theorem binary_10_5_no_keep_one_post_lt_one (π : Law (Option Bool)) (a : Bool)
    (hnone : π.mass none = 0) (hp0 : 0 < π.mass (some a)) (hp1 : π.mass (some a) < 1)
    (R : ResponseKernel (OrderedWord 5 Bool) Bool) (default : Cell → ℝ) :
    ¬ (responseRates (iidWordLaw π 10) (fun z => correctVote z a)
        (fun z => reaches z 5 a) (prefixLift (by norm_num) R) a default .keep = 1 ∧
      responseRates (iidWordLaw π 10) (fun z => correctVote z a)
        (fun z => reaches z 5 a) (prefixLift (by norm_num) R) a default .post < 1) := by
  rintro ⟨hkeep, hpost⟩
  have h := (binary_10_5_keep_one_forces_post_one π a hnone hp0 hp1 R default hkeep).2
  linarith


/-! ## Three readable labels: nonmodal counterexamples (Doc B A3.5, Doc A A3.5) -/

/-- Count profile with readable counts `x, y, z` on labels `0, 1, 2` and no abstention. -/
def prof3 (x y z : ℕ) : Option (Fin 3) → ℕ
  | none => 0
  | some i => ![x, y, z] i

/-- First-appearance tie weight of label `0` on the readable count vector `(x, y, z)`. -/
noncomputable def tieWeight3 (x y z : ℕ) : ℝ :=
  if 0 < x ∧ y ≤ x ∧ z ≤ x then
    1 / (1 + (if 0 < y ∧ x ≤ y ∧ z ≤ y then 1 else 0) +
      (if 0 < z ∧ x ≤ z ∧ y ≤ z then 1 else 0))
  else 0

/-- Multinomial coefficient of a three-label profile. -/
theorem multinomial_prof3 (x y z : ℕ) :
    Nat.multinomial Finset.univ (prof3 x y z) = (x + y + z)! / (x ! * y ! * z !) := by
  rw [Nat.multinomial, Fintype.sum_option, Fintype.prod_option, Fin.sum_univ_three,
    Fin.prod_univ_three]
  simp [prof3, add_assoc, mul_assoc]

/-- Readable modes of a three-label profile. -/
theorem mem_readableModes_prof3 (x y z : ℕ) (i : Fin 3) :
    i ∈ readableModes (prof3 x y z) ↔
      0 < ![x, y, z] i ∧ ∀ b, ![x, y, z] b ≤ ![x, y, z] i := by
  simp [readableModes, prof3]

/-- Number of readable modes of a three-label profile. -/
theorem card_readableModes_prof3 (x y z : ℕ) :
    ((readableModes (prof3 x y z)).card : ℝ) =
      (if 0 < x ∧ y ≤ x ∧ z ≤ x then 1 else 0) + (if 0 < y ∧ x ≤ y ∧ z ≤ y then 1 else 0) +
        (if 0 < z ∧ x ≤ z ∧ y ≤ z then 1 else 0) := by
  classical
  have h : readableModes (prof3 x y z) =
      Finset.univ.filter (fun i : Fin 3 => 0 < ![x, y, z] i ∧ ∀ b, ![x, y, z] b ≤ ![x, y, z] i) := by
    ext i
    rw [mem_readableModes_prof3]
    simp
  rw [h, Finset.card_filter, Fin.sum_univ_three]
  push_cast
  simp [Fin.forall_fin_succ]


/-- The actual tie factor of the count formula for label `0`. -/
theorem tie_prof3 (x y z : ℕ) (inst : Decidable ((0 : Fin 3) ∈ readableModes (prof3 x y z))) :
    (if (0 : Fin 3) ∈ readableModes (prof3 x y z) then
        1 / ((readableModes (prof3 x y z)).card : ℝ) else 0) = tieWeight3 x y z := by
  rw [card_readableModes_prof3]
  unfold tieWeight3
  by_cases h : 0 < x ∧ y ≤ x ∧ z ≤ x
  · have hm : (0 : Fin 3) ∈ readableModes (prof3 x y z) := by
      rw [mem_readableModes_prof3]; simp [Fin.forall_fin_succ]; omega
    rw [if_pos hm, if_pos h, if_pos h]
  · have hm : (0 : Fin 3) ∉ readableModes (prof3 x y z) := by
      rw [mem_readableModes_prof3]; simp [Fin.forall_fin_succ]; omega
    rw [if_neg hm, if_neg h]

/-- Readable pairs `(x, y)` with `x + y ≤ N`; the third count is `N - x - y`. -/
def pairs3 (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun xy => xy.1 + xy.2 ≤ N)

/-- With no abstention mass, the count-profile sum reduces to readable pairs. -/
theorem sum_validCountProfiles_three (N : ℕ) (F : (Option (Fin 3) → ℕ) → ℝ)
    (hF : ∀ c, c none ≠ 0 → F c = 0) :
    ∑ c ∈ validCountProfiles (Fin 3) N, F c =
      ∑ xy ∈ pairs3 N, F (prof3 xy.1 xy.2 (N - xy.1 - xy.2)) := by
  classical
  have hinj : Set.InjOn (fun xy : ℕ × ℕ => prof3 xy.1 xy.2 (N - xy.1 - xy.2))
      (pairs3 N : Set (ℕ × ℕ)) := by
    intro u _ v _ h
    have h0 := congrFun h (some 0)
    have h1 := congrFun h (some 1)
    simp [prof3] at h0 h1
    exact Prod.ext h0 h1
  rw [← Finset.sum_image hinj]
  symm
  apply Finset.sum_subset
  · intro c hc
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.1 hc
    have hle : xy.1 + xy.2 ≤ N := (Finset.mem_filter.1 hxy).2
    simp only [validCountProfiles, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
      and_true]
    rw [Fintype.sum_option, Fin.sum_univ_three]
    simp [prof3]
    omega
  · intro c hc hnot
    by_cases h0 : c none = 0
    · exfalso
      apply hnot
      have hsum : ∑ q, c q = N := by
        simpa [validCountProfiles, Finset.mem_piAntidiag] using hc
      rw [Fintype.sum_option, Fin.sum_univ_three, h0] at hsum
      refine Finset.mem_image.2 ⟨(c (some 0), c (some 1)), ?_, ?_⟩
      · simp only [pairs3, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · funext q
        cases q with
        | none => simp [prof3, h0]
        | some i =>
          fin_cases i
          · simp [prof3]
          · simp [prof3]
          · simp [prof3]; omega
    · exact hF c h0

/-- Doc B A3.1 on three readable labels with no abstention (label `0` correct). -/
theorem three_label_vote_formula (π : Law (Option (Fin 3))) (hnone : π.mass none = 0)
    (N : ℕ) :
    voteAccuracy π N 0 = ∑ xy ∈ pairs3 N,
      (((xy.1 + xy.2 + (N - xy.1 - xy.2))! / (xy.1 ! * xy.2 ! * (N - xy.1 - xy.2)!) : ℕ) : ℝ) *
        (π.mass (some 0) ^ xy.1 * π.mass (some 1) ^ xy.2 *
          π.mass (some 2) ^ (N - xy.1 - xy.2)) *
        tieWeight3 xy.1 xy.2 (N - xy.1 - xy.2) := by
  classical
  rw [plurality_multinomial_formula π 0, sum_validCountProfiles_three N]
  · apply Finset.sum_congr rfl
    intro xy _
    rw [multinomial_prof3, tie_prof3 _ _ _ _, Fintype.prod_option, Fin.prod_univ_three]
    simp [prof3, mul_assoc]
  · intro c hc
    rw [Fintype.prod_option, hnone, zero_pow hc, zero_mul]
    ring


/-- Readable masses sum to one when abstention has mass zero. -/
theorem three_label_total (π : Law (Option (Fin 3))) (hnone : π.mass none = 0) :
    π.mass (some 0) + π.mass (some 1) + π.mass (some 2) = 1 := by
  have ht := π.total
  rw [Fintype.sum_option, Fin.sum_univ_three, hnone] at ht
  linarith

/-- Doc B A3.5: `V_2 = p` on three readable labels with no abstention. -/
theorem three_label_V2 (π : Law (Option (Fin 3))) (hnone : π.mass none = 0) :
    voteAccuracy π 2 0 = π.mass (some 0) := by
  have ht := three_label_total π hnone
  rw [three_label_vote_formula π hnone]
  simp [pairs3, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ, tieWeight3,
    Nat.factorial]
  norm_num
  linear_combination π.mass (some 0) * ht

/-- Doc B A3.5: `V_3 = p^3 + 3p^2(q+r) + 2pqr`. -/
theorem three_label_V3 (π : Law (Option (Fin 3))) (hnone : π.mass none = 0) :
    voteAccuracy π 3 0 = π.mass (some 0) ^ 3 +
      3 * π.mass (some 0) ^ 2 * (π.mass (some 1) + π.mass (some 2)) +
      2 * π.mass (some 0) * π.mass (some 1) * π.mass (some 2) := by
  rw [three_label_vote_formula π hnone]
  simp [pairs3, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ, tieWeight3,
    Nat.factorial]
  norm_num
  ring

/-- Doc B A3.5: `V_4 = p^4 + 4p^3(q+r) + 3p^2(q^2+r^2) + 12p^2qr`. -/
theorem three_label_V4 (π : Law (Option (Fin 3))) (hnone : π.mass none = 0) :
    voteAccuracy π 4 0 = π.mass (some 0) ^ 4 +
      4 * π.mass (some 0) ^ 3 * (π.mass (some 1) + π.mass (some 2)) +
      3 * π.mass (some 0) ^ 2 * (π.mass (some 1) ^ 2 + π.mass (some 2) ^ 2) +
      12 * π.mass (some 0) ^ 2 * π.mass (some 1) * π.mass (some 2) := by
  rw [three_label_vote_formula π hnone]
  simp [pairs3, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ, tieWeight3,
    Nat.factorial]
  norm_num
  ring


/-- Three readable labels with masses `p, q, r` on labels `0, 1, 2`; abstention mass zero. -/
noncomputable def threeLabelLaw (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hs : p + q + r = 1) : Law (Option (Fin 3)) where
  mass x := match x with
    | none => 0
    | some i => ![p, q, r] i
  nonneg x := by
    cases x with
    | none => exact le_refl 0
    | some i => fin_cases i <;> simp [hp, hq, hr]
  total := by simp [Fintype.sum_option, Fin.sum_univ_three]; linarith

/-- Doc B Counterexample A3.5: correct `3/8`, wrong `1/8`, wrong `1/2`. -/
noncomputable def nonmodalLawB : Law (Option (Fin 3)) :=
  threeLabelLaw (3/8) (1/8) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Doc A (A3.5): correct `2/5`, wrong `1/2`, wrong `1/10`. -/
noncomputable def nonmodalLawA : Law (Option (Fin 3)) :=
  threeLabelLaw (2/5) (1/2) (1/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Doc B A3.5 through the actual count formula: `V_2 = 3/8`, `V_3 = 93/256`,
`V_4 = 189/512`; accuracy falls then rises, with a wrong strict mode. -/
theorem nonmodal_B_values :
    nonmodalLawB.mass none = 0 ∧
      voteAccuracy nonmodalLawB 2 0 = 3 / 8 ∧
      voteAccuracy nonmodalLawB 3 0 = 93 / 256 ∧
      voteAccuracy nonmodalLawB 4 0 = 189 / 512 ∧
      voteAccuracy nonmodalLawB 3 0 < voteAccuracy nonmodalLawB 2 0 ∧
      voteAccuracy nonmodalLawB 3 0 < voteAccuracy nonmodalLawB 4 0 ∧
      nonmodalLawB.mass (some 0) < nonmodalLawB.mass (some 2) ∧
      nonmodalLawB.mass (some 1) < nonmodalLawB.mass (some 2) := by
  have h0 : nonmodalLawB.mass none = 0 := rfl
  have m0 : nonmodalLawB.mass (some 0) = 3 / 8 := rfl
  have m1 : nonmodalLawB.mass (some 1) = 1 / 8 := rfl
  have m2 : nonmodalLawB.mass (some 2) = 1 / 2 := rfl
  rw [three_label_V2 _ h0, three_label_V3 _ h0, three_label_V4 _ h0, m0, m1, m2]
  norm_num [h0]

/-- Doc A (A3.5) through the actual count formula: `V_2 = 2/5`, `V_3 = 49/125`,
`V_4 = 2/5`; accuracy falls then rises, with a wrong strict mode. -/
theorem nonmodal_A_values :
    nonmodalLawA.mass none = 0 ∧
      voteAccuracy nonmodalLawA 2 0 = 2 / 5 ∧
      voteAccuracy nonmodalLawA 3 0 = 49 / 125 ∧
      voteAccuracy nonmodalLawA 4 0 = 2 / 5 ∧
      voteAccuracy nonmodalLawA 3 0 < voteAccuracy nonmodalLawA 2 0 ∧
      voteAccuracy nonmodalLawA 3 0 < voteAccuracy nonmodalLawA 4 0 ∧
      nonmodalLawA.mass (some 0) < nonmodalLawA.mass (some 1) ∧
      nonmodalLawA.mass (some 2) < nonmodalLawA.mass (some 1) := by
  have h0 : nonmodalLawA.mass none = 0 := rfl
  have m0 : nonmodalLawA.mass (some 0) = 2 / 5 := rfl
  have m1 : nonmodalLawA.mass (some 1) = 1 / 2 := rfl
  have m2 : nonmodalLawA.mass (some 2) = 1 / 10 := rfl
  rw [three_label_V2 _ h0, three_label_V3 _ h0, three_label_V4 _ h0, m0, m1, m2]
  norm_num [h0]


/-! ## Doc A A2 chance pickup -/

/-- Uniformly pick one of the `k` posted answers: the empirical law of the posted word. -/
noncomputable def uniformPick {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (hk0 : 0 < k) :
    ResponseKernel (OrderedWord k A) A := fun w =>
  { mass := fun x => (∑ i, if w i = x then (1 : ℝ) else 0) / k
    nonneg := fun x => div_nonneg
      (Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num) (Nat.cast_nonneg k)
    total := by
      rw [← Finset.sum_div, Finset.sum_comm]
      have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk0)
      simp [hk] }

/-- A single coordinate equals the correct answer with mass `p`. -/
theorem coord_eq_probability {A : Type*} [Fintype A] [DecidableEq A] (π : Law (Option A))
    (N : ℕ) (i : Fin N) (a : A) :
    (iidWordLaw π N).expect (fun z => if z i = some a then (1 : ℝ) else 0) =
      π.mass (some a) := by
  have h := Law.expect_pi_coord (fun _ : Fin N => π) i
    (fun x => if x = some a then (1 : ℝ) else 0)
  change (Law.pi (fun _ : Fin N => π)).expect _ = _
  rw [h]
  simp [Law.expect, Law1.mean]

/-- Doc A A2: uniformly selecting one of `k` posted IID answers has accuracy exactly `p`. -/
theorem uniformPick_accuracy {A : Type*} [Fintype A] [DecidableEq A] (π : Law (Option A))
    {N k : ℕ} (hk : k ≤ N) (hk0 : 0 < k) (a : A) :
    (iidWordLaw π N).expect (correctness (prefixLift hk (uniformPick (A := A) hk0)) a) =
      π.mass (some a) := by
  have hc : correctness (prefixLift hk (uniformPick (A := A) hk0)) a = fun z =>
      (∑ i : Fin k, (fun i : Fin k => fun z : OrderedWord N A =>
        if z ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ = some a then (1 : ℝ) else 0) i z) * (k : ℝ)⁻¹ := by
    funext z
    simp [correctness, prefixLift, uniformPick, postedWord, div_eq_mul_inv]
  rw [hc, Law.expect_mul_const, Law.expect_sum]
  simp only [coord_eq_probability, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk0)
  field_simp

/-- Doc A A2 chance-pickup law: correct mass `1/4`, wrong `3/4`, no abstention. -/
noncomputable def chanceLaw : Law (Option Bool) :=
  binaryReadableLaw (1 / 4) (3 / 4) 0 (by norm_num) (by norm_num) (le_refl 0) (by norm_num)

/-- Doc A A2: three-voter accuracy `5/32`, random-posted accuracy `1/4`, and premium
`3/32 > 0`, all on the actual law and the actual uniform-pick response kernel. -/
theorem chance_pickup_example (default : Cell → ℝ) :
    voteAccuracy chanceLaw 3 false = 5 / 32 ∧
      (iidWordLaw chanceLaw 3).expect
        (correctness (prefixLift le_rfl (uniformPick (A := Bool) (k := 3) (by norm_num))) false) =
        1 / 4 ∧
      (comparatorModel (iidWordLaw chanceLaw 3)
        (fun z => correctVote z false) (fun z => reaches z 3 false)).premium
          (responseRates (iidWordLaw chanceLaw 3)
            (fun z => correctVote z false) (fun z => reaches z 3 false)
            (prefixLift le_rfl (uniformPick (A := Bool) (k := 3) (by norm_num))) false default) =
        3 / 32 := by
  have h0 : chanceLaw.mass none = 0 := rfl
  have hp : chanceLaw.mass (some false) = 1 / 4 := rfl
  have hV : voteAccuracy chanceLaw 3 false = 5 / 32 := by
    rw [voteAccuracy_eq_binaryVotePoly chanceLaw false h0 (by norm_num), hp]
    simp only [binaryVotePoly, Finset.sum_range_succ, Finset.sum_range_zero, binomTerm,
      binaryVoteWeight]
    norm_num [Nat.choose]
  have hE := uniformPick_accuracy chanceLaw (N := 3) le_rfl (by norm_num : 0 < 3) false
  rw [hp] at hE
  refine ⟨hV, hE, ?_⟩
  rw [ordered_response_premium_eq, hE, hV]
  norm_num

end SEKernel.Closeout.BinaryVoting

#print axioms SEKernel.Closeout.BinaryVoting.binary_hump_identification
#print axioms SEKernel.Closeout.BinaryVoting.binary_10_5_keep_one_forces_post_one
#print axioms SEKernel.Closeout.BinaryVoting.nonmodal_B_values
