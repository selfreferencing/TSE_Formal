/-
Exact count formulas for the actual ordered first-appearance plurality rule.
The profile law and shuffle bridge are proved in IIDCountLaw; no conditional
uniformity, winner formula, or numerical sampling result is assumed here.
-/
import SEKernel.IIDCountLaw

namespace SEKernel.Epistemic

open Finset
open scoped Nat Classical
open SEKernel.FiniteProbability

/-- Readable positive-count weak maxima; the empty/all-abstention profile has no modes. -/
noncomputable def readableModes {A : Type*} [Fintype A] (c : Option A → ℕ) : Finset A := by
  classical
  exact Finset.univ.filter fun a => 0 < c (some a) ∧ ∀ b, c (some b) ≤ c (some a)

/-- The same positive readable modes in the full alphabet, with abstention excluded. -/
noncomputable def readableModeOptions {A : Type*} [Fintype A] (c : Option A → ℕ) :
    Finset (Option A) := by
  classical
  exact (readableModes c).image some

/-- The actual earliest-maximal-position set equals the positions carrying positive readable modes. -/
theorem candidatePositions_eq_active_modes {N : ℕ} {A : Type*} [Fintype A]
    (z : OrderedWord N A) :
    candidatePositions z = activePositions z (readableModeOptions (countProfile z)) := by
  classical
  ext i
  cases hi : z i with
  | none => simp [candidatePositions, activePositions, readableModeOptions, hi]
  | some a =>
    have hm : some a ∈ readableModeOptions (countProfile z) ↔
        a ∈ readableModes (countProfile z) := by simp [readableModeOptions]
    simp only [candidatePositions, activePositions, Finset.mem_filter, Finset.mem_univ,
      true_and, hi, Option.some_ne_none, true_and, hm]
    simp only [readableModes, Finset.mem_filter, Finset.mem_univ, true_and, countProfile]
    constructor
    · intro h
      constructor
      · rw [wordCount_eq_labelCount, labelCount_pos_iff]
        exact ⟨i, hi⟩
      · intro b
        by_cases hb : 0 < labelCount z (some b)
        · obtain ⟨j, hj⟩ := (labelCount_pos_iff z (some b)).1 hb
          simpa [wordCount_eq_labelCount, hj] using h.2 j (by simp [hj])
        · rw [wordCount_eq_labelCount, wordCount_eq_labelCount]
          omega
    · rintro ⟨_, h⟩
      refine ⟨by simp, ?_⟩
      intro j hj
      cases he : z j with
      | none => exact (hj he).elim
      | some b => simpa [wordCount_eq_labelCount, he] using h b

/-- The first-active-label function on the actual mode set is precisely plurality. -/
theorem first_mode_iff_plurality {N : ℕ} {A : Type*} [Fintype A]
    (z : OrderedWord N A) (a : A) :
    firstTInWord z (readableModeOptions (countProfile z)) = some (some a) ↔
      plurality z = some a := by
  classical
  unfold firstTInWord plurality
  rw [← candidatePositions_eq_active_modes]
  split_ifs <;> simp

theorem plurality_mem_readableModes {N : ℕ} {A : Type*} [Fintype A]
    (z : OrderedWord N A) (a : A) (h : plurality z = some a) :
    a ∈ readableModes (countProfile z) := by
  classical
  simp only [readableModes, Finset.mem_filter, Finset.mem_univ, true_and, countProfile]
  constructor
  · rw [wordCount_eq_labelCount, labelCount_pos_iff]
    exact plurality_mem_word z a h
  · intro b
    simpa only [wordCount_eq_labelCount] using plurality_dominates_readable z a h b

theorem readableModes_equal_count {N : ℕ} {A : Type*} [Fintype A]
    (z : OrderedWord N A) (a b : A)
    (ha : a ∈ readableModes (countProfile z)) (hb : b ∈ readableModes (countProfile z)) :
    wordCount z (some b) = wordCount z (some a) := by
  classical
  simp only [readableModes, Finset.mem_filter, Finset.mem_univ, true_and, countProfile] at ha hb
  exact le_antisymm (ha.2 b) (hb.2 a)

/-- Number of maximal readable positions: number of tied modes times their common count. -/
theorem active_modes_card {N : ℕ} {A : Type*} [Fintype A]
    (z : OrderedWord N A) (a : A) (ha : a ∈ readableModes (countProfile z)) :
    (activePositions z (readableModeOptions (countProfile z))).card =
      (readableModes (countProfile z)).card * wordCount z (some a) := by
  classical
  let H := readableModes (countProfile z)
  let T := readableModeOptions (countProfile z)
  have hs := Finset.sum_card_fiberwise_eq_card_filter Finset.univ T z
  have hsum : (activePositions z T).card = ∑ b ∈ H, wordCount z (some b) := by
    calc
      _ = ∑ q ∈ T, (Finset.univ.filter (fun i => z i = q)).card := hs.symm
      _ = ∑ b ∈ H, wordCount z (some b) := by
        dsimp [T, readableModeOptions]
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro b _
          unfold wordCount
          apply congrArg Finset.card
          ext i
          simp
        · intro b _ c _ h
          exact Option.some.inj h
  rw [hsum]
  calc
    _ = ∑ _b ∈ H, wordCount z (some a) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact readableModes_equal_count z a b ha hb
    _ = _ := by simp [H]

/-- The actual plurality winner of a uniform positional shuffle is uniform over the positive readable modes. -/
theorem shuffled_plurality_probability {N : ℕ} {A : Type*} [Fintype A]
    (z : OrderedWord N A) (a : A) :
    (uniformLaw (Equiv.Perm (Fin N))).prob (fun σ => plurality (shuffledWord z σ) = some a) =
      if a ∈ readableModes (countProfile z) then
        1 / ((readableModes (countProfile z)).card : ℝ) else 0 := by
  classical
  by_cases ha : a ∈ readableModes (countProfile z)
  · rw [if_pos ha]
    let T := readableModeOptions (countProfile z)
    have haT : some a ∈ T := by simp [T, readableModeOptions, ha]
    have hcount : 0 < wordCount z (some a) := by
      simpa only [readableModes, Finset.mem_filter, Finset.mem_univ, true_and, countProfile] using
        (show 0 < countProfile z (some a) from (Finset.mem_filter.mp ha).2.1)
    obtain ⟨i, hi⟩ := (labelCount_pos_iff z (some a)).1 (by
      simpa only [wordCount_eq_labelCount] using hcount)
    have hT : (activePositions z T).Nonempty := ⟨i, by simp [activePositions, hi, haT]⟩
    have hE : (fun σ => plurality (shuffledWord z σ) = some a) =
        (fun σ => firstTLabel z T hT σ = some a) := by
      funext σ
      apply propext
      rw [← first_mode_iff_plurality, shuffledWord_countProfile]
      rw [firstTInWord_shuffledWord z T hT, Option.some.injEq]
    rw [hE, firstTLabel_probability z T hT (some a) haT]
    have hnum : (Finset.univ.filter (fun j : Fin N => z j = some a)).card = wordCount z (some a) := by
      unfold wordCount
      apply congrArg Finset.card
      ext j
      simp
    rw [hnum, active_modes_card z a ha, Nat.cast_mul]
    have hc : (wordCount z (some a) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcount)
    have hH : ((readableModes (countProfile z)).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.card_pos.mpr ⟨a, ha⟩))
    field_simp
  · rw [if_neg ha]
    have hE : (fun σ => plurality (shuffledWord z σ) = some a) = (fun _ => False) := by
      funext σ
      apply propext
      constructor
      · intro hv
        have hm := plurality_mem_readableModes (shuffledWord z σ) a hv
        rw [shuffledWord_countProfile] at hm
        exact ha hm
      · exact False.elim
    rw [hE, Law.prob_false]

/-- Actual IID probability of a count cell together with the specified first-appearance winner. -/
theorem iid_countProfile_vote_probability {N : ℕ} {A : Type*} [Fintype A]
    (π : Law (Option A)) (c : Option A → ℕ) (hc : ∑ q, c q = N) (a : A) :
    (iidWordLaw π N).prob (fun z => countProfile z = c ∧ correctVote z a) =
      ((Nat.multinomial Finset.univ c : ℝ) * ∏ q, π.mass q ^ c q) *
        (if a ∈ readableModes c then 1 / ((readableModes c).card : ℝ) else 0) := by
  classical
  obtain ⟨z, hz⟩ := exists_word_of_sum_counts c hc
  rw [← hz]
  change (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z ∧ correctVote w a) = _
  rw [iid_countProfile_event_probability_shuffle π z (fun w => correctVote w a)]
  rw [iid_countProfile_probability π (countProfile z) (sum_wordCount z)]
  simpa only [correctVote] using congrArg
    (fun v : ℝ => ((Nat.multinomial Finset.univ (countProfile z) : ℝ) *
      ∏ q, π.mass q ^ countProfile z q) * v) (shuffled_plurality_probability z a)

/-- All admissible count vectors, with a finite enumeration even at N=0. -/
noncomputable def validCountProfiles (A : Type*) [Fintype A] (N : ℕ) : Finset (Option A → ℕ) := by
  classical
  exact Finset.piAntidiag Finset.univ N

/-- Doc B A3.1: the actual first-appearance plurality accuracy is its multinomial count sum. -/
theorem plurality_multinomial_formula {N : ℕ} {A : Type*} [Fintype A]
    (π : Law (Option A)) (a : A) :
    voteAccuracy π N a = ∑ c ∈ validCountProfiles A N,
      ((Nat.multinomial Finset.univ c : ℝ) * ∏ q, π.mass q ^ c q) *
        (if a ∈ readableModes c then 1 / ((readableModes c).card : ℝ) else 0) := by
  classical
  have hp : voteAccuracy π N a = ∑ c ∈ validCountProfiles A N,
      (iidWordLaw π N).prob (fun z => countProfile z = c ∧ correctVote z a) := by
    unfold voteAccuracy Law.prob
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    have hz : countProfile z ∈ validCountProfiles A N := by
      simp [validCountProfiles, Finset.mem_piAntidiag, countProfile, sum_wordCount]
    rw [Finset.sum_eq_single (countProfile z)]
    · by_cases hv : correctVote z a <;> simp [hv]
    · intro c _ hc
      have hne : countProfile z ≠ c := Ne.symm hc
      simp [hne]
    · exact fun hn => (hn hz).elim
  rw [hp]
  apply Finset.sum_congr rfl
  intro c hc
  have hsum : ∑ q, c q = N := by simpa [validCountProfiles] using hc
  exact iid_countProfile_vote_probability π c hsum a

end SEKernel.Epistemic
