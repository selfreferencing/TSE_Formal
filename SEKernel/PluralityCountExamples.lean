/-
Actual-law count consumers. All sampling probabilities below are derived from
IIDCountLaw's proved binomial specialization, rather than a polynomial model.
-/
import SEKernel.PluralityCountFormula

namespace SEKernel.Epistemic

open Finset
open scoped Nat Classical
open SEKernel.FiniteProbability

/-- Deterministic pushforward preserves event probabilities. -/
theorem prob_map_event {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (L : Law Ω) (f : Ω → Λ) (E : Λ → Prop) :
    (L.map f).prob E = L.prob (fun ω => E (f ω)) := by
  classical
  rw [← Law.expect_indicator, Law.expect_map]
  exact Law.expect_indicator L (fun ω => E (f ω))

/-- Applying a finite alphabet map independently at every coordinate gives its IID pushforward law. -/
theorem iid_map_atom_probability {N : ℕ} {B C : Type*} [Fintype B] [Fintype C]
    (π : Law B) (f : B → C) (v : Fin N → C) :
    (iidAlphabetLaw π N).prob (fun w => (fun i => f (w i)) = v) =
      (iidAlphabetLaw (π.map f) N).mass v := by
  classical
  have hE : (fun w : Fin N → B => (fun i => f (w i)) = v) =
      (fun w => ∀ i, f (w i) = v i) := by
    funext w
    exact propext funext_iff
  rw [hE]
  change (Law.pi (fun _ : Fin N => π)).prob _ = _
  rw [prob_pi_forall (fun _ : Fin N => π) (fun i x => f x = v i)]
  rfl

theorem law_eq_of_mass_eq {Ω : Type*} [Fintype Ω] (L K : Law Ω)
    (h : L.mass = K.mass) : L = K := by
  cases L
  cases K
  cases h
  rfl

/-- Finite IID mapping law, for arbitrary events rather than just atoms. -/
theorem iid_map_event_probability {N : ℕ} {B C : Type*} [Fintype B] [Fintype C]
    (π : Law B) (f : B → C) (E : (Fin N → C) → Prop) :
    (iidAlphabetLaw π N).prob (fun w => E (fun i => f (w i))) =
      (iidAlphabetLaw (π.map f) N).prob E := by
  classical
  have hL : (iidAlphabetLaw π N).map (fun w i => f (w i)) =
      iidAlphabetLaw (π.map f) N := by
    apply law_eq_of_mass_eq
    funext v
    exact iid_map_atom_probability π f v
  rw [← hL, prob_map_event]

noncomputable def labelFlag {B : Type*} (b x : B) : Bool := by
  classical
  exact if x = b then true else false

@[simp] theorem labelFlag_eq_true {B : Type*} (b x : B) : labelFlag b x = true ↔ x = b := by
  classical
  by_cases h : x = b <;> simp [labelFlag, h]

theorem labelFlag_mass {B : Type*} [Fintype B] (π : Law B) (b : B) :
    (π.map (labelFlag b)).mass true = π.mass b := by
  classical
  change π.prob (fun x => labelFlag b x = true) = _
  simp only [labelFlag_eq_true]
  unfold Law.prob
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem wordCount_labelFlag {N : ℕ} {B : Type*} (w : Fin N → B) (b : B) :
    wordCount (fun i => labelFlag b (w i)) true = wordCount w b := by
  classical
  unfold wordCount
  apply congrArg Finset.card
  ext i
  simp

/-- The actual count of any selected label has the binomial law. -/
theorem iid_single_label_count_probability {N j : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (b : B) (hj : j ≤ N) :
    (iidAlphabetLaw π N).prob (fun w => wordCount w b = j) =
      (N.choose j : ℝ) * π.mass b ^ j * (1 - π.mass b) ^ (N - j) := by
  classical
  have h := iid_map_event_probability (N := N) π (labelFlag b) (fun w => wordCount w true = j)
  simp only [wordCount_labelFlag] at h
  rw [h, iid_binary_count_probability _ hj, labelFlag_mass]

/-- A value lying in a finite set is the disjoint sum of its point events. -/
theorem prob_value_mem_finset {Ω Λ : Type*} [Fintype Ω]
    (L : Law Ω) (f : Ω → Λ) (s : Finset Λ) :
    L.prob (fun ω => f ω ∈ s) = ∑ v ∈ s, L.prob (fun ω => f ω = v) := by
  classical
  unfold Law.prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : f ω ∈ s
  · rw [Finset.sum_eq_single (f ω)]
    · simp [h]
    · intro v _ hv
      simp [Ne.symm hv]
    · exact fun hn => (hn h).elim
  · have hz : ∀ v ∈ s, f ω ≠ v := by
      intro v hv he
      exact h (he.symm ▸ hv)
    simp [h, hz]

/-- Exact binomial upper tail, derived from the actual IID label-count distribution. -/
theorem iid_single_label_tail_probability {N threshold : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (b : B) :
    (iidAlphabetLaw π N).prob (fun w => threshold ≤ wordCount w b) =
      ∑ j ∈ Finset.Icc threshold N,
        (N.choose j : ℝ) * π.mass b ^ j * (1 - π.mass b) ^ (N - j) := by
  classical
  have hE : (fun w : Fin N → B => threshold ≤ wordCount w b) =
      (fun w => wordCount w b ∈ Finset.Icc threshold N) := by
    funext w
    apply propext
    have hbound : wordCount w b ≤ N := by
      unfold wordCount
      exact (Finset.card_filter_le _ _).trans (by simp)
    simp [Finset.mem_Icc, hbound]
  rw [hE, prob_value_mem_finset]
  apply Finset.sum_congr rfl
  intro j hj
  exact iid_single_label_count_probability π b (Finset.mem_Icc.mp hj).2

/-- A selected label has a three-of-five consensus with this exact probability. -/
theorem iid_five_consensus_polynomial {A : Type*} [Fintype A]
    (π : Law (Option A)) (a : A) :
    (iidWordLaw π 5).prob (fun z => consensusAt z 3 a) =
      10 * π.mass (some a) ^ 3 - 15 * π.mass (some a) ^ 4 +
        6 * π.mass (some a) ^ 5 := by
  classical
  have hE : (fun z : OrderedWord 5 A => consensusAt z 3 a) =
      (fun z => 3 ≤ wordCount z (some a)) := by
    funext z
    apply propext
    simp only [consensusAt, wordCount_eq_labelCount]
  rw [hE]
  change (iidAlphabetLaw π 5).prob (fun z => 3 ≤ wordCount z (some a)) = _
  rw [iid_single_label_tail_probability]
  have hI : Finset.Icc 3 5 = ({3, 4, 5} : Finset ℕ) := by ext j; simp; omega
  rw [hI]
  norm_num [Nat.choose]
  ring

/-- Doc B A4.4: exact five-draw false-consensus mass for the actual IID word law. -/
theorem iid_five_falseConsensus_polynomial {A : Type*} [Fintype A]
    (π : Law (Option A)) (correct : A) :
    (iidWordLaw π 5).prob (fun z => falseConsensus z 3 correct) =
      ∑ b, if b = correct then 0 else
        10 * π.mass (some b) ^ 3 - 15 * π.mass (some b) ^ 4 +
          6 * π.mass (some b) ^ 5 := by
  classical
  rw [falseConsensus_probability_eq_sum _ (by norm_num)]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b = correct
  · simp [hb]
  · simp only [hb, ↓reduceIte, iid_five_consensus_polynomial]

/-- Two readable labels, `false` correct and `true` wrong, with an explicit abstention mass. -/
noncomputable def binaryReadableLaw (p q abst : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (habst : 0 ≤ abst) (hs : p + q + abst = 1) : Law (Option Bool) where
  mass := fun x => match x with | none => abst | some false => p | some true => q
  nonneg := by intro x; cases x with
    | none => exact habst
    | some b => cases b; exact hp; exact hq
  total := by simp only [Fintype.sum_option, Fintype.sum_bool]; linarith

noncomputable def trapCorrectModeLaw : Law (Option Bool) :=
  binaryReadableLaw (3 / 5) (2 / 5) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

noncomputable def trapCorrectModeLawA : Law (Option Bool) :=
  binaryReadableLaw (11 / 20) (9 / 20) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Doc B A4.4's correct-mode Trap witness, evaluated through the proved count tail. -/
theorem actual_trap_correctMode_B :
    (iidWordLaw trapCorrectModeLaw 5).prob (fun z => falseConsensus z 3 false) = 992 / 3125 ∧
      (3 / 10 : ℝ) < 992 / 3125 ∧
      trapCorrectModeLaw.mass (some true) < trapCorrectModeLaw.mass (some false) := by
  rw [iid_five_falseConsensus_polynomial]
  norm_num [Fintype.sum_bool, trapCorrectModeLaw, binaryReadableLaw]

/-- Doc A A3.6's correct-mode Trap witness, evaluated through the proved count tail. -/
theorem actual_trap_correctMode_A :
    (iidWordLaw trapCorrectModeLawA 5).prob (fun z => falseConsensus z 3 false) = 650997 / 1600000 ∧
      (3 / 10 : ℝ) < 650997 / 1600000 ∧
      trapCorrectModeLawA.mass (some true) < trapCorrectModeLawA.mass (some false) := by
  rw [iid_five_falseConsensus_polynomial]
  norm_num [Fintype.sum_bool, trapCorrectModeLawA, binaryReadableLaw]

/-- Correct mass 1/5, a wrong mass 3/10, and five other wrong masses 1/10. -/
noncomputable def nonTrapWrongModeLaw : Law (Option (Fin 7)) where
  mass := fun x => match x with
    | none => 0
    | some i => ![(1/5 : ℝ), 3/10, 1/10, 1/10, 1/10, 1/10, 1/10] i
  nonneg := by
    intro x
    cases x with
    | none => norm_num
    | some i => fin_cases i <;> norm_num
  total := by norm_num [Fintype.sum_option, Fin.sum_univ_succ]

/-- Doc A's wrong-mode non-Trap witness is an actual IID false-consensus probability. -/
theorem actual_nonTrap_wrongMode_A :
    (iidWordLaw nonTrapWrongModeLaw 5).prob (fun z => falseConsensus z 3 (0 : Fin 7)) = 5147 / 25000 ∧
      (5147 / 25000 : ℝ) < 3 / 10 ∧
      ∀ b : Fin 7, b ≠ 1 → nonTrapWrongModeLaw.mass (some b) < nonTrapWrongModeLaw.mass (some 1) := by
  rw [iid_five_falseConsensus_polynomial]
  constructor
  · norm_num [Fin.sum_univ_succ, nonTrapWrongModeLaw]
  constructor
  · norm_num
  · intro b hb
    fin_cases b <;> norm_num [nonTrapWrongModeLaw] at *

end SEKernel.Epistemic
