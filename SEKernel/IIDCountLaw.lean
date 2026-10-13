/-
Exact probabilities of actual IID count fibers. Every count formula is proved
from the independent word law and the cardinal of the fiber it measures.
-/
import SEKernel.CountProfileCombinatorics

namespace SEKernel.Epistemic

open Finset
open scoped Nat
open SEKernel.FiniteProbability

/-- IID law on words over any finite alphabet; `iidWordLaw` is its option-alphabet instance. -/
noncomputable def iidAlphabetLaw {B : Type*} [Fintype B] (π : Law B) (N : ℕ) :
    Law (Fin N → B) := Law.pi (fun _ : Fin N => π)

/-- The IID probability of a particular ordered word depends only on its actual counts. -/
theorem iidAlphabetLaw_mass {N : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (z : Fin N → B) :
    (iidAlphabetLaw π N).mass z = ∏ b, π.mass b ^ wordCount z b := by
  classical
  unfold iidAlphabetLaw Law.pi
  symm
  calc
    _ = ∏ b, ∏ i ∈ Finset.univ.filter (fun i => z i = b), π.mass b := by
      apply Finset.prod_congr rfl
      intro b _
      simp only [Finset.prod_const, wordCount]
    _ = _ := Finset.prod_fiberwise' Finset.univ z π.mass

/-- Probability of the actual count fiber, before substituting its cardinal. -/
theorem iid_countProfile_probability_card {N : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (c : B → ℕ) :
    (iidAlphabetLaw π N).prob (fun z => countProfile z = c) =
      ((countFiber c (N := N)).card : ℝ) * ∏ b, π.mass b ^ c b := by
  classical
  unfold Law.prob
  calc
    _ = ∑ z ∈ countFiber c (N := N), (iidAlphabetLaw π N).mass z := by
      rw [countFiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : countProfile z = c <;> simp [hz]
    _ = ∑ _z ∈ countFiber c (N := N), ∏ b, π.mass b ^ c b := by
      apply Finset.sum_congr rfl
      intro z hz
      have hc : countProfile z = c := (Finset.mem_filter.mp hz).2
      rw [iidAlphabetLaw_mass]
      apply Finset.prod_congr rfl
      intro b _
      rw [← congrFun hc b]
      rfl
    _ = _ := by simp

/-- The exact multinomial law of actual IID counts, including the empty word. -/
theorem iid_countProfile_probability {N : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (c : B → ℕ) (hc : ∑ b, c b = N) :
    (iidAlphabetLaw π N).prob (fun z => countProfile z = c) =
      (Nat.multinomial Finset.univ c : ℝ) * ∏ b, π.mass b ^ c b := by
  classical
  obtain ⟨z, hz⟩ := exists_word_of_sum_counts c hc
  rw [iid_countProfile_probability_card, ← hz, countFiber_card]

/-- Real-valued factorial form of the exact count law. -/
theorem iid_countProfile_probability_factorial {N : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (c : B → ℕ) (hc : ∑ b, c b = N) :
    (iidAlphabetLaw π N).prob (fun z => countProfile z = c) =
      ((N ! : ℕ) : ℝ) / (∏ b, ((c b)! : ℕ) : ℕ) * ∏ b, π.mass b ^ c b := by
  classical
  rw [iid_countProfile_probability π c hc]
  congr 1
  apply (eq_div_iff (Nat.cast_ne_zero.mpr
    (ne_of_gt (Finset.prod_pos fun b _ => Nat.factorial_pos _)))).2
  exact_mod_cast (by
    simpa only [hc, mul_comm] using Nat.multinomial_spec Finset.univ c)

/-- Existing option-word law satisfies the actual multinomial count formula. -/
theorem iidWordLaw_countProfile_probability {N : ℕ} {A : Type*} [Fintype A]
    (π : Law (Option A)) (c : Option A → ℕ) (hc : ∑ a, c a = N) :
    (iidWordLaw π N).prob (fun z => countProfile z = c) =
      (Nat.multinomial Finset.univ c : ℝ) * ∏ a, π.mass a ^ c a :=
  iid_countProfile_probability π c hc

/-- An event restricted to the actual count fiber. -/
noncomputable def eventCountFiber {N : ℕ} {B : Type*} [Fintype B]
    (c : B → ℕ) (E : (Fin N → B) → Prop) : Finset (Fin N → B) := by
  classical
  exact (countFiber c).filter E

/-- Restricting an IID count fiber to an event keeps its common per-word mass. -/
theorem iid_countProfile_event_probability_card {N : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (c : B → ℕ) (E : (Fin N → B) → Prop) :
    (iidAlphabetLaw π N).prob (fun z => countProfile z = c ∧ E z) =
      ((eventCountFiber c E (N := N)).card : ℝ) * ∏ b, π.mass b ^ c b := by
  classical
  unfold eventCountFiber Law.prob
  have he : Finset.univ.filter (fun z : Fin N → B => countProfile z = c ∧ E z) =
      (countFiber c (N := N)).filter E := by
    ext z
    simp [countFiber]
  calc
    _ = ∑ z ∈ (countFiber c (N := N)).filter E, (iidAlphabetLaw π N).mass z := by
      rw [← he, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : countProfile z = c ∧ E z <;> simp [hz]
    _ = ∑ _z ∈ (countFiber c (N := N)).filter E, ∏ b, π.mass b ^ c b := by
      apply Finset.sum_congr rfl
      intro z hz
      have hc : countProfile z = c := by
        simpa only [countFiber, Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.mem_filter.mp hz).1
      rw [iidAlphabetLaw_mass]
      apply Finset.prod_congr rfl
      intro b _
      rw [← congrFun hc b]
      rfl
    _ = _ := by simp

/-- Right-composition is a bijection of positional permutation samples. -/
noncomputable def shuffleComposition {N : ℕ} (e : Equiv.Perm (Fin N)) :
    Equiv.Perm (Equiv.Perm (Fin N)) where
  toFun π := π.trans e.symm
  invFun π := π.trans e
  left_inv π := by ext i; simp
  right_inv π := by ext i; simp

/-- Uniform shuffling gives equal atom probabilities to words of equal counts. -/
theorem shuffledWord_atom_equal {N : ℕ} {B : Type*}
    (z w v : Fin N → B) (hwv : countProfile w = countProfile v) :
    (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => shuffledWord z π = w) =
      (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => shuffledWord z π = v) := by
  classical
  obtain ⟨e, he⟩ := exists_perm_of_countProfile_eq w v hwv
  have hE : (fun π => shuffledWord z (shuffleComposition e π) = v) =
      (fun π => shuffledWord z π = w) := by
    funext π
    apply propext
    change shuffledWord z π ∘ e = v ↔ shuffledWord z π = w
    rw [← he]
    exact ⟨fun h => e.surjective.injective_comp_right h, fun h => congrArg (fun f => f ∘ e) h⟩
  rw [← hE]
  exact uniformLaw_prob_equiv (shuffleComposition e) (fun π => shuffledWord z π = v)

/-- Uniform shuffling is the uniform distribution on the actual count-profile fiber. -/
theorem shuffledWord_atom_probability {N : ℕ} {B : Type*} [Fintype B]
    (z w : Fin N → B) (hw : countProfile w = countProfile z) :
    (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => shuffledWord z π = w) =
      1 / ((countFiber (countProfile z) (N := N)).card : ℝ) := by
  classical
  let L := uniformLaw (Equiv.Perm (Fin N))
  let S := countFiber (countProfile z) (N := N)
  have hS : S.Nonempty := ⟨z, by simp [S, countFiber]⟩
  have htotal : (∑ v ∈ S, L.prob (fun π => shuffledWord z π = v)) = 1 := by
    rw [← prob_mem_eq_sum]
    have he : (fun π => shuffledWord z π ∈ S) = (fun _ => True) := by
      funext π
      apply propext
      exact ⟨fun _ => trivial, fun _ => by simp [S, countFiber, shuffledWord_countProfile]⟩
    rw [he, L.prob_true]
  have hequal : (∑ v ∈ S, L.prob (fun π => shuffledWord z π = v)) =
      (S.card : ℝ) * L.prob (fun π => shuffledWord z π = w) := by
    calc
      _ = ∑ _v ∈ S, L.prob (fun π => shuffledWord z π = w) := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvp : countProfile v = countProfile z := by simpa [S, countFiber] using hv
        exact shuffledWord_atom_equal z v w (hvp.trans hw.symm)
      _ = _ := by simp
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hS.card_pos)
  apply (eq_div_iff hc).2
  rw [hequal] at htotal
  simpa only [mul_comm] using htotal

/-- Event probabilities for a uniform shuffle are actual event-fiber cardinal ratios. -/
theorem shuffledWord_event_probability {N : ℕ} {B : Type*} [Fintype B]
    (z : Fin N → B) (E : (Fin N → B) → Prop) :
    (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => E (shuffledWord z π)) =
      ((eventCountFiber (countProfile z) E (N := N)).card : ℝ) /
        ((countFiber (countProfile z) (N := N)).card : ℝ) := by
  classical
  unfold eventCountFiber
  let S := (countFiber (countProfile z) (N := N)).filter E
  have hE : (fun π => E (shuffledWord z π)) = (fun π => shuffledWord z π ∈ S) := by
    funext π
    apply propext
    simp [S, countFiber, shuffledWord_countProfile]
  rw [hE, prob_mem_eq_sum]
  calc
    _ = ∑ _w ∈ S, 1 / ((countFiber (countProfile z) (N := N)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply shuffledWord_atom_probability
      simpa [S, countFiber] using (Finset.mem_filter.mp hw).1
    _ = _ := by simp [S, div_eq_mul_inv]

/-- Conditioning an IID law on a positive count cell gives exactly uniform shuffling.
The positivity is explicit, so no conditional value on a null cell is selected. -/
theorem iid_conditional_count_uniform_shuffle {N : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (z : Fin N → B) (E : (Fin N → B) → Prop)
    (hpos : 0 < (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z)) :
    (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z ∧ E w) /
      (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z) =
      (uniformLaw (Equiv.Perm (Fin N))).prob (fun σ => E (shuffledWord z σ)) := by
  classical
  rw [iid_countProfile_event_probability_card, iid_countProfile_probability_card,
    shuffledWord_event_probability]
  rw [iid_countProfile_probability_card] at hpos
  have hm : (∏ b, π.mass b ^ countProfile z b) ≠ 0 := by
    intro hm
    rw [hm, mul_zero] at hpos
    exact (lt_irrefl 0 hpos)
  exact mul_div_mul_right _ _ hm

/-- Unnormalized uniform-shuffle bridge, valid even when the IID count cell has zero mass. -/
theorem iid_countProfile_event_probability_shuffle {N : ℕ} {B : Type*} [Fintype B]
    (π : Law B) (z : Fin N → B) (E : (Fin N → B) → Prop) :
    (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z ∧ E w) =
      (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z) *
        (uniformLaw (Equiv.Perm (Fin N))).prob (fun σ => E (shuffledWord z σ)) := by
  classical
  rw [iid_countProfile_event_probability_card, iid_countProfile_probability_card,
    shuffledWord_event_probability]
  have hS : (countFiber (countProfile z) (N := N)).Nonempty :=
    ⟨z, by simp [countFiber]⟩
  have hc : ((countFiber (countProfile z) (N := N)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt hS.card_pos)
  field_simp [hc]
  <;> ring

/-- Count profile for a binary word with exactly `j` true entries. -/
def boolCountProfile (N j : ℕ) (b : Bool) : ℕ := if b then j else N - j

theorem sum_boolCountProfile {N j : ℕ} (hj : j ≤ N) :
    ∑ b, boolCountProfile N j b = N := by
  simp [boolCountProfile, Nat.add_sub_of_le hj]

theorem countProfile_bool_iff {N j : ℕ} (z : Fin N → Bool) (hj : j ≤ N) :
    countProfile z = boolCountProfile N j ↔ wordCount z true = j := by
  constructor
  · intro h
    simpa [countProfile, boolCountProfile] using congrFun h true
  · intro h
    funext b
    cases b
    · have hs := sum_wordCount z
      rw [Fintype.sum_bool] at hs
      simp only [countProfile, boolCountProfile, Bool.false_eq_true, ↓reduceIte]
      omega
    · simpa only [countProfile, boolCountProfile, ↓reduceIte] using h

theorem multinomial_boolCountProfile {N j : ℕ} (hj : j ≤ N) :
    Nat.multinomial Finset.univ (boolCountProfile N j) = N.choose j := by
  rw [Nat.multinomial, Fintype.sum_bool, Fintype.prod_bool]
  simp [boolCountProfile, Nat.add_sub_of_le hj,
    Nat.choose_eq_factorial_div_factorial hj]

/-- The binomial specialization is a probability of actual binary words. -/
theorem iid_binary_count_probability {N j : ℕ} (π : Law Bool) (hj : j ≤ N) :
    (iidAlphabetLaw π N).prob (fun z => wordCount z true = j) =
      (N.choose j : ℝ) * π.mass true ^ j * (1 - π.mass true) ^ (N - j) := by
  have hE : (fun z : Fin N → Bool => wordCount z true = j) =
      (fun z => countProfile z = boolCountProfile N j) := by
    funext z
    exact propext (countProfile_bool_iff z hj).symm
  have hf : π.mass false = 1 - π.mass true := by
    have ht := π.total
    rw [Fintype.sum_bool] at ht
    linarith
  rw [hE, iid_countProfile_probability π _ (sum_boolCountProfile hj),
    multinomial_boolCountProfile hj, Fintype.prod_bool]
  simp [boolCountProfile, hf, mul_assoc]

/-- Total first-entry function, returning no label when no entry is in `T`. -/
noncomputable def firstTInWord {N : ℕ} {B : Type*} [DecidableEq B]
    (z : Fin N → B) (T : Finset B) : Option B :=
  if h : (activePositions z T).Nonempty then some (z ((activePositions z T).min' h)) else none

/-- The previous fixed-word permutation object is the actual first label of its shuffled word. -/
theorem firstTInWord_shuffledWord {N : ℕ} {B : Type*} [DecidableEq B]
    (z : Fin N → B) (T : Finset B) (hT : (activePositions z T).Nonempty)
    (π : Equiv.Perm (Fin N)) :
    firstTInWord (shuffledWord z π) T = some (firstTLabel z T hT π) := by
  classical
  obtain ⟨k, hklabel, hkT, hkmin⟩ := firstTLabel_semantics z T hT π
  have hk : k ∈ activePositions (shuffledWord z π) T := by
    simp [activePositions, hkT]
  have hA : (activePositions (shuffledWord z π) T).Nonempty := ⟨k, hk⟩
  have he : (activePositions (shuffledWord z π) T).min' hA = k := by
    apply le_antisymm ((activePositions (shuffledWord z π) T).min'_le _ hk)
    apply hkmin
    simpa [activePositions] using (activePositions (shuffledWord z π) T).min'_mem hA
  rw [firstTInWord, dif_pos hA, he, hklabel]

/-- Conditional first-tied-label counting for the actual IID word law: `u_a / L`.
`T` can be any fixed nonempty set of active labels, including a set of tied modes. -/
theorem iid_conditional_firstT_probability {N : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (π : Law B) (z : Fin N → B) (T : Finset B)
    (hT : (activePositions z T).Nonempty) (a : B) (ha : a ∈ T)
    (hpos : 0 < (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z)) :
    (iidAlphabetLaw π N).prob
        (fun w => countProfile w = countProfile z ∧ firstTInWord w T = some a) /
      (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z) =
      (wordCount z a : ℝ) / ((activePositions z T).card : ℝ) := by
  rw [iid_conditional_count_uniform_shuffle π z _ hpos]
  have hE : (fun σ => firstTInWord (shuffledWord z σ) T = some a) =
      (fun σ => firstTLabel z T hT σ = a) := by
    funext σ
    apply propext
    rw [firstTInWord_shuffledWord z T hT, Option.some.injEq]
  rw [hE, firstTLabel_probability z T hT a ha]
  have hcount : (Finset.univ.filter (fun i : Fin N => z i = a)).card = wordCount z a := by
    unfold wordCount
    apply congrArg Finset.card
    ext i
    simp
  rw [hcount]

/-- When every label is active, the first active label is the first coordinate. -/
theorem firstTInWord_univ {N : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (z : Fin N → B) (hN : 0 < N) :
    firstTInWord z Finset.univ = some (z ⟨0, hN⟩) := by
  classical
  have hz : (⟨0, hN⟩ : Fin N) ∈ activePositions z Finset.univ := by simp [activePositions]
  have hA : (activePositions z Finset.univ).Nonempty := ⟨⟨0, hN⟩, hz⟩
  have he : (activePositions z Finset.univ).min' hA = ⟨0, hN⟩ := by
    apply le_antisymm ((activePositions z Finset.univ).min'_le _ hz)
    exact Nat.zero_le _
  rw [firstTInWord, dif_pos hA, he]

/-- Conditional fixed-count fairness: the first coordinate has label probability `count / N`. -/
theorem iid_conditional_first_position_probability {N : ℕ} {B : Type*}
    [Fintype B] [DecidableEq B] (π : Law B) (z : Fin N → B) (a : B) (hN : 0 < N)
    (hpos : 0 < (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z)) :
    (iidAlphabetLaw π N).prob
        (fun w => countProfile w = countProfile z ∧ w ⟨0, hN⟩ = a) /
      (iidAlphabetLaw π N).prob (fun w => countProfile w = countProfile z) =
      (wordCount z a : ℝ) / (N : ℝ) := by
  have hA : (activePositions z Finset.univ).Nonempty :=
    ⟨⟨0, hN⟩, by simp [activePositions]⟩
  have h := iid_conditional_firstT_probability π z Finset.univ hA a (Finset.mem_univ a) hpos
  have hE : (fun w : Fin N → B => countProfile w = countProfile z ∧
      firstTInWord w Finset.univ = some a) =
      (fun w => countProfile w = countProfile z ∧ w ⟨0, hN⟩ = a) := by
    funext w
    apply propext
    rw [firstTInWord_univ w hN, Option.some.injEq]
  rw [hE] at h
  simpa [activePositions] using h

end SEKernel.Epistemic
