/-
One shared wrong answer maximizes the ideal-board premium at fixed right mass.
The proof couples ordered words by merging wrong labels; first-appearance ties
are retained. It does not require an ordering of answer labels.
-/
import SEKernel.CloseoutBinaryVoting

namespace SEKernel.Closeout.HumpWorstCase

open Finset SEKernel.FiniteProbability SEKernel.Epistemic SEKernel.EpistemicPayoff
open SEKernel.Closeout.BinaryVoting

/-- Merging labels can only increase the count of a label at any given position. -/
theorem labelCount_map_le {N : ℕ} {A B : Type*} (z : OrderedWord N A)
    (f : Option A → Option B) (x : Option A) :
    labelCount z x ≤ labelCount (fun i => f (z i)) (f x) := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact congrArg f hi

/-- If a coarsening preserves abstention and the right label's exact positions,
winning after coarsening implies winning before it, including first-appearance ties. -/
theorem plurality_of_map_correct {N : ℕ} {A B : Type*} (z : OrderedWord N A)
    (f : Option A → Option B) (a : A) (b : B)
    (hnone : ∀ x, f x = none ↔ x = none)
    (hcorrect : ∀ x, f x = some b ↔ x = some a)
    (hwin : plurality (fun i => f (z i)) = some b) : plurality z = some a := by
  classical
  let v : OrderedWord N B := fun i => f (z i)
  have hcount : labelCount v (some b) = labelCount z (some a) := by
    unfold labelCount
    congr 1
    ext i
    simp [v, hcorrect]
  have hnon (i : Fin N) (hi : z i ≠ none) : v i ≠ none :=
    fun h => hi ((hnone _).1 h)
  have hmax (i : Fin N) (hi : z i ≠ none) :
      labelCount z (z i) ≤ labelCount z (some a) := by
    calc labelCount z (z i) ≤ labelCount v (v i) := labelCount_map_le z f (z i)
         _ ≤ labelCount v (some b) := plurality_maximal_count v b hwin i (hnon i hi)
         _ = labelCount z (some a) := hcount
  obtain ⟨i₀, hi₀, hc₀, hfirst⟩ := plurality_first_maximal v b hwin
  have hi₀z : z i₀ = some a := (hcorrect _).1 hi₀
  have hicand : i₀ ∈ candidatePositions z := by
    simp only [candidatePositions, mem_filter, mem_univ, true_and, hi₀z]
    exact ⟨by simp, fun j hj => hmax j hj⟩
  have hsub : candidatePositions z ⊆ candidatePositions v := by
    intro i hi
    obtain ⟨hin, himax⟩ := (mem_filter.mp hi).2
    have hge : labelCount z (some a) ≤ labelCount z (z i) := by
      simpa [hi₀z] using himax i₀ (by simp [hi₀z])
    refine mem_filter.mpr ⟨mem_univ _, hnon i hin, ?_⟩
    intro j hj
    calc labelCount v (v j) ≤ labelCount v (some b) :=
           plurality_maximal_count v b hwin j hj
         _ = labelCount z (some a) := hcount
         _ ≤ labelCount z (z i) := hge
         _ ≤ labelCount v (v i) := labelCount_map_le z f (z i)
  have hne : (candidatePositions z).Nonempty := ⟨i₀, hicand⟩
  have hm : (candidatePositions z).min' hne = i₀ := by
    exact le_antisymm (min'_le _ _ hicand)
      (hfirst _ (hsub (min'_mem _ _)))
  unfold plurality
  rw [dif_pos hne, hm, hi₀z]

/-- All wrong labels become `false`, the right label becomes `true`. -/
def mergeWrong {A : Type*} [DecidableEq A] (a : A) : Option A → Option Bool
  | none => none
  | some x => some (if x = a then true else false)

theorem mergeWrong_none {A : Type*} [DecidableEq A] (a : A) (x : Option A) :
    mergeWrong a x = none ↔ x = none := by
  cases x <;> simp [mergeWrong]

theorem mergeWrong_correct {A : Type*} [DecidableEq A] (a : A) (x : Option A) :
    mergeWrong a x = some true ↔ x = some a := by
  cases x with
  | none => simp [mergeWrong]
  | some x => by_cases h : x = a <;> simp [mergeWrong, h]

theorem mergeWrong_mass_none {A : Type*} [Fintype A] [DecidableEq A]
    (π : Law (Option A)) (a : A) : (π.map (mergeWrong a)).mass none = π.mass none := by
  classical
  change π.prob (fun x => mergeWrong a x = none) = _
  simp only [mergeWrong_none, Law.prob]
  simp

theorem mergeWrong_mass_correct {A : Type*} [Fintype A] [DecidableEq A]
    (π : Law (Option A)) (a : A) :
    (π.map (mergeWrong a)).mass (some true) = π.mass (some a) := by
  classical
  change π.prob (fun x => mergeWrong a x = some true) = _
  simp only [mergeWrong_correct, Law.prob]
  simp

/-- The single-wrong-label binary comparator is a lower bound for voting accuracy,
for every sample size (also allowing abstention). -/
theorem mergeWrong_voteAccuracy_le {A : Type*} [Fintype A] [DecidableEq A]
    (π : Law (Option A)) (a : A) (N : ℕ) :
    voteAccuracy (π.map (mergeWrong a)) N true ≤ voteAccuracy π N a := by
  unfold voteAccuracy
  change (iidAlphabetLaw (π.map (mergeWrong a)) N).prob _ ≤
    (iidAlphabetLaw π N).prob _
  rw [← iid_map_event_probability]
  apply Law.prob_mono
  intro z hz
  exact plurality_of_map_correct z (mergeWrong a) a true
    (mergeWrong_none a) (mergeWrong_correct a) hz

/-- B1: with no abstention, the binary hump is an upper bound for the actual
ideal-board premium on any finite answer alphabet. -/
theorem premium_le_hump10 {A : Type*} [Fintype A] [DecidableEq A]
    (π : Law (Option A)) (a : A) (hnone : π.mass none = 0) :
    reachProbability π 10 5 a - voteAccuracy π 10 a ≤ hump10 (π.mass (some a)) := by
  have hV := mergeWrong_voteAccuracy_le π a 10
  have hB := binary_hump_identification (π.map (mergeWrong a)) true
    (by rw [mergeWrong_mass_none, hnone])
  rw [mergeWrong_mass_correct, reach_prefix_probability _ 10 5 (by norm_num),
    mergeWrong_mass_correct] at hB
  rw [reach_prefix_probability _ 10 5 (by norm_num)]
  linarith

/-- A label map injective on the labels actually present in a word preserves
the winner, even if it is not injective on the entire alphabet. -/
theorem plurality_map_on_word {N : ℕ} {A B : Type*} (z : OrderedWord N A)
    (f : Option A → Option B) (hnone : ∀ x, f x = none ↔ x = none)
    (hinj : ∀ i j, f (z i) = f (z j) → z i = z j) :
    plurality (fun i => f (z i)) = f (plurality z) := by
  classical
  have hcount (t : Fin N) :
      labelCount (fun i => f (z i)) (f (z t)) = labelCount z (z t) := by
    unfold labelCount
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hinj i t, congrArg f⟩
  have hc : candidatePositions (fun i => f (z i)) = candidatePositions z := by
    ext i
    simp only [candidatePositions, mem_filter, mem_univ, true_and,
      ne_eq, hnone, hcount]
  unfold plurality
  simp only [hc]
  split_ifs
  · rfl
  · exact ((hnone none).2 rfl).symm

/-- With at most one positive-mass wrong label, merging wrong answers preserves
voting accuracy at every sample size. Zero-mass words are discarded by the
actual finite probability sum, rather than assumed absent pointwise. -/
theorem mergeWrong_voteAccuracy_eq {A : Type*} [Fintype A] [DecidableEq A]
    (π : Law (Option A)) (a : A)
    (hsingle : ∀ b c : A, b ≠ a → c ≠ a →
      0 < π.mass (some b) → 0 < π.mass (some c) → b = c) (N : ℕ) :
    voteAccuracy (π.map (mergeWrong a)) N true = voteAccuracy π N a := by
  classical
  unfold voteAccuracy
  change (iidAlphabetLaw (π.map (mergeWrong a)) N).prob _ =
    (iidAlphabetLaw π N).prob _
  rw [← iid_map_event_probability]
  unfold Law.prob
  apply sum_congr rfl
  intro z _
  by_cases hz : (iidAlphabetLaw π N).mass z = 0
  · simp [hz]
  have hcoord (i : Fin N) : 0 < π.mass (z i) := by
    have hn : π.mass (z i) ≠ 0 := by
      intro hi
      apply hz
      change ∏ j : Fin N, π.mass (z j) = 0
      exact prod_eq_zero (mem_univ i) hi
    exact lt_of_le_of_ne (π.nonneg _) (Ne.symm hn)
  have hinj (i j : Fin N) (h : mergeWrong a (z i) = mergeWrong a (z j)) : z i = z j := by
    cases hi : z i with
    | none =>
      have hj := (mergeWrong_none a (z j)).1 (by rw [← h, hi]; rfl)
      exact hj.symm
    | some b =>
      cases hj : z j with
      | none =>
        have hh := (mergeWrong_none a (some b)).1 (by rw [← hi, h, hj]; rfl)
        cases hh
      | some c =>
        by_cases hb : b = a
        · have hc := (mergeWrong_correct a (some c)).1 (by
            rw [← hj, ← h, hi, hb]
            simp [mergeWrong])
          simpa [hb] using hc.symm
        · by_cases hc : c = a
          · have hh := (mergeWrong_correct a (some b)).1 (by
              rw [← hi, h, hj, hc]
              simp [mergeWrong])
            exact False.elim (hb (Option.some.inj hh))
          · exact congrArg some (hsingle b c hb hc (by simpa [hi] using hcoord i)
              (by simpa [hj] using hcoord j))
  have hw := plurality_map_on_word z (mergeWrong a) (mergeWrong_none a) hinj
  have he : correctVote (fun i => mergeWrong a (z i)) true ↔ correctVote z a := by
    unfold correctVote
    rw [hw, mergeWrong_correct]
  simp only [he]

/-- B2: the premium attains the hump bound whenever at most one wrong label
has positive mass. This includes the all-right-answer law. -/
theorem premium_eq_hump10_of_single_wrong {A : Type*} [Fintype A] [DecidableEq A]
    (π : Law (Option A)) (a : A) (hnone : π.mass none = 0)
    (hsingle : ∀ b c : A, b ≠ a → c ≠ a →
      0 < π.mass (some b) → 0 < π.mass (some c) → b = c) :
    reachProbability π 10 5 a - voteAccuracy π 10 a = hump10 (π.mass (some a)) := by
  have hB := binary_hump_identification (π.map (mergeWrong a)) true
    (by rw [mergeWrong_mass_none, hnone])
  rw [mergeWrong_voteAccuracy_eq π a hsingle, mergeWrong_mass_correct,
    reach_prefix_probability _ 10 5 (by norm_num), mergeWrong_mass_correct] at hB
  rw [reach_prefix_probability _ 10 5 (by norm_num)]
  exact hB

end SEKernel.Closeout.HumpWorstCase
