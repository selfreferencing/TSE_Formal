import SEKernel.MutationBaseline

/-! Finite score pooling and exact witnesses. Random ties here are explicitly
uniform among the slots attaining the largest score. Continuous scale-family
claims are outside this finite module. -/
namespace SEKernel.ScorePooling
open scoped BigOperators
open FiniteProbability MutationBaseline
noncomputable section

/-- A common finite weighted score, without a normalization assumption. -/
def weightedScore {ι : Type*} [Fintype ι] (w outcome : ι → ℝ) : ℝ :=
  (∑ i, w i * outcome i) / ∑ i, w i

theorem current_scores_equal {ι : Type*} [Fintype ι]
    (w a b : ι → ℝ) (h : ∀ i, a i = b i) :
    weightedScore w a = weightedScore w b := by simp [weightedScore, h]

/-- Same institutions on both pools; changing which pools are included changes
historical means in both directions. -/
theorem historical_composition_examples :
    weightedScore (fun _ : Fin 2 => (1:ℝ)) (fun i => if i=0 then 0 else 1) = 1/2 ∧
    weightedScore (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) = 1 ∧
    weightedScore (fun _ : Fin 2 => (1:ℝ)) (fun i => if i=0 then 1 else 0) = 1/2 ∧
    weightedScore (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0) = 0 := by
  norm_num [weightedScore, Fin.sum_univ_succ]

/-- The eligible slots for a uniform tie at the largest score. -/
def topSlots {ι : Type*} [Fintype ι] (score : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, score j ≤ score i)

theorem topSlots_nonempty {ι : Type*} [Fintype ι] [Nonempty ι] (score : ι → ℝ) :
    (topSlots score).Nonempty := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ score Finset.univ_nonempty
  refine ⟨i, ?_⟩
  simp only [topSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j
  exact hmax j (Finset.mem_univ j)

/-- Actual top-one selection law. Its denominator counts eligible *slots*. -/
def fairTopLaw {ι : Type*} [Fintype ι] [Nonempty ι] (score : ι → ℝ) : Law ι where
  mass i := by
    classical
    exact if i ∈ topSlots score then ((topSlots score).card : ℝ)⁻¹ else 0
  nonneg i := by split_ifs <;> positivity
  total := by
    classical
    have hc : ((topSlots score).card : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Finset.card_pos.mpr (topSlots_nonempty score))
    rw [← Finset.sum_filter]
    have heq : Finset.univ.filter (fun i => i ∈ topSlots score) = topSlots score := by ext; simp
    rw [heq]
    simp [hc]

/-- The proved tie-count formula used in all exact evaluations below. -/
theorem fairTopLaw_count {ι : Type*} [Fintype ι] [Nonempty ι]
    (score : ι → ℝ) (i : ι) :
    (fairTopLaw score).mass i =
      if (∀ j, score j ≤ score i) then ((topSlots score).card : ℝ)⁻¹ else 0 := by
  classical
  simp [fairTopLaw, topSlots]

/-- Closed tie-count formula for a distinguished slot among three candidates. -/
theorem fairTopLaw_three_zero (x y z : ℝ) :
    (fairTopLaw ![x,y,z]).mass 0 =
      if y ≤ x ∧ z ≤ x then
        ((1 + (if y=x then 1 else 0) + (if z=x then 1 else 0) : ℝ))⁻¹ else 0 := by
  classical
  rw [fairTopLaw_count]
  by_cases hy : y ≤ x <;> by_cases hz : z ≤ x
  · have hslots : topSlots ![x,y,z] =
        ({0} ∪ (if y=x then {1} else ∅) ∪ (if z=x then {2} else ∅) : Finset (Fin 3)) := by
      ext i
      fin_cases i
      · simp [topSlots, Fin.forall_fin_succ, hy, hz]
      · simp only [topSlots, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Fin.forall_fin_zero, forall_const, le_refl, and_true, Finset.mem_union,
          Finset.mem_singleton]
        by_cases he : y=x
        · simp [he, hz]
        · have hlt : y < x := lt_of_le_of_ne hy he
          simp [he, not_le.mpr hlt]
          split_ifs <;> norm_num [Fin.ext_iff]
      · simp only [topSlots, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Fin.forall_fin_zero, forall_const, le_refl, and_true, Finset.mem_union,
          Finset.mem_singleton]
        by_cases he : z=x
        · simp [he, hy]
        · have hlt : z < x := lt_of_le_of_ne hz he
          simp [he, not_le.mpr hlt]
          split_ifs <;> norm_num [Fin.ext_iff]
    rw [hslots]
    by_cases he : y=x <;> by_cases hf : z=x <;>
      norm_num [Fin.forall_fin_succ, hy, hz, he, hf,
        Finset.card_insert_of_notMem, Fin.ext_iff]
  · simp [Fin.forall_fin_succ, hy, hz]
  · simp [Fin.forall_fin_succ, hy, hz]
  · simp [Fin.forall_fin_succ, hy, hz]

def bit (b : Bool) : ℝ := if b then 1 else 0

abbrev FiveDraws := Bool × Bool × Bool × Bool × Bool

def fiveDrawLaw (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : Law FiveDraws :=
  (bernoulli p hp hp').prod ((bernoulli p hp hp').prod
    ((bernoulli p hp hp').prod ((bernoulli p hp hp').prod (bernoulli p hp hp'))))

/-- One evaluation for the newcomer, two independent evaluations per incumbent. -/
def unequalScores (ω : FiveDraws) : Fin 3 → ℝ :=
  ![bit ω.1, (bit ω.2.1 + bit ω.2.2.1)/2,
      (bit ω.2.2.2.1 + bit ω.2.2.2.2)/2]

def unequalWinnerLaw (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : Law (Fin 3) :=
  (fiveDrawLaw p hp hp').bind (fun ω => fairTopLaw (unequalScores ω))

/-- Exact independent Bernoulli witness, computed through the slot-count formula. -/
theorem unequal_evaluation_probability (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (unequalWinnerLaw p hp hp').mass 0 = p-p^3 + (p^5+(1-p)^5)/3 := by
  classical
  unfold unequalWinnerLaw Law.bind fiveDrawLaw
  simp only [Law.prod]
  simp [Fintype.sum_prod_type, fairTopLaw_three_zero, unequalScores, bit,
    MutationBaseline.bernoulli]
  norm_num
  ring

/-- Higher variance does not have a universal direction for top-one survival. -/
theorem unequal_evaluation_counterexamples :
    (unequalWinnerLaw (1/10) (by norm_num) (by norm_num)).mass 0 = 71/240 ∧
    (71:ℝ)/240 < 1/3 ∧
    (unequalWinnerLaw (1/2) (by norm_num) (by norm_num)).mass 0 = 19/48 ∧
    (19:ℝ)/48 > 1/3 := by
  rw [unequal_evaluation_probability, unequal_evaluation_probability]
  norm_num

def fairBit : Law Bool := MutationBaseline.bernoulli (1/2) (by norm_num) (by norm_num)

def pastLaw (m : ℕ) : Law (Fin m → Bool) := Law.pi (fun _ => fairBit)

/-- The current pool is included in both histories; past pools are separate
product coordinates. `m+1` is the total number of incumbent evaluations. -/
def overlapLaw (m : ℕ) : Law (Bool × (Fin m → Bool)) := fairBit.prod (pastLaw m)

def trueCount {m : ℕ} (z : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i => z i = true)).card

theorem trueCount_le {m : ℕ} (z : Fin m → Bool) : trueCount z ≤ m := by
  simpa [trueCount] using Finset.card_filter_le (Finset.univ : Finset (Fin m))
    (fun i => z i = true)

theorem trueCount_eq_iff {m : ℕ} (z : Fin m → Bool) :
    trueCount z = m ↔ ∀ i, z i = true := by
  simpa [trueCount] using
    (Finset.card_filter_eq_iff (s := Finset.univ) (p := fun i => z i = true))

def historicalScore {m : ℕ} (ω : Bool × (Fin m → Bool)) : ℝ :=
  (bit ω.1 + trueCount ω.2)/(m+1 : ℕ)

def currentScore {m : ℕ} (ω : Bool × (Fin m → Bool)) : ℝ := bit ω.1

/-- With at least `S` protected incumbent copies, this event is exactly the
newcomer's inclusion event for any `1 ≤ S ≤ P-1`. -/
theorem historical_strict_win {m : ℕ} (ω : Bool × (Fin m → Bool)) :
    historicalScore ω < currentScore ω ↔ ω.1 = true ∧ ¬ ∀ i, ω.2 i = true := by
  have hm : (0:ℝ) < (m+1 : ℕ) := by positivity
  have hc := trueCount_le ω.2
  have hce := trueCount_eq_iff ω.2
  have hcr : (trueCount ω.2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hc
  cases hb : ω.1
  · simp only [historicalScore, currentScore, bit, hb, Bool.false_eq_true, if_false,
      zero_add, false_and]
    exact iff_false_intro (not_lt.mpr (div_nonneg (by positivity) (le_of_lt hm)))
  · simp only [historicalScore, currentScore, bit, hb, if_true, true_and]
    rw [div_lt_iff₀ hm]
    push_cast
    constructor
    · intro h hall
      have he : trueCount ω.2 = m := hce.mpr hall
      rw [he] at h
      linarith
    · intro h
      have hne : trueCount ω.2 ≠ m := mt hce.mp h
      have hn : trueCount ω.2 < m := by omega
      have hn' : (trueCount ω.2 : ℝ) < (m:ℝ) := by exact_mod_cast hn
      linarith

theorem prob_prod_rectangle {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (L : Law Ω) (K : Law Λ) (E : Ω → Prop) (F : Λ → Prop) :
    (L.prod K).prob (fun ω => E ω.1 ∧ F ω.2) = L.prob E * K.prob F := by
  classical
  rw [← L.expect_indicator E, ← K.expect_indicator F,
    ← Law.expect_prod_mul]
  rw [← (L.prod K).expect_indicator (fun ω => E ω.1 ∧ F ω.2)]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω.1 <;> by_cases hf : F ω.2 <;> simp [he, hf]

theorem past_all_true_probability (m : ℕ) :
    (pastLaw m).prob (fun z => ∀ i, z i = true) = (1/2 : ℝ)^m := by
  classical
  have he : (fun z : Fin m → Bool => ∀ i, z i = true) =
      (fun z => z = fun _ => true) := by
    funext z
    exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩
  rw [he]
  simp [Law.prob, pastLaw, Law.pi, fairBit, MutationBaseline.bernoulli]

/-- Exact finite historical-overlap probability. Generation/pool indexing starts
at zero; the incumbent has `m+1` observations, the newcomer one. -/
theorem historical_survival_probability (m : ℕ) :
    (overlapLaw m).prob (fun ω => historicalScore ω < currentScore ω) =
      (1/2 : ℝ)*(1-(1/2 : ℝ)^m) := by
  have he : (fun ω : Bool × (Fin m → Bool) => historicalScore ω < currentScore ω) =
      (fun ω => ω.1 = true ∧ ¬ ∀ i, ω.2 i = true) := by
    funext ω
    exact propext (historical_strict_win ω)
  rw [he]
  change (fairBit.prod (pastLaw m)).prob
    (fun ω => (fun b => b=true) ω.1 ∧ (fun z => ¬ ∀ i, z i=true) ω.2) = _
  rw [prob_prod_rectangle fairBit (pastLaw m) (fun b => b=true)
    (fun z => ¬ ∀ i, z i=true), Law.prob_compl, past_all_true_probability]
  congr 1
  simp [Law.prob, fairBit, MutationBaseline.bernoulli]

def newcomerSurvivorShare {m : ℕ} (S : ℕ) (ω : Bool × (Fin m → Bool)) : ℝ :=
  (if historicalScore ω < currentScore ω then 1 else 0)/(S:ℝ)

theorem historical_expected_share (m S : ℕ) :
    (overlapLaw m).expect (newcomerSurvivorShare S) =
      ((1/2 : ℝ)*(1-(1/2 : ℝ)^m))/(S:ℝ) := by
  classical
  unfold newcomerSurvivorShare
  simp only [div_eq_mul_inv]
  rw [Law.expect_mul_const, Law.expect_indicator, historical_survival_probability]
  simp only [div_eq_mul_inv, one_mul]

theorem historical_share_exceeds_current_iff (m P S : ℕ)
    (hP : 0 < P) (hS : 0 < S) :
    (overlapLaw m).expect (newcomerSurvivorShare S) > (1:ℝ)/P ↔
      (1/2 : ℝ)*(1-(1/2 : ℝ)^m) > (S:ℝ)/P := by
  rw [historical_expected_share]
  have hp : (0:ℝ) < P := by positivity
  have hs : (0:ℝ) < S := by positivity
  rw [gt_iff_lt, lt_div_iff₀ hs, gt_iff_lt]
  simp only [div_mul_eq_mul_div, one_mul]

/-- Under current common-pool scores all copies have the same realized score.
Protected incumbent ties therefore give the newcomer zero probability. -/
theorem current_pool_strict_win_probability (m : ℕ) :
    (overlapLaw m).prob (fun ω => currentScore ω < currentScore ω) = 0 := by simp

theorem historical_overlap_counterexample :
    (overlapLaw 2).prob (fun ω => historicalScore ω < currentScore ω) = 3/8 ∧
    (overlapLaw 2).expect (newcomerSurvivorShare 4) = 3/32 ∧
    (3:ℝ)/32 > 1/12 := by
  rw [historical_survival_probability, historical_expected_share]
  norm_num


theorem fairBit_mean : fairBit.expect bit = 1/2 := by
  exact bernoulli_mean _ _ _

theorem fairBit_variance : fairBit.variance bit = 1/4 := by
  rw [Law.variance_eq]
  norm_num [Law.expect, Law1.mean, fairBit, bit, MutationBaseline.bernoulli]

theorem trueCount_eq_sum {m : ℕ} (z : Fin m → Bool) :
    (trueCount z : ℝ) = ∑ i, bit (z i) := by
  classical
  unfold trueCount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases z i <;> simp [bit]

theorem past_sum_mean (m : ℕ) :
    (pastLaw m).expect (fun z => ∑ i, bit (z i)) = (m:ℝ)/2 := by
  rw [Law.expect_sum]
  simp only [pastLaw, Law.expect_pi_coord, fairBit_mean]
  simp
  ring

theorem past_sum_variance (m : ℕ) :
    (pastLaw m).variance (fun z => ∑ i, bit (z i)) = (m:ℝ)/4 := by
  rw [pastLaw, Law.variance_pi_sum]
  simp only [fairBit_variance, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem currentScore_mean (m : ℕ) : (overlapLaw m).expect currentScore = 1/2 := by
  exact Law.expect_prod_fst _ _ bit |>.trans fairBit_mean

theorem historicalScore_mean (m : ℕ) : (overlapLaw m).expect historicalScore = 1/2 := by
  unfold historicalScore
  simp_rw [trueCount_eq_sum, div_eq_mul_inv]
  rw [Law.expect_mul_const, Law.expect_add]
  change ((fairBit.prod (pastLaw m)).expect (fun ω => bit ω.1) +
    (fairBit.prod (pastLaw m)).expect (fun ω => ∑ i, bit (ω.2 i))) * _ = _
  rw [Law.expect_prod_fst fairBit (pastLaw m) bit,
    Law.expect_prod_snd fairBit (pastLaw m) (fun z => ∑ i, bit (z i)),
    fairBit_mean, past_sum_mean]
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem currentScore_variance (m : ℕ) : (overlapLaw m).variance currentScore = 1/4 := by
  rw [Law.variance_eq]
  rw [show (fun ω : Bool × (Fin m → Bool) => currentScore ω ^ 2) =
      (fun ω => bit ω.1 ^ 2) by rfl]
  rw [overlapLaw, Law.expect_prod_fst fairBit (pastLaw m) (fun b => bit b ^ 2)]
  change fairBit.expect (fun b => bit b ^ 2) -
    (fairBit.prod (pastLaw m)).expect (fun ω => bit ω.1) ^ 2 = 1/4
  rw [Law.expect_prod_fst fairBit (pastLaw m) bit, ← Law.variance_eq, fairBit_variance]

theorem historicalScore_variance (m : ℕ) :
    (overlapLaw m).variance historicalScore = 1/(4*((m:ℝ)+1)) := by
  have he : (historicalScore : Bool × (Fin m → Bool) → ℝ) =
      (fun ω => (((m:ℝ)+1)⁻¹) * (bit ω.1 + ∑ i, bit (ω.2 i))) := by
    funext ω
    simp only [historicalScore, trueCount_eq_sum, Nat.cast_add, Nat.cast_one]
    ring
  rw [he, Law.variance_const_mul, overlapLaw,
    Law.variance_prod_add fairBit (pastLaw m) bit (fun z => ∑ i, bit (z i)),
    fairBit_variance, past_sum_variance]
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

end
end SEKernel.ScorePooling
