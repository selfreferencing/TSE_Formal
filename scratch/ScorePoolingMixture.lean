import SEKernel.ScorePooling
namespace SEKernel.ScorePooling
open scoped BigOperators
open FiniteProbability
noncomputable section

/-- A point mass plus a uniform law on an odd finite integer grid. -/
def spikeUniform (R : ℕ) (hR : 0 < R) (center : Fin R)
    (w : ℝ) (hw : 0 ≤ w) (hw' : w ≤ 1) : Law (Fin R) where
  mass i := (if i=center then 1-w else 0) + w/R
  nonneg i := by
    apply add_nonneg
    · split_ifs <;> linarith
    · exact div_nonneg hw (Nat.cast_nonneg R)
  total := by
    classical
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hr : (R:ℝ) ≠ 0 := by positivity
    field_simp <;> ring

def uniformThree : Law (Fin 3) := spikeUniform 3 (by omega) 1 1 (by norm_num) (by norm_num)

def errorScores {R : ℕ} (offset : ℝ) (ω : Fin R × (Fin 3 × Fin 3)) : Fin 3 → ℝ :=
  ![(ω.1:ℝ)-offset, (ω.2.1:ℝ)-1, (ω.2.2:ℝ)-1]

def spikeErrorLaw (R : ℕ) (hR : 0 < R) (center : Fin R)
    (w : ℝ) (hw : 0 ≤ w) (hw' : w ≤ 1) : Law (Fin R × (Fin 3 × Fin 3)) :=
  (spikeUniform R hR center w hw hw').prod (uniformThree.prod uniformThree)

def spikeErrorWinnerLaw (R : ℕ) (hR : 0 < R) (center : Fin R)
    (w : ℝ) (hw : 0 ≤ w) (hw' : w ≤ 1) : Law (Fin 3) :=
  (spikeErrorLaw R hR center w hw hw').bind
    (fun ω => fairTopLaw (errorScores (center:ℝ) ω))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- Doc A's finite symmetric-grid mixture, evaluated by the proved tie count. -/
theorem symmetric_mixture_A_probability :
    (spikeErrorWinnerLaw 11 (by omega) 5 (1/10) (by norm_num) (by norm_num)).mass 0 =
      46/165 := by
  classical
  norm_num [spikeErrorWinnerLaw, Law.bind, spikeErrorLaw, Law.prod,
    Fintype.sum_prod_type, fairTopLaw_three_zero, errorScores, Fin.sum_univ_succ,
    uniformThree, spikeUniform]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Doc B's finite symmetric-grid mixture, evaluated by the proved tie count. -/
theorem symmetric_mixture_B_probability :
    (spikeErrorWinnerLaw 41 (by omega) 20 (1/100) (by norm_num) (by norm_num)).mass 0 =
      3217/12300 := by
  classical
  norm_num [spikeErrorWinnerLaw, Law.bind, spikeErrorLaw, Law.prod,
    Fintype.sum_prod_type, fairTopLaw_three_zero, errorScores, Fin.sum_univ_succ,
    uniformThree, spikeUniform]

/-- Both exact survival probabilities fall below neutral one-of-three survival. -/
theorem symmetric_mixture_selection_deficits :
    (46:ℝ)/165 < 1/3 ∧ (3217:ℝ)/12300 < 1/3 := by norm_num

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The higher challenger variance in Doc A's witness is an exact finite moment. -/
theorem symmetric_mixture_A_moments :
    (spikeUniform 11 (by omega) 5 (1/10) (by norm_num) (by norm_num)).expect
      (fun i => (i:ℝ)-5) = 0 ∧
    (spikeUniform 11 (by omega) 5 (1/10) (by norm_num) (by norm_num)).variance
      (fun i => (i:ℝ)-5) = 1 ∧
    uniformThree.expect (fun i => (i:ℝ)-1) = 0 ∧
    uniformThree.variance (fun i => (i:ℝ)-1) = 2/3 := by
  norm_num [Law.variance_eq, Law.expect, Law1.mean, spikeUniform,
    uniformThree, Fin.sum_univ_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The higher challenger variance in Doc B's witness is an exact finite moment. -/
theorem symmetric_mixture_B_moments :
    (spikeUniform 41 (by omega) 20 (1/100) (by norm_num) (by norm_num)).expect
      (fun i => (i:ℝ)-20) = 0 ∧
    (spikeUniform 41 (by omega) 20 (1/100) (by norm_num) (by norm_num)).variance
      (fun i => (i:ℝ)-20) = 7/5 := by
  norm_num [Law.variance_eq, Law.expect, Law1.mean, spikeUniform, Fin.sum_univ_succ]

end
end SEKernel.ScorePooling
