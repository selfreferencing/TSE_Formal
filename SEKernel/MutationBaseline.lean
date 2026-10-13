import SEKernel.FiniteProbability

/-! Finite retained-survivor mutation. The interface uses `u` for voter-to-board
and `d` for board-to-voter. Generation indices include zero. -/
namespace SEKernel.MutationBaseline
open scoped BigOperators
open FiniteProbability
noncomputable section

/-- A binary phenotype after mutation, before retention is combined with offspring. -/
def mutationProbability (u d y : ℝ) : ℝ := u * (1 - y) + (1 - d) * y

/-- Conditional expected board fraction after unchanged survivors and offspring. -/
def affineStep (r u d y : ℝ) : ℝ := r * u + (1 - r * (u + d)) * y

theorem transmission_identity (r u d y : ℝ) :
    (1 - r) * y + r * mutationProbability u d y = affineStep r u d y := by
  unfold mutationProbability affineStep
  ring

/-- Bernoulli law, with `true` denoting a board. -/
def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : Law Bool where
  mass b := if b then p else 1 - p
  nonneg b := by cases b <;> simp <;> linarith
  total := by simp

@[simp] theorem bernoulli_true (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (bernoulli p hp hp').mass true = p := rfl

@[simp] theorem bernoulli_mean (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (bernoulli p hp hp').expect (fun b => if b then (1 : ℝ) else 0) = p := by
  simp [Law.expect, Law1.mean, bernoulli]

theorem mutationProbability_bounds {u d y : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    0 ≤ mutationProbability u d y ∧ mutationProbability u d y ≤ 1 := by
  constructor
  · exact add_nonneg (mul_nonneg hu (by linarith)) (mul_nonneg (by linarith) hy)
  · calc
      mutationProbability u d y ≤ 1 * (1-y) + 1*y :=
        add_le_add (mul_le_mul_of_nonneg_right hu' (by linarith))
          (mul_le_mul_of_nonneg_right (by linarith : 1-d ≤ 1) hy)
      _ = 1 := by ring

/-- Actual finite law for one offspring, conditional on its parental board marginal.
No joint independence of offspring is asserted or needed by the mean identity. -/
def offspringLaw (u d y : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) : Law Bool :=
  bernoulli (mutationProbability u d y)
    (mutationProbability_bounds hu hu' hd hd' hy hy').1
    (mutationProbability_bounds hu hu' hd hd' hy hy').2

theorem offspring_mean (u d y : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    (offspringLaw u d y hu hu' hd hd' hy hy').expect
      (fun b => if b then (1 : ℝ) else 0) = mutationProbability u d y := by
  exact bernoulli_mean _ _ _

/-- Each offspring may depend arbitrarily on the others. Only its board marginal
is required; summing expectations gives the transmission formula. -/
theorem finite_population_transmission {Ω : Type*} [Fintype Ω]
    (L : Law Ω) (P S : ℕ) (hP : 0 < P) (hSP : S ≤ P)
    (u d y : ℝ) (X : Fin (P-S) → Ω → ℝ)
    (hX : ∀ j, L.expect (X j) = mutationProbability u d y) :
    L.expect (fun ω => ((S : ℝ)*y + ∑ j, X j ω) / P) =
      affineStep ((P-S : ℕ) / (P : ℝ)) u d y := by
  rw [show (fun ω => ((S : ℝ)*y + ∑ j, X j ω) / (P : ℝ)) =
      (fun ω => ((S : ℝ)*y + ∑ j, X j ω) * (P : ℝ)⁻¹) by rfl,
    L.expect_mul_const, L.expect_add, L.expect_const, L.expect_sum]
  simp only [hX, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((P-S : ℕ) : ℝ) = (P : ℝ) - S := Nat.cast_sub hSP
  have hp : (P : ℝ) ≠ 0 := by positivity
  rw [hcast]
  unfold affineStep mutationProbability
  field_simp
  ring

/-- Uniform-survival neutrality is the explicit input `E Y = x`. -/
theorem expect_affineStep {Ω : Type*} [Fintype Ω] (L : Law Ω)
    (r u d : ℝ) (Y : Ω → ℝ) :
    L.expect (fun ω => affineStep r u d (Y ω)) = affineStep r u d (L.expect Y) := by
  unfold affineStep
  rw [L.expect_add, L.expect_const, L.expect_const_mul]

theorem neutral_expectation {Ω : Type*} [Fintype Ω] (L : Law Ω)
    (r u d x : ℝ) (Y : Ω → ℝ) (hY : L.expect Y = x) :
    L.expect (fun ω => affineStep r u d (Y ω)) = affineStep r u d x := by
  rw [expect_affineStep, hY]

/-- The neutral fixed point, with the nonzero denominator explicit. -/
theorem fixed_point (r u d : ℝ) (hud : u+d ≠ 0) :
    affineStep r u d (u/(u+d)) = u/(u+d) := by
  unfold affineStep
  field_simp
  ring

/-- Expected population fractions; this is the deterministic recursion of means. -/
def meanTrajectory (r u d initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | t+1 => affineStep r u d (meanTrajectory r u d initial t)

@[simp] theorem meanTrajectory_zero (r u d initial : ℝ) :
    meanTrajectory r u d initial 0 = initial := rfl
@[simp] theorem meanTrajectory_succ (r u d initial : ℝ) (t : ℕ) :
    meanTrajectory r u d initial (t+1) =
      affineStep r u d (meanTrajectory r u d initial t) := rfl

theorem meanTrajectory_closed (r u d initial : ℝ) (hud : u+d ≠ 0) (t : ℕ) :
    meanTrajectory r u d initial t =
      u/(u+d) + (initial-u/(u+d)) * (1-r*(u+d))^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [meanTrajectory_succ, ih]
    have hf := fixed_point r u d hud
    unfold affineStep at hf ⊢
    rw [pow_succ]
    nlinarith

theorem meanTrajectory_distance (r u d initial : ℝ) (hud : u+d ≠ 0) (t : ℕ) :
    |meanTrajectory r u d initial t - u/(u+d)| =
      |initial-u/(u+d)| * |1-r*(u+d)|^t := by
  rw [meanTrajectory_closed r u d initial hud]
  simp only [add_sub_cancel_left, abs_mul, abs_pow]

theorem coefficient_bounds {r u d : ℝ} (hr : 0 < r) (hr' : r < 1)
    (hu : 0 ≤ u) (hu' : u ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) (hud : 0 < u+d) :
    -1 < 1-r*(u+d) ∧ 1-r*(u+d) < 1 := by
  have hprod : 0 < r*(u+d) := mul_pos hr hud
  have hlt : r*(u+d) < 2 := by nlinarith
  constructor <;> linarith

theorem geometric_sum_start_one (b : ℝ) (T : ℕ) :
    (1-b) * (∑ t ∈ Finset.range T, b^(t+1)) = b*(1-b^T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- The finite-horizon average, with generations 1 through `T` and both
denominators explicitly nonzero. -/
theorem meanTrajectory_average (r u d initial : ℝ) (hud : u+d ≠ 0)
    (T : ℕ) (hT : 0 < T) (hb : 1-r*(u+d) ≠ 1) :
    (∑ t ∈ Finset.range T, meanTrajectory r u d initial (t+1)) / T =
      u/(u+d) + (initial-u/(u+d)) *
        ((1-r*(u+d)) * (1-(1-r*(u+d))^T) /
          ((T:ℝ)*(1-(1-r*(u+d))))) := by
  simp_rw [meanTrajectory_closed r u d initial hud]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hg := geometric_sum_start_one (1-r*(u+d)) T
  have ht : (T:ℝ) ≠ 0 := by positivity
  have hb' : 1-(1-r*(u+d)) ≠ 0 := by exact sub_ne_zero.mpr (Ne.symm hb)
  have hgs : (∑ t ∈ Finset.range T, (1-r*(u+d))^(t+1)) =
      (1-r*(u+d))*(1-(1-r*(u+d))^T)/(1-(1-r*(u+d))) := by
    apply (eq_div_iff hb').2
    simpa only [mul_comm] using hg
  rw [hgs]
  field_simp

theorem meanTrajectory_zero_monotone {r u d : ℝ} (hud : 0 < u+d)
    (hu : 0 ≤ u) (hb : 0 ≤ 1-r*(u+d)) (hb' : 1-r*(u+d) ≤ 1) (t : ℕ) :
    meanTrajectory r u d 0 t ≤ meanTrajectory r u d 0 (t+1) := by
  rw [meanTrajectory_closed _ _ _ _ (ne_of_gt hud),
      meanTrajectory_closed _ _ _ _ (ne_of_gt hud), pow_succ]
  have hz : 0 ≤ u/(u+d) := div_nonneg hu (le_of_lt hud)
  have hp : 0 ≤ (1-r*(u+d))^t := pow_nonneg hb _
  have hm := mul_nonneg (mul_nonneg hz hp) (sub_nonneg.mpr hb')
  nlinarith only [hm]

/-- Six alleles: zero is voter, the other five are board alleles. A locus hit
changes uniformly to one of the five different alleles. -/
def sixAlleleMutation (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) (a : Fin 6) : Law (Fin 6) where
  mass b := if b=a then 1-q else q/5
  nonneg b := by split_ifs <;> first | linarith | positivity
  total := by
    classical
    have hf (b : Fin 6) : (if b=a then 1-q else q/5) =
        q/5 + (if b=a then (1-q)-q/5 else 0) := by split_ifs <;> ring
    simp_rw [hf]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem sixAllele_voter_to_board (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    (sixAlleleMutation q hq hq' 0).prob (fun b => b ≠ 0) = q := by
  classical
  simp [Law.prob, sixAlleleMutation, Fin.sum_univ_succ]
  ring

theorem sixAllele_board_to_voter (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (a : Fin 6) (ha : a ≠ 0) :
    (sixAlleleMutation q hq hq' a).prob (fun b => b = 0) = q/5 := by
  classical
  simp [Law.prob, sixAlleleMutation, ha, Ne.symm ha]

/-- The six-allele instance is separate from the interface theorem. -/
theorem sixAllele_fixed_point (q : ℝ) (hq : q ≠ 0) :
    q/(q+q/5) = (5:ℝ)/6 := by field_simp; ring

theorem experiment_coefficients :
    (2:ℝ)/3 * (3/25) = 2/25 ∧
    1-(2:ℝ)/3*((3:ℝ)/25+3/125) = 113/125 ∧
    ((3:ℝ)/25)/((3:ℝ)/25+3/125) = 5/6 := by norm_num

theorem experiment_trajectory (t : ℕ) :
    meanTrajectory (2/3) (3/25) (3/125) 0 t =
      (5:ℝ)/6 * (1-(113/125)^t) := by
  rw [meanTrajectory_closed _ _ _ _ (by norm_num)]
  norm_num
  ring

/-- Exact expected mean over generations 1 through 7; no sample-path claim. -/
theorem experiment_seven_generation_mean :
    (∑ t : Fin 7, meanTrajectory (2/3) (3/25) (3/125) 0 (t.val+1))/7 =
      (177168949182968:ℝ)/667572021484375 := by
  simp only [experiment_trajectory]
  norm_num [Fin.sum_univ_succ]

end
end SEKernel.MutationBaseline
