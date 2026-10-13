/-
Wave 3: exact clonal selection of two loci, the advocate silent in voters.
These are constant-fitness proportional-selection results. They do not assert
that the experiment's noisy truncation lifecycle is proportional selection.
All generations are indexed by t : ℕ, starting at t = 0.
-/
import SEKernel.FiniteProbability

namespace SEKernel.SilentGene

noncomputable section

open Finset FiniteProbability

section ConstantFitness
variable {ι : Type*} [Fintype ι]

/-- Unnormalized total mass after t clonal generations. -/
def clonalNormalizer (x : Law ι) (f : ι → ℝ) (t : ℕ) : ℝ :=
  ∑ i, x.mass i * f i ^ t

/-- Exact finite-time constant-fitness distribution. -/
def clonalTrajectory (x : Law ι) (f : ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  x.mass i * f i ^ t / clonalNormalizer x f t

theorem clonalNormalizer_pos (x : Law ι) {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) (t : ℕ) : 0 < clonalNormalizer x f t := by
  exact Law1.mean_pos x.nonneg x.total (fun i => pow_pos (hf i) t)

@[simp] theorem clonalTrajectory_zero (x : Law ι) (f : ι → ℝ) :
    clonalTrajectory x f 0 = x.mass := by
  funext i
  simp [clonalTrajectory, clonalNormalizer, x.total]

theorem clonalTrajectory_nonneg (x : Law ι) {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) (t : ℕ) (i : ι) : 0 ≤ clonalTrajectory x f t i :=
  div_nonneg (mul_nonneg (x.nonneg i) (pow_nonneg (hf i).le t))
    (clonalNormalizer_pos x hf t).le

theorem clonalTrajectory_total (x : Law ι) {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) (t : ℕ) : ∑ i, clonalTrajectory x f t i = 1 := by
  simp only [clonalTrajectory, ← Finset.sum_div]
  exact div_self (ne_of_gt (clonalNormalizer_pos x hf t))

theorem clonalTrajectory_mean (x : Law ι) {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) (t : ℕ) :
    Law1.mean (clonalTrajectory x f t) f =
      clonalNormalizer x f (t+1) / clonalNormalizer x f t := by
  unfold Law1.mean clonalTrajectory clonalNormalizer
  simp only [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

/-- The closed distribution is an actual orbit of the existing Law1.step. -/
theorem clonalTrajectory_step (x : Law ι) {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) (t : ℕ) :
    Law1.step (clonalTrajectory x f t) f = clonalTrajectory x f (t+1) := by
  funext i
  unfold Law1.step
  rw [clonalTrajectory_mean x hf t]
  unfold clonalTrajectory
  rw [pow_succ]
  field_simp [ne_of_gt (clonalNormalizer_pos x hf t),
    ne_of_gt (clonalNormalizer_pos x hf (t+1))]

/-- Any orbit with the same start has the displayed finite-time solution. -/
theorem constant_fitness_closed_form (x : Law ι) {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) (y : ℕ → ι → ℝ)
    (hzero : y 0 = x.mass) (hstep : ∀ t, y (t+1) = Law1.step (y t) f) :
    ∀ t, y t = clonalTrajectory x f t := by
  intro t
  induction t with
  | zero => simpa using hzero
  | succ t ih => rw [hstep, ih, clonalTrajectory_step x hf]

end ConstantFitness

abbrev Genotype := Bool × Bool

/-- First bit means board; second bit means advocate. -/
def fitness (v b c : ℝ) (g : Genotype) : ℝ :=
  if g.1 then (if g.2 then c else b) else v

theorem fitness_pos {v b c : ℝ} (hv : 0 < v) (hb : 0 < b) (hc : 0 < c) :
    ∀ g, 0 < fitness v b c g := by
  intro ⟨i,j⟩
  cases i <;> cases j <;> simp [fitness, hv, hb, hc]

/-- Conditional mass ratios carry explicit positive compartment masses. -/
def boardShare (x : Genotype → ℝ) : ℝ := x (true,false) + x (true,true)
def voterShare (x : Genotype → ℝ) : ℝ := x (false,false) + x (false,true)
def advocateAmongBoards (x : Genotype → ℝ) : ℝ := x (true,true) / boardShare x
def silentAmongVoters (x : Genotype → ℝ) : ℝ := x (false,true) / voterShare x

theorem clonal_mean (x : Genotype → ℝ) (v b c : ℝ) :
    Law1.mean x (fitness v b c) = voterShare x * v +
      x (true,false) * b + x (true,true) * c := by
  simp [Law1.mean, Fintype.sum_prod_type, Fintype.sum_bool, fitness, voterShare]
  ring

/-- Equal voter fitness exactly preserves the silent conditional frequency. -/
theorem silent_frequency_preserved (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hV : 0 < voterShare x.mass) :
    silentAmongVoters (Law1.step x.mass (fitness v b c)) =
      silentAmongVoters x.mass := by
  have hm := Law1.mean_pos x.nonneg x.total (fitness_pos hv hb hc)
  unfold silentAmongVoters voterShare Law1.step
  simp only [fitness, Bool.false_eq_true, ↓reduceIte]
  field_simp [ne_of_gt hm, ne_of_gt hv, ne_of_gt hV]
  <;> ring

/-- Conditional advocate update, independent of the population board share. -/
theorem advocate_frequency_step (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hB : 0 < boardShare x.mass) :
    advocateAmongBoards (Law1.step x.mass (fitness v b c)) =
      c * x.mass (true,true) /
        (b * x.mass (true,false) + c * x.mass (true,true)) := by
  have hm := Law1.mean_pos x.nonneg x.total (fitness_pos hv hb hc)
  have hd : 0 < b * x.mass (true,false) + c * x.mass (true,true) := by
    have h0 := x.nonneg (true,false)
    have h1 := x.nonneg (true,true)
    unfold boardShare at hB
    rcases lt_or_eq_of_le h0 with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos hb h) (mul_nonneg hc.le h1)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hb.le h0) (mul_pos hc (by linarith))
  unfold advocateAmongBoards boardShare Law1.step
  simp only [fitness, Bool.true_eq, ↓reduceIte, Bool.false_eq_true]
  field_simp [ne_of_gt hm, ne_of_gt hd]
  <;> ring

/-- The odds of advocate versus plain board multiply by c/b. -/
theorem advocate_odds_step (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hu : 0 < x.mass (true,false)) :
    Law1.step x.mass (fitness v b c) (true,true) /
      Law1.step x.mass (fitness v b c) (true,false) =
      (c/b) * (x.mass (true,true) / x.mass (true,false)) := by
  have hm := Law1.mean_pos x.nonneg x.total (fitness_pos hv hb hc)
  simp only [Law1.step, fitness, Bool.true_eq, ↓reduceIte, Bool.false_eq_true]
  field_simp [ne_of_gt hm, ne_of_gt hb, ne_of_gt hu]
  <;> ring

theorem four_genotype_normalizer (x : Law Genotype) (v b c : ℝ) (t : ℕ) :
    clonalNormalizer x (fitness v b c) t =
      voterShare x.mass * v^t + x.mass (true,false)*b^t + x.mass (true,true)*c^t := by
  simp [clonalNormalizer, Fintype.sum_prod_type, Fintype.sum_bool, fitness, voterShare]
  ring

/-- Silence persists for every finite clonal generation. -/
theorem silent_frequency_time (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hV : 0 < voterShare x.mass) (t : ℕ) :
    silentAmongVoters (clonalTrajectory x (fitness v b c) t) =
      silentAmongVoters x.mass := by
  have hZ := clonalNormalizer_pos x (fitness_pos hv hb hc) t
  have hvt := pow_pos hv t
  unfold silentAmongVoters voterShare clonalTrajectory
  simp only [fitness, Bool.false_eq_true, ↓reduceIte]
  field_simp [ne_of_gt hZ, ne_of_gt hvt, ne_of_gt hV]
  <;> ring

/-- Exact advocate frequency at time t. -/
theorem advocate_frequency_time (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hB : 0 < boardShare x.mass) (t : ℕ) :
    advocateAmongBoards (clonalTrajectory x (fitness v b c) t) =
      x.mass (true,true)*c^t /
        (x.mass (true,false)*b^t+x.mass (true,true)*c^t) := by
  have hZ := clonalNormalizer_pos x (fitness_pos hv hb hc) t
  have hden : 0 < x.mass (true,false)*b^t+x.mass (true,true)*c^t := by
    have h0 := x.nonneg (true,false)
    have h1 := x.nonneg (true,true)
    unfold boardShare at hB
    rcases lt_or_eq_of_le h0 with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos h (pow_pos hb t))
        (mul_nonneg h1 (pow_nonneg hc.le t))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg h0 (pow_nonneg hb.le t))
        (mul_pos (by linarith) (pow_pos hc t))
  unfold advocateAmongBoards boardShare clonalTrajectory
  simp only [fitness, Bool.true_eq, ↓reduceIte, Bool.false_eq_true]
  field_simp [ne_of_gt hZ, ne_of_gt hden]
  <;> ring

/-- Actual total board frequency at every finite generation. -/
theorem board_frequency_time (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c) (t : ℕ) :
    boardShare (clonalTrajectory x (fitness v b c) t) =
      (x.mass (true,false)*b^t+x.mass (true,true)*c^t) /
        (voterShare x.mass*v^t+x.mass (true,false)*b^t+x.mass (true,true)*c^t) := by
  unfold boardShare clonalTrajectory
  simp only [fitness, Bool.true_eq, ↓reduceIte, Bool.false_eq_true]
  rw [four_genotype_normalizer]
  ring

/-- Exact finite-generation board genotype odds. -/
theorem advocate_odds_time (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hu : 0 < x.mass (true,false)) (t : ℕ) :
    clonalTrajectory x (fitness v b c) t (true,true) /
      clonalTrajectory x (fitness v b c) t (true,false) =
      (x.mass (true,true)/x.mass (true,false))*(c/b)^t := by
  have hZ := clonalNormalizer_pos x (fitness_pos hv hb hc) t
  have hbt := pow_pos hb t
  simp only [clonalTrajectory, fitness, Bool.true_eq, ↓reduceIte, Bool.false_eq_true, div_pow]
  field_simp [ne_of_gt hZ, ne_of_gt hbt, ne_of_gt hu]
  <;> ring

/-- Elementary finite complement bound, used with the actual clonal fractions. -/
theorem complement_fraction_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    1-b/(a+b) ≤ a/b := by
  have hab : 0 < a+b := add_pos_of_nonneg_of_pos ha hb
  calc
    1-b/(a+b) = a/(a+b) := by field_simp; ring
    _ ≤ a/b := (div_le_div_iff₀ hab hb).mpr (by nlinarith [sq_nonneg a])

/-- Advocate deficit is bounded at every finite time; the strict fitness
ordering c>b makes the geometric ratio decay. -/
theorem advocate_deficit_bound (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < x.mass (true,true)) (t : ℕ) :
    1-advocateAmongBoards (clonalTrajectory x (fitness v b c) t) ≤
      (x.mass (true,false)/x.mass (true,true))*(b/c)^t := by
  have hB : 0 < boardShare x.mass :=
    add_pos_of_nonneg_of_pos (x.nonneg (true,false)) hh
  rw [advocate_frequency_time x hv hb hc hB]
  have h := complement_fraction_bound
    (mul_nonneg (x.nonneg (true,false)) (pow_nonneg hb.le t))
    (mul_pos hh (pow_pos hc t))
  convert h using 1 <;> simp only [div_pow] <;> ring

/-- Board deficit bound for b≤c. If v<b, its geometric ratio is below one. -/
theorem board_deficit_bound (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c) (hbc : b ≤ c)
    (hB : 0 < boardShare x.mass) (t : ℕ) :
    1-boardShare (clonalTrajectory x (fitness v b c) t) ≤
      (voterShare x.mass / boardShare x.mass)*(v/b)^t := by
  let R := voterShare x.mass*v^t
  let W := x.mass (true,false)*b^t+x.mass (true,true)*c^t
  let L := boardShare x.mass*b^t
  have hR : 0 ≤ R := mul_nonneg
    (add_nonneg (x.nonneg (false,false)) (x.nonneg (false,true))) (pow_nonneg hv.le t)
  have hL : 0 < L := mul_pos hB (pow_pos hb t)
  have hLW : L ≤ W := by
    have hpow := pow_le_pow_left₀ hb.le hbc t
    have hmul := mul_le_mul_of_nonneg_left hpow (x.nonneg (true,true))
    dsimp [L,W,boardShare]
    nlinarith
  have hW : 0 < W := hL.trans_le hLW
  have hRW : 0 < R+W := add_pos_of_nonneg_of_pos hR hW
  rw [board_frequency_time x hv hb hc]
  rw [add_assoc]
  change 1-W/(R+W) ≤ _
  calc
    1-W/(R+W) ≤ R/W := complement_fraction_bound hR hW
    _ ≤ R/L := (div_le_div_iff₀ hW hL).mpr (mul_le_mul_of_nonneg_left hLW hR)
    _ = (voterShare x.mass / boardShare x.mass)*(v/b)^t := by
      simp only [R,L,div_pow]
      ring

/-- The actual clonal board frequency crosses half exactly at the ratio test. -/
theorem board_half_frequency_iff (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c) (t : ℕ) :
    (1/2:ℝ) ≤ boardShare (clonalTrajectory x (fitness v b c) t) ↔
      voterShare x.mass ≤ x.mass (true,false)*(b/v)^t+x.mass (true,true)*(c/v)^t := by
  have hZ := clonalNormalizer_pos x (fitness_pos hv hb hc) t
  rw [four_genotype_normalizer] at hZ
  rw [board_frequency_time x hv hb hc, le_div_iff₀ hZ]
  have hratio : x.mass (true,false)*(b/v)^t+x.mass (true,true)*(c/v)^t =
      (x.mass (true,false)*b^t+x.mass (true,true)*c^t)/v^t := by
    simp only [div_pow]
    ring
  rw [hratio,le_div_iff₀ (pow_pos hv t)]
  constructor <;> intro h <;> nlinarith

/-- The actual advocate frequency among boards crosses half at its ratio test. -/
theorem advocate_half_frequency_iff (x : Law Genotype) {v b c : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hB : 0 < boardShare x.mass) (t : ℕ) :
    (1/2:ℝ) ≤ advocateAmongBoards (clonalTrajectory x (fitness v b c) t) ↔
      x.mass (true,false) ≤ x.mass (true,true)*(c/b)^t := by
  have hden : 0 < x.mass (true,false)*b^t+x.mass (true,true)*c^t := by
    have h0 := x.nonneg (true,false)
    have h1 := x.nonneg (true,true)
    unfold boardShare at hB
    rcases lt_or_eq_of_le h0 with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos h (pow_pos hb t))
        (mul_nonneg h1 (pow_nonneg hc.le t))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg h0 (pow_nonneg hb.le t))
        (mul_pos (by linarith) (pow_pos hc t))
  rw [advocate_frequency_time x hv hb hc hB, le_div_iff₀ hden]
  have hratio : x.mass (true,true)*(c/b)^t = x.mass (true,true)*c^t/b^t := by
    simp only [div_pow]
    ring
  rw [hratio,le_div_iff₀ (pow_pos hb t)]
  constructor <;> intro h <;> nlinarith

/-- A concrete normalized four-genotype population for the suppression refutation. -/
def quarterPopulation : Law Genotype where
  mass := fun _ => 1/4
  nonneg := fun _ => by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- Selection removes voter mass while preserving the silent conditional share.
Thus removal of voters does not imply loss of the allele among remaining voters. -/
theorem removing_voters_does_not_suppress_silent :
    voterShare (Law1.step quarterPopulation.mass (fitness 1 2 3)) = 2/7 ∧
    voterShare quarterPopulation.mass = 1/2 ∧
    silentAmongVoters (Law1.step quarterPopulation.mass (fitness 1 2 3)) = 1/2 ∧
    silentAmongVoters quarterPopulation.mass = 1/2 := by
  norm_num [voterShare,silentAmongVoters,Law1.step,clonal_mean,quarterPopulation,fitness]

/-- A clonal population with positive initial compartments and ordered fitnesses.
The advocate advantage c-b may be recorded separately as a; only c enters here. -/
structure CrossingModel where
  r : ℝ
  u : ℝ
  h : ℝ
  v : ℝ
  b : ℝ
  c : ℝ
  r_pos : 0 < r
  u_pos : 0 < u
  h_pos : 0 < h
  v_pos : 0 < v
  vb : v < b
  bc : b < c

namespace CrossingModel

variable (m : CrossingModel)

def boardMass (t : ℕ) : ℝ := m.u*(m.b/m.v)^t + m.h*(m.c/m.v)^t
def advocateMass (t : ℕ) : ℝ := m.h*(m.c/m.b)^t
def board (t : ℕ) : Prop := m.r ≤ m.boardMass t
def advocate (t : ℕ) : Prop := m.u ≤ m.advocateMass t

theorem b_pos : 0 < m.b := m.v_pos.trans m.vb
theorem c_pos : 0 < m.c := m.b_pos.trans m.bc
theorem bv_gt_one : 1 < m.b/m.v := (one_lt_div m.v_pos).mpr m.vb
theorem cv_gt_one : 1 < m.c/m.v := (one_lt_div m.v_pos).mpr (m.vb.trans m.bc)
theorem cb_gt_one : 1 < m.c/m.b := (one_lt_div m.b_pos).mpr m.bc

theorem boardMass_monotone : Monotone m.boardMass := by
  intro s t hst
  exact add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ m.bv_gt_one.le hst) m.u_pos.le)
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ m.cv_gt_one.le hst) m.h_pos.le)

theorem advocateMass_monotone : Monotone m.advocateMass := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ m.cb_gt_one.le hst) m.h_pos.le

/-- Finite Bernoulli lower certificate for advocate crossing. -/
theorem advocate_bernoulli_certificate (T : ℕ)
    (hT : m.u ≤ m.h*(1+(T:ℝ)*(m.c/m.b-1))) : m.advocate T := by
  have hpow := one_add_mul_le_pow (by linarith [m.cb_gt_one] : (-2:ℝ) ≤ m.c/m.b-1) T
  have hp : 1+(T:ℝ)*(m.c/m.b-1) ≤ (m.c/m.b)^T := by
    simpa using hpow
  exact hT.trans (mul_le_mul_of_nonneg_left hp m.h_pos.le)

/-- Finite Bernoulli lower certificate for board crossing. -/
theorem board_bernoulli_certificate (T : ℕ)
    (hT : m.r ≤ (m.u+m.h)*(1+(T:ℝ)*(m.b/m.v-1))) : m.board T := by
  have hpow := one_add_mul_le_pow (by linarith [m.bv_gt_one] : (-2:ℝ) ≤ m.b/m.v-1) T
  have hp : 1+(T:ℝ)*(m.b/m.v-1) ≤ (m.b/m.v)^T := by simpa using hpow
  have hbc : m.b/m.v ≤ m.c/m.v := (div_le_div_iff_of_pos_right m.v_pos).mpr m.bc.le
  have hpowbc := pow_le_pow_left₀ (div_nonneg m.b_pos.le m.v_pos.le) hbc T
  unfold board boardMass
  calc
    m.r ≤ (m.u+m.h)*(1+(T:ℝ)*(m.b/m.v-1)) := hT
    _ ≤ (m.u+m.h)*(m.b/m.v)^T := mul_le_mul_of_nonneg_left hp (add_pos m.u_pos m.h_pos).le
    _ ≤ m.u*(m.b/m.v)^T+m.h*(m.c/m.v)^T := by
      nlinarith [mul_le_mul_of_nonneg_left hpowbc m.h_pos.le]

/-- Archimedean choice supplies a finite Bernoulli witness, without limits. -/
theorem linear_certificate_exists {mass δ target : ℝ} (hmass : 0 < mass)
    (hδ : 0 < δ) : ∃ T : ℕ, target ≤ mass*(1+(T:ℝ)*δ) := by
  obtain ⟨T,hT⟩ := exists_nat_gt (target/(mass*δ))
  have hmul := (div_lt_iff₀ (mul_pos hmass hδ)).mp hT
  exact ⟨T,by nlinarith⟩

theorem advocate_exists : ∃ t, m.advocate t := by
  obtain ⟨T,hT⟩ := linear_certificate_exists m.h_pos (sub_pos.mpr m.cb_gt_one)
    (target := m.u)
  exact ⟨T,m.advocate_bernoulli_certificate T hT⟩

theorem board_exists : ∃ t, m.board t := by
  obtain ⟨T,hT⟩ := linear_certificate_exists (add_pos m.u_pos m.h_pos)
    (sub_pos.mpr m.bv_gt_one) (target := m.r)
  exact ⟨T,m.board_bernoulli_certificate T hT⟩

/-- First nonnegative crossing time, justified by the proved finite certificate. -/
def advocateTime : ℕ := by classical exact Nat.find m.advocate_exists
def boardTime : ℕ := by classical exact Nat.find m.board_exists

theorem advocateTime_spec : m.advocate m.advocateTime := by
  classical
  exact Nat.find_spec m.advocate_exists

theorem boardTime_spec : m.board m.boardTime := by
  classical
  exact Nat.find_spec m.board_exists

theorem advocateTime_le {T : ℕ} (hT : m.advocate T) : m.advocateTime ≤ T := by
  classical
  exact Nat.find_min' m.advocate_exists hT

theorem boardTime_le {T : ℕ} (hT : m.board T) : m.boardTime ≤ T := by
  classical
  exact Nat.find_min' m.board_exists hT

theorem advocateTime_le_bernoulli (T : ℕ)
    (hT : m.u ≤ m.h*(1+(T:ℝ)*(m.c/m.b-1))) : m.advocateTime ≤ T :=
  m.advocateTime_le (m.advocate_bernoulli_certificate T hT)

theorem boardTime_le_bernoulli (T : ℕ)
    (hT : m.r ≤ (m.u+m.h)*(1+(T:ℝ)*(m.b/m.v-1))) : m.boardTime ≤ T :=
  m.boardTime_le (m.board_bernoulli_certificate T hT)

/-- The guard is essential because subtraction of natural times saturates. -/
theorem board_before_advocate_iff :
    m.boardTime < m.advocateTime ↔
      1 ≤ m.advocateTime ∧ m.board (m.advocateTime-1) := by
  constructor
  · intro h
    have hA : 1 ≤ m.advocateTime := by omega
    refine ⟨hA,?_⟩
    exact m.boardTime_spec.trans (m.boardMass_monotone (by omega))
  · rintro ⟨hA,hboard⟩
    have := m.boardTime_le hboard
    omega

theorem boardTime_eq_of_predecessor {T : ℕ} (hT : 1 ≤ T)
    (hcross : m.board T) (hbefore : ¬m.board (T-1)) : m.boardTime = T := by
  have hle := m.boardTime_le hcross
  have hge : T ≤ m.boardTime := by
    by_contra h
    have hlt : m.boardTime < T := by omega
    exact hbefore (m.boardTime_spec.trans (m.boardMass_monotone (by omega)))
  omega

theorem advocateTime_eq_of_predecessor {T : ℕ} (hT : 1 ≤ T)
    (hcross : m.advocate T) (hbefore : ¬m.advocate (T-1)) : m.advocateTime = T := by
  have hle := m.advocateTime_le hcross
  have hge : T ≤ m.advocateTime := by
    by_contra h
    have hlt : m.advocateTime < T := by omega
    exact hbefore (m.advocateTime_spec.trans (m.advocateMass_monotone (by omega)))
  omega

end CrossingModel

/-- Doc A's advocate-first example. -/
def advocateFirstA : CrossingModel where
  r := 99/100
  u := 51/10000
  h := 49/10000
  v := 1
  b := 2
  c := 4
  r_pos := by norm_num
  u_pos := by norm_num
  h_pos := by norm_num
  v_pos := by norm_num
  vb := by norm_num
  bc := by norm_num

/-- Doc A and Doc B's board-first example. -/
def boardFirst : CrossingModel where
  r := 4/5
  u := 9/50
  h := 1/50
  v := 1
  b := 2
  c := 3
  r_pos := by norm_num
  u_pos := by norm_num
  h_pos := by norm_num
  v_pos := by norm_num
  vb := by norm_num
  bc := by norm_num

/-- Doc B's second advocate-first example. -/
def advocateFirstB : CrossingModel where
  r := 49/50
  u := 19/1000
  h := 1/1000
  v := 1
  b := 2
  c := 10
  r_pos := by norm_num
  u_pos := by norm_num
  h_pos := by norm_num
  v_pos := by norm_num
  vb := by norm_num
  bc := by norm_num

theorem advocateFirstA_crossings :
    advocateFirstA.boardTime = 4 ∧ advocateFirstA.advocateTime = 1 := by
  constructor
  · apply CrossingModel.boardTime_eq_of_predecessor <;>
      norm_num [CrossingModel.board, CrossingModel.boardMass, advocateFirstA]
  · apply CrossingModel.advocateTime_eq_of_predecessor <;>
      norm_num [CrossingModel.advocate, CrossingModel.advocateMass, advocateFirstA]

theorem boardFirst_crossings :
    boardFirst.boardTime = 2 ∧ boardFirst.advocateTime = 6 := by
  constructor
  · apply CrossingModel.boardTime_eq_of_predecessor <;>
      norm_num [CrossingModel.board, CrossingModel.boardMass, boardFirst]
  · apply CrossingModel.advocateTime_eq_of_predecessor <;>
      norm_num [CrossingModel.advocate, CrossingModel.advocateMass, boardFirst]

theorem advocateFirstB_crossings :
    advocateFirstB.boardTime = 3 ∧ advocateFirstB.advocateTime = 2 := by
  constructor
  · apply CrossingModel.boardTime_eq_of_predecessor <;>
      norm_num [CrossingModel.board, CrossingModel.boardMass, advocateFirstB]
  · apply CrossingModel.advocateTime_eq_of_predecessor <;>
      norm_num [CrossingModel.advocate, CrossingModel.advocateMass, advocateFirstB]

end
end SEKernel.SilentGene
