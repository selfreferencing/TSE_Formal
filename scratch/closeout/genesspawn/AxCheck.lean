import SEKernel.SilentGene
import SEKernel.GenotypeTransition
import SEKernel.SpawnAllocation
import SEKernel.CorrelatedAnswers
import SEKernel.InnovationArrival

/-!
# Close-out: silent genes, transmission leftovers, and spawning allocation

Finite close-out results for Doc A Parts C/D/E and Doc B Parts C/D/E.
All generation indices start at `t = 0`.  Conditional frequencies always carry
an explicit positive compartment mass.  The silent-allele recursion of Section 1
is a statement about the DETERMINISTIC population-frequency map only (referee G3);
no multigeneration random-voter-slot claim is made.
-/

namespace SEKernel.Closeout.GenesSpawn

open Finset FiniteProbability
open scoped BigOperators
noncomputable section

/-! ## 1. Deterministic multigeneration silent-allele mutation recursion (Doc A C4, Doc B C.5) -/

section SilentRecursion

abbrev Genotype := Bool × Bool

/-- Exact proportional selection (`Law1.step`) packaged as a normalized finite law. -/
def selectionLaw (x : Law Genotype) (f : Genotype → ℝ) (hf : ∀ g, 0 < f g) : Law Genotype where
  mass := Law1.step x.mass f
  nonneg := Law1.step_nonneg x.nonneg (fun g => (hf g).le)
    (Law1.mean_pos x.nonneg x.total hf).le
  total := Law1.step_sum (ne_of_gt (Law1.mean_pos x.nonneg x.total hf))

/-- The scalar affine recursion `z_{t+1} = η + (1-2η) z_t`, `z_0` given. -/
def silentRecursion (eta z0 : ℝ) : ℕ → ℝ
  | 0 => z0
  | t+1 => eta + (1 - 2*eta) * silentRecursion eta z0 t

@[simp] theorem silentRecursion_zero (eta z0 : ℝ) : silentRecursion eta z0 0 = z0 := rfl

@[simp] theorem silentRecursion_succ (eta z0 : ℝ) (t : ℕ) :
    silentRecursion eta z0 (t+1) = eta + (1 - 2*eta) * silentRecursion eta z0 t := rfl

/-- Closed form: `z_t = 1/2 + (z_0 - 1/2)(1-2η)^t`, every `t ≥ 0`, every real `η`. -/
theorem silentRecursion_closed (eta z0 : ℝ) (t : ℕ) :
    silentRecursion eta z0 t = 1/2 + (z0 - 1/2) * (1 - 2*eta)^t := by
  induction t with
  | zero => simp
  | succ t ih => rw [silentRecursion_succ, ih, pow_succ]; ring

/-- `1/2` is a fixed point for every `η`; for `η ≠ 0` (in particular `0<η<1`) it is the
unique fixed point of the affine map. -/
theorem silent_fixed_point_iff {eta : ℝ} (heta : eta ≠ 0) (z : ℝ) :
    eta + (1 - 2*eta) * z = z ↔ z = 1/2 := by
  constructor
  · intro h
    have h2 : eta * (1 - 2*z) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 heta
    · linarith
  · intro h; rw [h]; ring

theorem silent_half_fixed (eta : ℝ) : silentRecursion eta (1/2) = fun _ => 1/2 := by
  funext t; rw [silentRecursion_closed]; ring

/-- Exact distance to the fixed point. -/
theorem silentRecursion_distance (eta z0 : ℝ) (t : ℕ) :
    |silentRecursion eta z0 t - 1/2| = |z0 - 1/2| * |1 - 2*eta|^t := by
  rw [silentRecursion_closed, add_sub_cancel_left, abs_mul, abs_pow]

/-- Contraction modulus for `0<η<1`. -/
theorem silent_contraction {eta : ℝ} (h0 : 0 < eta) (h1 : eta < 1) : |1 - 2*eta| < 1 := by
  rw [abs_lt]; constructor <;> linarith

/-- For `0<η<1` the deterministic recursion tends to the fixed point `1/2`. -/
theorem silentRecursion_tendsto {eta : ℝ} (h0 : 0 < eta) (h1 : eta < 1) (z0 : ℝ) :
    Filter.Tendsto (silentRecursion eta z0) Filter.atTop (nhds (1/2)) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (silent_contraction h0 h1)
  have h := (hpow.const_mul (z0 - 1/2)).const_add (1/2 : ℝ)
  simp only [mul_zero, add_zero] at h
  have he : silentRecursion eta z0 = fun t => 1/2 + (z0 - 1/2) * (1 - 2*eta)^t :=
    funext (silentRecursion_closed eta z0)
  rw [he]
  exact h

/-- Start at zero: `z_t = (1 - (1-2η)^t)/2`. -/
theorem silentRecursion_from_zero (eta : ℝ) (t : ℕ) :
    silentRecursion eta 0 t = (1 - (1 - 2*eta)^t)/2 := by
  rw [silentRecursion_closed]; ring

/-- Monotone approach from zero when `0 ≤ η ≤ 1/2` (the specification's range `μ ≤ 1/2`). -/
theorem silentRecursion_monotone_from_zero {eta : ℝ} (h0 : 0 ≤ eta) (h1 : eta ≤ 1/2) :
    Monotone (silentRecursion eta 0) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [silentRecursion_from_zero, silentRecursion_from_zero, pow_succ]
  have ha : 0 ≤ 1 - 2*eta := by linarith
  have hb : 1 - 2*eta ≤ 1 := by linarith
  have hp : 0 ≤ (1 - 2*eta)^t := pow_nonneg ha t
  nlinarith [mul_le_mul_of_nonneg_left hb hp]

/-- From zero with `0 ≤ η ≤ 1/2`, the trajectory stays in `[0,1/2]`. -/
theorem silentRecursion_from_zero_bounds {eta : ℝ} (h0 : 0 ≤ eta) (h1 : eta ≤ 1/2) (t : ℕ) :
    0 ≤ silentRecursion eta 0 t ∧ silentRecursion eta 0 t ≤ 1/2 := by
  rw [silentRecursion_from_zero]
  have ha : 0 ≤ 1 - 2*eta := by linarith
  have hb : 1 - 2*eta ≤ 1 := by linarith
  have hp : 0 ≤ (1 - 2*eta)^t := pow_nonneg ha t
  have hq : (1 - 2*eta)^t ≤ 1 := pow_le_one₀ ha hb
  constructor <;> linarith

/-- The monotonicity hypothesis `η ≤ 1/2` is needed: at `η = 3/4` the orbit from zero
overshoots and returns (`3/4` then `3/8`). -/
theorem silentRecursion_not_monotone_above_half :
    silentRecursion (3/4) 0 1 = 3/4 ∧ silentRecursion (3/4) 0 2 = 3/8 := by
  constructor <;> norm_num [silentRecursion]

/-- Parameters of the deterministic frequency lifecycle: clonal selection with voter
fitness `v` for both voter genotypes, board fitnesses `b` (plain) and `c` (advocate);
retained elite fraction `e`; offspring copy one selected parent (no crossover), the board
locus is never mutated, and only offspring flip the advocate locus with probability `mu`. -/
structure SilentLifecycle where
  v : ℝ
  b : ℝ
  c : ℝ
  e : ℝ
  mu : ℝ
  v_pos : 0 < v
  b_pos : 0 < b
  c_pos : 0 < c
  e_nonneg : 0 ≤ e
  e_le_one : e ≤ 1
  mu_nonneg : 0 ≤ mu
  mu_le_one : mu ≤ 1

namespace SilentLifecycle

variable (m : SilentLifecycle)

/-- `η = (1-e)μ`. -/
def eta : ℝ := (1 - m.e) * m.mu

/-- Selection step: the actual `Law1.step` with the silent-gene fitnesses. -/
def select (x : Law Genotype) : Law Genotype :=
  selectionLaw x (SilentGene.fitness m.v m.b m.c)
    (SilentGene.fitness_pos m.v_pos m.b_pos m.c_pos)

/-- Offspring law: a selected parent's genotype, then the existing mutation kernel with
board-locus rate zero and advocate-locus rate `mu`. -/
def offspring (x : Law Genotype) : Law Genotype :=
  GenotypeTransition.mutate (m.select x) 0 m.mu le_rfl zero_le_one m.mu_nonneg m.mu_le_one

/-- The deterministic next population-frequency vector: elites unchanged, offspring mutated
(existing `retainedOffspringLaw`). -/
def next (x : Law Genotype) : Law Genotype :=
  GenotypeTransition.retainedOffspringLaw (m.select x) (m.offspring x) m.e m.e_nonneg m.e_le_one

/-- The deterministic multigeneration orbit. -/
def orbit (x : Law Genotype) : ℕ → Law Genotype
  | 0 => x
  | t+1 => m.next (orbit x t)

theorem select_mass (x : Law Genotype) :
    (m.select x).mass = Law1.step x.mass (SilentGene.fitness m.v m.b m.c) := rfl

theorem select_voterShare_pos (x : Law Genotype) (hV : 0 < SilentGene.voterShare x.mass) :
    0 < SilentGene.voterShare (m.select x).mass := by
  have hm := Law1.mean_pos x.nonneg x.total (SilentGene.fitness_pos m.v_pos m.b_pos m.c_pos)
  rw [select_mass]
  unfold SilentGene.voterShare Law1.step
  simp only [SilentGene.fitness, Bool.false_eq_true, ↓reduceIte]
  rw [← add_div, ← add_mul]
  exact div_pos (mul_pos hV m.v_pos) hm

theorem next_voterShare (x : Law Genotype) :
    SilentGene.voterShare (m.next x).mass = SilentGene.voterShare (m.select x).mass := by
  have h := GenotypeTransition.mutate_voterMass (m.select x) 0 m.mu le_rfl zero_le_one
    m.mu_nonneg m.mu_le_one
  unfold GenotypeTransition.voterMass at h
  unfold SilentGene.voterShare next offspring GenotypeTransition.retainedOffspringLaw
    GenotypeTransition.mixture
  simp only
  unfold GenotypeTransition.boardMass at h
  linear_combination (1 - m.e) * h

theorem next_silent_mass (x : Law Genotype) :
    (m.next x).mass (false,true) =
      (1 - m.e) * (m.mu * SilentGene.voterShare (m.select x).mass +
        (1 - 2*m.mu) * (m.select x).mass (false,true)) + m.e * (m.select x).mass (false,true) := by
  have h := GenotypeTransition.mutate_silent_coordinate (m.select x) 0 m.mu le_rfl zero_le_one
    m.mu_nonneg m.mu_le_one
  unfold next offspring GenotypeTransition.retainedOffspringLaw GenotypeTransition.mixture
  simp only
  rw [h]
  unfold GenotypeTransition.voterMass SilentGene.voterShare
  ring

/-- One deterministic generation (Doc A C4 / Doc B (C5a)): with positive voter mass,
`z' = η + (1-2η) z`, `η = (1-e)μ`, independent of `v,b,c`. -/
theorem next_silent_frequency (x : Law Genotype) (hV : 0 < SilentGene.voterShare x.mass) :
    SilentGene.silentAmongVoters (m.next x).mass =
      m.eta + (1 - 2*m.eta) * SilentGene.silentAmongVoters x.mass := by
  have hz := SilentGene.silent_frequency_preserved x m.v_pos m.b_pos m.c_pos hV
  rw [← select_mass] at hz
  have hVy := m.select_voterShare_pos x hV
  rw [← hz]
  unfold SilentGene.silentAmongVoters
  rw [next_voterShare, next_silent_mass]
  unfold eta
  field_simp
  ring

theorem orbit_voterShare_pos (x : Law Genotype) (hV : 0 < SilentGene.voterShare x.mass) (t : ℕ) :
    0 < SilentGene.voterShare (m.orbit x t).mass := by
  induction t with
  | zero => exact hV
  | succ t ih =>
    rw [show m.orbit x (t+1) = m.next (m.orbit x t) from rfl, next_voterShare]
    exact m.select_voterShare_pos _ ih

/-- Multigeneration deterministic recursion: the silent frequency among voters on the orbit
of the deterministic frequency map is exactly the scalar recursion. -/
theorem orbit_silent_frequency (x : Law Genotype) (hV : 0 < SilentGene.voterShare x.mass) (t : ℕ) :
    SilentGene.silentAmongVoters (m.orbit x t).mass =
      silentRecursion m.eta (SilentGene.silentAmongVoters x.mass) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show m.orbit x (t+1) = m.next (m.orbit x t) from rfl, m.next_silent_frequency _ (m.orbit_voterShare_pos x hV t), ih]
    rfl

/-- Closed form on the actual deterministic orbit (Doc B (C5b)). -/
theorem orbit_silent_closed (x : Law Genotype) (hV : 0 < SilentGene.voterShare x.mass) (t : ℕ) :
    SilentGene.silentAmongVoters (m.orbit x t).mass =
      1/2 + (SilentGene.silentAmongVoters x.mass - 1/2) * (1 - 2*m.eta)^t := by
  rw [orbit_silent_frequency m x hV, silentRecursion_closed]

theorem eta_nonneg : 0 ≤ m.eta := mul_nonneg (by linarith [m.e_le_one]) m.mu_nonneg

theorem eta_le_mu : m.eta ≤ m.mu := by
  unfold eta; nlinarith [m.e_nonneg, m.mu_nonneg]

/-- From a voter compartment with no silent carriers and `mu ≤ 1/2`, the orbit's silent
frequency rises monotonically, `z_t = (1-(1-2η)^t)/2 ≤ 1/2`. -/
theorem orbit_monotone_from_zero (x : Law Genotype) (hV : 0 < SilentGene.voterShare x.mass)
    (hz : SilentGene.silentAmongVoters x.mass = 0) (hmu : m.mu ≤ 1/2) :
    Monotone (fun t => SilentGene.silentAmongVoters (m.orbit x t).mass) ∧
      ∀ t, SilentGene.silentAmongVoters (m.orbit x t).mass = (1 - (1 - 2*m.eta)^t)/2 := by
  have he : (fun t => SilentGene.silentAmongVoters (m.orbit x t).mass) = silentRecursion m.eta 0 := by
    funext t; rw [orbit_silent_frequency m x hV, hz]
  refine ⟨?_, fun t => ?_⟩
  · rw [he]; exact silentRecursion_monotone_from_zero m.eta_nonneg (m.eta_le_mu.trans hmu)
  · rw [orbit_silent_frequency m x hV, hz, silentRecursion_from_zero]

/-- For `0 < η < 1` the deterministic orbit's silent frequency tends to `1/2`. -/
theorem orbit_tendsto_half (x : Law Genotype) (hV : 0 < SilentGene.voterShare x.mass)
    (h0 : 0 < m.eta) (h1 : m.eta < 1) :
    Filter.Tendsto (fun t => SilentGene.silentAmongVoters (m.orbit x t).mass)
      Filter.atTop (nhds (1/2)) := by
  have he : (fun t => SilentGene.silentAmongVoters (m.orbit x t).mass) =
      silentRecursion m.eta (SilentGene.silentAmongVoters x.mass) :=
    funext (orbit_silent_frequency m x hV)
  rw [he]; exact silentRecursion_tendsto h0 h1 _

end SilentLifecycle

/-- Doc B's exact target at `e = 1/3`, `μ = 1/10`, `z_0 = 0`: `z_t = (1 - (13/15)^t)/2`. -/
theorem docB_silent_example (t : ℕ) :
    silentRecursion ((1 - 1/3) * (1/10)) 0 t = (1 - (13/15 : ℝ)^t)/2 := by
  rw [silentRecursion_from_zero]; norm_num

end SilentRecursion

/-! ### Doc B C.1 scalar `y` sign and endpoints (expressed advocate frequency among boards) -/

section ScalarY

theorem scalar_y_denominator_pos {b c y : ℝ} (hb : 0 < b) (hc : 0 < c) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < b*(1-y) + c*y := by
  rcases lt_or_eq_of_le hy1 with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos hb (by linarith)) (mul_nonneg hc.le hy0)
  · subst h; simp [hc]

/-- Doc B C.1: `y_s - y = y(1-y)(c-b)/(b(1-y)+cy)`. -/
theorem scalar_y_increment {b c y : ℝ} (hb : 0 < b) (hc : 0 < c) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    c*y/(b*(1-y)+c*y) - y = y*(1-y)*(c-b)/(b*(1-y)+c*y) := by
  have hd := scalar_y_denominator_pos hb hc hy0 hy1
  field_simp
  ring

/-- Doc B C.1: on the interior `0<y<1`, `y_s > y` iff `c > b`. -/
theorem scalar_y_increases_iff {b c y : ℝ} (hb : 0 < b) (hc : 0 < c) (hy0 : 0 < y) (hy1 : y < 1) :
    y < c*y/(b*(1-y)+c*y) ↔ b < c := by
  have hd := scalar_y_denominator_pos hb hc hy0.le hy1.le
  have hinc := scalar_y_increment hb hc hy0.le hy1.le
  have hyy : 0 < y*(1-y) := mul_pos hy0 (by linarith)
  constructor
  · intro h
    have h2 : 0 < y*(1-y)*(c-b)/(b*(1-y)+c*y) := by linarith
    have h3 : 0 < y*(1-y)*(c-b) := by
      by_contra hn; push_neg at hn; exact absurd h2 (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hn hd.le))
    by_contra hbc; push_neg at hbc
    nlinarith [mul_nonneg hyy.le (sub_nonneg.mpr hbc)]
  · intro h
    have : 0 < y*(1-y)*(c-b)/(b*(1-y)+c*y) := div_pos (mul_pos hyy (by linarith)) hd
    linarith

/-- Doc B C.1 endpoints: `y = 0` and `y = 1` are fixed. -/
theorem scalar_y_endpoints {b c : ℝ} (hc : 0 < c) :
    c*0/(b*(1-0)+c*0) = 0 ∧ c*1/(b*(1-1)+c*1) = 1 := by
  constructor
  · simp
  · simp [ne_of_gt hc]

/-- The scalar map is the actual `Law1.step` update of the expressed advocate frequency. -/
theorem actual_y_step (x : Law Genotype) {v b c : ℝ} (hv : 0 < v) (hb : 0 < b) (hc : 0 < c)
    (hB : 0 < SilentGene.boardShare x.mass) :
    SilentGene.advocateAmongBoards (Law1.step x.mass (SilentGene.fitness v b c)) =
      c * SilentGene.advocateAmongBoards x.mass /
        (b * (1 - SilentGene.advocateAmongBoards x.mass) + c * SilentGene.advocateAmongBoards x.mass) := by
  rw [SilentGene.advocate_frequency_step x hv hb hc hB]
  unfold SilentGene.advocateAmongBoards SilentGene.boardShare at *
  have h10 := x.nonneg (true,false)
  have hne : x.mass (true,false) + x.mass (true,true) ≠ 0 := ne_of_gt hB
  rw [one_sub_div hne]
  field_simp
  ring_nf

/-- Doc B (C1a): `B_s = B[b(1-y)+cy]/((1-B)v + B[b(1-y)+cy])` for the actual step, `0<B`. -/
theorem actual_B_step (x : Law Genotype) {v b c : ℝ}
    (hB : 0 < SilentGene.boardShare x.mass) :
    SilentGene.boardShare (Law1.step x.mass (SilentGene.fitness v b c)) =
      SilentGene.boardShare x.mass * (b * (1 - SilentGene.advocateAmongBoards x.mass) +
          c * SilentGene.advocateAmongBoards x.mass) /
        ((1 - SilentGene.boardShare x.mass) * v + SilentGene.boardShare x.mass *
          (b * (1 - SilentGene.advocateAmongBoards x.mass) +
            c * SilentGene.advocateAmongBoards x.mass)) := by
  have hkey : SilentGene.boardShare x.mass * (b * (1 - SilentGene.advocateAmongBoards x.mass) +
      c * SilentGene.advocateAmongBoards x.mass) = b * x.mass (true,false) + c * x.mass (true,true) := by
    unfold SilentGene.advocateAmongBoards
    unfold SilentGene.boardShare at hB ⊢
    field_simp
    ring
  have hV : SilentGene.voterShare x.mass = 1 - SilentGene.boardShare x.mass := by
    have := GenotypeTransition.four_masses_sum x
    unfold SilentGene.voterShare SilentGene.boardShare; linarith
  rw [hkey, ← hV]
  have hm := SilentGene.clonal_mean x.mass v b c
  unfold SilentGene.boardShare Law1.step
  simp only [SilentGene.fitness, Bool.false_eq_true, ↓reduceIte]
  rw [hm, ← add_div]
  ring

end ScalarY


/-! ## 2. Allocation converse (Doc A E2, Doc B E.3 (E3c)) and natural-vector conversion -/

section AllocationConverse

open SpawnAllocation
open scoped Classical

variable {J : Type*} [Fintype J] {K : J → ℕ}

/-- Value of an actual finite set of call slots. -/
def slotValue (d : CallSlot K → ℝ) (A : Finset (CallSlot K)) : ℝ := ∑ i ∈ A, d i

omit [Fintype J] in
theorem slot_eq_iff (i i' : CallSlot K) : i = i' ↔ i.1 = i'.1 ∧ i.2.val = i'.2.val := by
  rcases i with ⟨j, r⟩
  rcases i' with ⟨j', r'⟩
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    simp only at h1 h2
    subst h1
    rw [Fin.ext h2]

omit [Fintype J] in
/-- A set whose membership is a per-task threshold is prefix closed. -/
theorem prefixClosed_of_threshold (A : Finset (CallSlot K)) (k : J → ℕ)
    (h : ∀ j (r : Fin (K j)), Sigma.mk j r ∈ A ↔ r.val < k j) : PrefixClosed A := by
  intro j r q hqr hr
  rw [h] at hr ⊢
  exact lt_of_le_of_lt (Fin.le_def.mp hqr) hr

/-- The next available call on task `t` (zero-based index `n_t`). -/
def nextSlot (A : Finset (CallSlot K)) (t : J) (ht : taskCount A t < K t) : CallSlot K :=
  ⟨t, ⟨taskCount A t, ht⟩⟩

/-- The last allocated call on task `s` (zero-based index `n_s - 1`). -/
def lastSlot (A : Finset (CallSlot K)) (s : J) (hs : 0 < taskCount A s) : CallSlot K :=
  ⟨s, ⟨taskCount A s - 1, by have := taskCount_le_cap A s; omega⟩⟩

/-- Doc B (E3c) / Doc A E2 exchange criterion, in pairwise form (no infinities):
exhausted budget: every available next call is worth at most every allocated last call;
remaining budget: every available next call is worth zero. -/
structure ExchangeCriterion (d : CallSlot K → ℝ) (B : ℕ) (A : Finset (CallSlot K)) : Prop where
  exhausted : A.card = B → ∀ (t s : J) (ht : taskCount A t < K t) (hs : 0 < taskCount A s),
    d (nextSlot A t ht) ≤ d (lastSlot A s hs)
  slack : A.card < B → ∀ (t : J) (ht : taskCount A t < K t), d (nextSlot A t ht) = 0

section PrefixFacts
variable {A : Finset (CallSlot K)} (hA : PrefixClosed A)
include hA

theorem nextSlot_not_mem (t : J) (ht : taskCount A t < K t) : nextSlot A t ht ∉ A := by
  unfold nextSlot
  rw [prefix_mem_iff_taskCount A hA]
  exact lt_irrefl _

theorem lastSlot_mem (s : J) (hs : 0 < taskCount A s) : lastSlot A s hs ∈ A := by
  unfold lastSlot
  rw [prefix_mem_iff_taskCount A hA]
  simp only
  omega

theorem not_mem_le_next (d : CallSlot K → ℝ) (hdec : ∀ j, Antitone (fun r : Fin (K j) => d ⟨j, r⟩))
    (t : J) (r : Fin (K t)) (hr : Sigma.mk t r ∉ A) :
    ∃ ht : taskCount A t < K t, d ⟨t, r⟩ ≤ d (nextSlot A t ht) := by
  rw [prefix_mem_iff_taskCount A hA] at hr
  have ht : taskCount A t < K t := by have := r.isLt; omega
  exact ⟨ht, hdec t (show (⟨taskCount A t, ht⟩ : Fin (K t)) ≤ r from Fin.le_def.mpr (by simp; omega))⟩

theorem mem_ge_last (d : CallSlot K → ℝ) (hdec : ∀ j, Antitone (fun r : Fin (K j) => d ⟨j, r⟩))
    (s : J) (r : Fin (K s)) (hr : Sigma.mk s r ∈ A) :
    ∃ hs : 0 < taskCount A s, d (lastSlot A s hs) ≤ d ⟨s, r⟩ := by
  rw [prefix_mem_iff_taskCount A hA] at hr
  have hs : 0 < taskCount A s := by omega
  refine ⟨hs, hdec s (show r ≤ (⟨taskCount A s - 1, _⟩ : Fin (K s)) from Fin.le_def.mpr ?_)⟩
  simp only; omega

/-- Adding the next call on `t` keeps prefix closure. -/
theorem insert_next_prefix (t : J) (ht : taskCount A t < K t) :
    PrefixClosed (insert (nextSlot A t ht) A) := by
  classical
  apply prefixClosed_of_threshold _ (fun j => if j = t then taskCount A t + 1 else taskCount A j)
  intro j r
  rw [Finset.mem_insert, slot_eq_iff, prefix_mem_iff_taskCount A hA]
  simp only [nextSlot]
  by_cases hj : j = t
  · subst hj; simp only [↓reduceIte, true_and]; omega
  · simp [hj]

/-- Moving one call from task `s` to a different task `t` keeps prefix closure. -/
theorem swap_prefix (t s : J) (hts : t ≠ s) (ht : taskCount A t < K t) (hs : 0 < taskCount A s) :
    PrefixClosed (insert (nextSlot A t ht) (A.erase (lastSlot A s hs))) := by
  classical
  apply prefixClosed_of_threshold _
    (fun j => if j = t then taskCount A t + 1 else if j = s then taskCount A s - 1 else taskCount A j)
  intro j r
  rw [Finset.mem_insert, Finset.mem_erase, ne_eq, slot_eq_iff, slot_eq_iff,
    prefix_mem_iff_taskCount A hA]
  simp only [nextSlot, lastSlot]
  by_cases hj : j = t
  · subst hj
    simp only [↓reduceIte, true_and, hts, false_and, not_false_eq_true]
    omega
  · by_cases hjs : j = s
    · subst hjs; simp only [hj, ↓reduceIte, false_and, false_or, true_and]; omega
    · simp [hj, hjs]

end PrefixFacts

/-- Necessity: an optimal feasible prefix allocation satisfies the exchange criterion
(both budget cases).  Nonnegativity is used only to turn `≤ 0` into `= 0`. -/
theorem optimal_implies_exchange (d : CallSlot K → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hdec : ∀ j, Antitone (fun r : Fin (K j) => d ⟨j, r⟩)) (B : ℕ) (A : FeasibleAllocation K B)
    (hopt : ∀ C : FeasibleAllocation K B, slotValue d C.val ≤ slotValue d A.val) :
    ExchangeCriterion d B A.val := by
  classical
  have hA := A.property.1
  constructor
  · intro hcard t s ht hs
    by_cases hts : t = s
    · subst hts
      unfold nextSlot lastSlot
      exact hdec t (Fin.le_def.mpr (by simp only; omega))
    · have hlast := lastSlot_mem hA s hs
      have hnot : nextSlot A.val t ht ∉ A.val.erase (lastSlot A.val s hs) :=
        fun h => nextSlot_not_mem hA t ht (Finset.mem_of_mem_erase h)
      have hc : (insert (nextSlot A.val t ht) (A.val.erase (lastSlot A.val s hs))).card ≤ B := by
        rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hlast]
        have := Finset.card_pos.mpr ⟨_, hlast⟩
        omega
      have h := hopt ⟨_, swap_prefix hA t s hts ht hs, hc⟩
      unfold slotValue at h
      simp only at h
      rw [Finset.sum_insert hnot] at h
      have he := Finset.sum_erase_add A.val (f := d) hlast
      linarith
  · intro hlt t ht
    have hnot := nextSlot_not_mem hA t ht
    have hc : (insert (nextSlot A.val t ht) A.val).card ≤ B := by
      rw [Finset.card_insert_of_notMem hnot]; omega
    have h := hopt ⟨_, insert_next_prefix hA t ht, hc⟩
    unfold slotValue at h
    simp only at h
    rw [Finset.sum_insert hnot] at h
    exact le_antisymm (by linarith) (hd _)

/-- Sufficiency: the exchange criterion produces a threshold certificate. -/
theorem exchange_implies_certificate (d : CallSlot K → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hdec : ∀ j, Antitone (fun r : Fin (K j) => d ⟨j, r⟩)) (B : ℕ) (A : FeasibleAllocation K B)
    (hx : ExchangeCriterion d B A.val) : ∃ lambda, SlotCertificate d B A.val lambda := by
  classical
  have hA := A.property.1
  have hB := A.property.2
  rcases lt_or_eq_of_le hB with hlt | hcard
  · refine ⟨0, le_rfl, hB, fun i _ => hd i, ?_, by simp⟩
    rintro ⟨t, r⟩ hr
    obtain ⟨ht, hle⟩ := not_mem_le_next hA d hdec t r hr
    rw [hx.slack hlt t ht] at hle
    exact hle
  · by_cases hne : A.val.Nonempty
    · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image A.val d hne
      refine ⟨d i0, hd i0, hB, fun i hi => hmin i hi, ?_, by simp [hcard]⟩
      rintro ⟨t, r⟩ hr
      obtain ⟨ht, hle⟩ := not_mem_le_next hA d hdec t r hr
      rcases i0 with ⟨s, r0⟩
      obtain ⟨hs, hlast⟩ := mem_ge_last hA d hdec s r0 hi0
      exact hle.trans ((hx.exhausted hcard t s ht hs).trans hlast)
    · have he : A.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      refine ⟨∑ i, d i, Finset.sum_nonneg (fun i _ => hd i), hB, by simp [he], ?_, by simp [hcard]⟩
      intro i _
      exact Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)

/-- Doc A E2 / Doc B (E3c): a feasible prefix allocation is optimal iff it satisfies the
exchange criterion (both budget cases), iff it has a threshold certificate. -/
theorem prefix_optimal_iff_exchange (d : CallSlot K → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hdec : ∀ j, Antitone (fun r : Fin (K j) => d ⟨j, r⟩)) (B : ℕ) (A : FeasibleAllocation K B) :
    ((∀ C : FeasibleAllocation K B, slotValue d C.val ≤ slotValue d A.val) ↔
        ExchangeCriterion d B A.val) ∧
      (ExchangeCriterion d B A.val ↔ ∃ lambda, SlotCertificate d B A.val lambda) := by
  have hsuff : ∀ lambda, SlotCertificate d B A.val lambda →
      ∀ C : FeasibleAllocation K B, slotValue d C.val ≤ slotValue d A.val := by
    intro lambda h C
    have := certified_allocation_optimal K B 0 d A lambda h C
    simpa [allocationReturn, slotValue] using this
  refine ⟨⟨optimal_implies_exchange d hd hdec B A, fun hx => ?_⟩,
    ⟨exchange_implies_certificate d hd hdec B A, fun ⟨lambda, h⟩ => ?_⟩⟩
  · obtain ⟨lambda, h⟩ := exchange_implies_certificate d hd hdec B A hx
    exact hsuff lambda h
  · exact optimal_implies_exchange d hd hdec B A (hsuff lambda h)

/-! ### Natural-vector allocations `k_j ≤ K_j`, `Σ k_j ≤ B` and prefix slot sets -/

/-- A separately defined arbitrary feasible natural-vector allocation. -/
abbrev NatAllocation (K : J → ℕ) (B : ℕ) := {k : J → ℕ // (∀ j, k j ≤ K j) ∧ ∑ j, k j ≤ B}

/-- The prefix slot set of a natural vector: the first `k_j` calls of task `j`. -/
def prefixSet (K : J → ℕ) (k : J → ℕ) : Finset (CallSlot K) :=
  Finset.univ.filter (fun i => i.2.val < k i.1)

theorem mem_prefixSet (k : J → ℕ) (i : CallSlot K) : i ∈ prefixSet K k ↔ i.2.val < k i.1 := by
  simp [prefixSet]

theorem prefixSet_closed (k : J → ℕ) : PrefixClosed (prefixSet K k) :=
  prefixClosed_of_threshold _ k (fun j r => mem_prefixSet k ⟨j, r⟩)

theorem taskCount_prefixSet (k : J → ℕ) (hk : ∀ j, k j ≤ K j) (j : J) :
    taskCount (prefixSet K k) j = k j := by
  classical
  unfold taskCount taskSlots
  have he : (Finset.univ.filter (fun r : Fin (K j) => Sigma.mk j r ∈ prefixSet K k)) =
      Finset.univ.filter (fun r : Fin (K j) => r.val < k j) := by
    ext r; simp [mem_prefixSet]
  rw [he]
  exact Epistemic.prefixPositions_card (hk j)

theorem prefixSet_card (k : J → ℕ) (hk : ∀ j, k j ≤ K j) :
    (prefixSet K k).card = ∑ j, k j := by
  rw [← taskCount_sum]
  exact Finset.sum_congr rfl (fun j _ => taskCount_prefixSet k hk j)

theorem prefixSet_taskCount (A : Finset (CallSlot K)) (hA : PrefixClosed A) :
    prefixSet K (taskCount A) = A := by
  ext ⟨j, r⟩
  rw [mem_prefixSet, prefix_mem_iff_taskCount A hA]

def natToPrefix {B : ℕ} (k : NatAllocation K B) : FeasibleAllocation K B :=
  ⟨prefixSet K k.val, prefixSet_closed k.val, by rw [prefixSet_card k.val k.property.1]; exact k.property.2⟩

def feasibleToNat {B : ℕ} (A : FeasibleAllocation K B) : NatAllocation K B :=
  ⟨taskCount A.val, fun j => taskCount_le_cap A.val j, by rw [taskCount_sum]; exact A.property.2⟩

/-- Lossless conversion between natural vectors and feasible prefix allocations. -/
def natPrefixEquiv (K : J → ℕ) (B : ℕ) : NatAllocation K B ≃ FeasibleAllocation K B where
  toFun := natToPrefix
  invFun := feasibleToNat
  left_inv k := Subtype.ext (funext (fun j => taskCount_prefixSet k.val k.property.1 j))
  right_inv A := Subtype.ext (prefixSet_taskCount A.val A.property.1)

theorem toPrefix_taskCount {B : ℕ} (k : NatAllocation K B) (j : J) :
    taskCount (natToPrefix k).val j = k.val j := taskCount_prefixSet k.val k.property.1 j

/-- The task-level reach objective `R(k) = Σ_j w_j [α_j - (α_j-β_j)(1-p_j)^{k_j}]`. -/
def reachObjective (weight alpha beta p : J → ℝ) (k : J → ℕ) : ℝ :=
  ∑ j, weight j * reachPayoff (alpha j) (beta j) (p j) (k j)

/-- The reach slot values `m_{j,r} = w_j (α_j-β_j) p_j (1-p_j)^r`. -/
def reachSlot (K : J → ℕ) (weight alpha beta p : J → ℝ) : CallSlot K → ℝ :=
  fun i => weight i.1 * reachMarginal (alpha i.1) (beta i.1) (p i.1) i.2.val

theorem reachObjective_eq_slotValue {B : ℕ} (weight alpha beta p : J → ℝ) (k : NatAllocation K B) :
    reachObjective weight alpha beta p k.val =
      (∑ j, weight j * beta j) + slotValue (reachSlot K weight alpha beta p) (natToPrefix k).val := by
  have h := reach_allocation_objective (natToPrefix k).val (natToPrefix k).property.1 weight alpha beta p
  simp only [toPrefix_taskCount] at h
  exact h

/-- Optimality over separately defined natural vectors follows from the certified prefix
results: an optimal natural vector exists, with `Σ k_j = min(B, Σ K_j)`. -/
theorem exists_optimal_nat_allocation (K : J → ℕ) (B : ℕ) (weight alpha beta p : J → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hresponse : ∀ j, 0 ≤ beta j ∧ beta j ≤ alpha j ∧ alpha j ≤ 1)
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) :
    ∃ k : NatAllocation K B, ∑ j, k.val j = min B (∑ j, K j) ∧
      ∀ l : NatAllocation K B, reachObjective weight alpha beta p l.val ≤
        reachObjective weight alpha beta p k.val := by
  obtain ⟨A, lambda, hsize, _, hopt⟩ :=
    exists_optimal_reach_allocation K B weight alpha beta p hw hresponse hp
  refine ⟨(feasibleToNat A), ?_, fun l => ?_⟩
  · change ∑ j, taskCount A.val j = _
    rw [taskCount_sum, hsize]
  · have h := hopt (natToPrefix l)
    simp only [toPrefix_taskCount] at h
    exact h

/-- Optimality of a natural vector over natural vectors is optimality of its prefix set
over feasible prefix allocations. -/
theorem nat_optimal_iff_prefix_optimal {B : ℕ} (weight alpha beta p : J → ℝ) (k : NatAllocation K B) :
    (∀ l : NatAllocation K B, reachObjective weight alpha beta p l.val ≤
        reachObjective weight alpha beta p k.val) ↔
      ∀ C : FeasibleAllocation K B, slotValue (reachSlot K weight alpha beta p) C.val ≤
        slotValue (reachSlot K weight alpha beta p) (natToPrefix k).val := by
  constructor
  · intro h C
    have h1 := h (feasibleToNat C)
    rw [reachObjective_eq_slotValue, reachObjective_eq_slotValue] at h1
    have hC : natToPrefix (feasibleToNat C) = C := (natPrefixEquiv K B).right_inv C
    rw [hC] at h1
    linarith
  · intro h l
    rw [reachObjective_eq_slotValue, reachObjective_eq_slotValue]
    linarith [h (natToPrefix l)]

/-- Doc B (E3c) on natural vectors, both budget cases.  With the marginal
`m_{j,r} = w_j(α_j-β_j)p_j(1-p_j)^r`: an exhausted allocation is optimal iff
`m_{t,k_t} ≤ m_{s,k_s-1}` whenever `k_t < K_t` and `k_s > 0`; an allocation with budget
remaining is optimal iff `m_{t,k_t} = 0` whenever `k_t < K_t`. -/
theorem nat_allocation_optimal_iff {B : ℕ} (weight alpha beta p : J → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hab : ∀ j, beta j ≤ alpha j) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (k : NatAllocation K B) :
    (∀ l : NatAllocation K B, reachObjective weight alpha beta p l.val ≤
        reachObjective weight alpha beta p k.val) ↔
      ((∑ j, k.val j = B → ∀ t s, k.val t < K t → 0 < k.val s →
          weight t * reachMarginal (alpha t) (beta t) (p t) (k.val t) ≤
            weight s * reachMarginal (alpha s) (beta s) (p s) (k.val s - 1)) ∧
        (∑ j, k.val j < B → ∀ t, k.val t < K t →
          weight t * reachMarginal (alpha t) (beta t) (p t) (k.val t) = 0)) := by
  have hd : ∀ i, 0 ≤ reachSlot K weight alpha beta p i := fun i =>
    mul_nonneg (hw i.1) (reach_marginals_nonneg (hab i.1) (hp i.1).1 (hp i.1).2 i.2.val)
  have hdec : ∀ j, Antitone (fun r : Fin (K j) => reachSlot K weight alpha beta p ⟨j, r⟩) :=
    fun j r q hrq => mul_le_mul_of_nonneg_left
      (reach_marginals_decreasing (hab j) (hp j).1 (hp j).2 hrq) (hw j)
  rw [nat_optimal_iff_prefix_optimal, (prefix_optimal_iff_exchange _ hd hdec B (natToPrefix k)).1]
  have hcard : (natToPrefix k).val.card = ∑ j, k.val j := prefixSet_card k.val k.property.1
  have htc := toPrefix_taskCount k
  constructor
  · rintro ⟨hex, hsl⟩
    refine ⟨fun hB t s ht hs => ?_, fun hB t ht => ?_⟩
    · have h := hex (hcard.trans hB) t s (by rw [htc]; exact ht) (by rw [htc]; exact hs)
      simpa [nextSlot, lastSlot, reachSlot, htc] using h
    · have h := hsl (hcard.trans_lt hB) t (by rw [htc]; exact ht)
      simpa [nextSlot, reachSlot, htc] using h
  · rintro ⟨hex, hsl⟩
    refine ⟨fun hB t s ht hs => ?_, fun hB t ht => ?_⟩
    · have h := hex (hcard.symm.trans hB) t s (by rw [← htc]; exact ht) (by rw [← htc]; exact hs)
      simpa [nextSlot, lastSlot, reachSlot, htc] using h
    · have h := hsl (hcard.symm.trans_lt hB) t (by rw [← htc]; exact ht)
      simpa [nextSlot, reachSlot, htc] using h


/-- Doc A E2 shadow-price form on natural vectors: `k` is optimal iff there is `λ ≥ 0` with
`m_{t,k_t-1} ≥ λ` whenever `k_t > 0`, `m_{t,k_t} ≤ λ` whenever `k_t < K_t`, and
`λ (B - Σ_t k_t) = 0`. -/
theorem nat_allocation_optimal_iff_shadow_price {B : ℕ} (weight alpha beta p : J → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hab : ∀ j, beta j ≤ alpha j) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (k : NatAllocation K B) :
    (∀ l : NatAllocation K B, reachObjective weight alpha beta p l.val ≤
        reachObjective weight alpha beta p k.val) ↔
      ∃ lambda : ℝ, 0 ≤ lambda ∧
        (∀ t, 0 < k.val t →
          lambda ≤ weight t * reachMarginal (alpha t) (beta t) (p t) (k.val t - 1)) ∧
        (∀ t, k.val t < K t →
          weight t * reachMarginal (alpha t) (beta t) (p t) (k.val t) ≤ lambda) ∧
        lambda * ((B : ℝ) - ∑ j, (k.val j : ℝ)) = 0 := by
  have hd : ∀ i, 0 ≤ reachSlot K weight alpha beta p i := fun i =>
    mul_nonneg (hw i.1) (reach_marginals_nonneg (hab i.1) (hp i.1).1 (hp i.1).2 i.2.val)
  have hdecN : ∀ j, Antitone (fun r : ℕ => weight j * reachMarginal (alpha j) (beta j) (p j) r) :=
    fun j r q hrq => mul_le_mul_of_nonneg_left
      (reach_marginals_decreasing (hab j) (hp j).1 (hp j).2 hrq) (hw j)
  have hdec : ∀ j, Antitone (fun r : Fin (K j) => reachSlot K weight alpha beta p ⟨j, r⟩) :=
    fun j r q hrq => hdecN j hrq
  have hcard : ((natToPrefix k).val.card : ℝ) = ∑ j, (k.val j : ℝ) := by
    have h := prefixSet_card (K := K) k.val k.property.1
    change ((prefixSet K k.val).card : ℝ) = _
    rw [h]; push_cast; rfl
  have hiff := prefix_optimal_iff_exchange _ hd hdec B (natToPrefix k)
  rw [nat_optimal_iff_prefix_optimal, hiff.1, hiff.2]
  have hmem : ∀ (t : J) (r : Fin (K t)), (Sigma.mk t r : CallSlot K) ∈ (natToPrefix k).val ↔
      r.val < k.val t := fun t r => mem_prefixSet k.val ⟨t, r⟩
  constructor
  · rintro ⟨lambda, hc⟩
    refine ⟨lambda, hc.nonneg, fun t ht => ?_, fun t ht => ?_, ?_⟩
    · have hlt : k.val t - 1 < K t := by have := k.property.1 t; omega
      have := hc.selected ⟨t, ⟨k.val t - 1, hlt⟩⟩ ((hmem t _).mpr (by simp only; omega))
      simpa [reachSlot] using this
    · have := hc.unselected ⟨t, ⟨k.val t, ht⟩⟩ (by rw [hmem]; simp)
      simpa [reachSlot] using this
    · have := hc.slack; rwa [hcard] at this
  · rintro ⟨lambda, h0, hsel, hun, hslack⟩
    refine ⟨lambda, h0, (natToPrefix k).property.2, ?_, ?_, by rw [hcard]; exact hslack⟩
    · rintro ⟨t, r⟩ hr
      rw [hmem] at hr
      have hpos : 0 < k.val t := by omega
      exact (hsel t hpos).trans (hdecN t (show r.val ≤ k.val t - 1 by omega))
    · rintro ⟨t, r⟩ hr
      rw [hmem] at hr
      have hlt : k.val t < K t := by have := r.isLt; omega
      exact (hdecN t (show k.val t ≤ r.val by omega)).trans (hun t hlt)

end AllocationConverse


/-! ## 3. General marginal identities (Doc B E1c–g, Doc A E1) and the payoff-gap bound E4c -/

section MarginalIdentities

open Epistemic
open scoped Classical

section Generic
variable {Ω : Type*} [Fintype Ω]

/-- Three-cell response with fixed pick-up constants: `κK` if the benchmark event `V` holds,
otherwise `κP` if a correct answer was posted (`C`), otherwise `κN`. -/
def cellPayoff (kK kP kN : ℝ) (V C : Ω → Prop) (ω : Ω) : ℝ :=
  if V ω then kK else if C ω then kP else kN

/-- The institution's success probability `F` under an actual finite law. -/
def threeCellPayoff (L : Law Ω) (kK kP kN : ℝ) (V C : Ω → Prop) : ℝ :=
  L.expect (cellPayoff kK kP kN V C)

omit [Fintype Ω] in
theorem cellPayoff_decomp (kK kP kN : ℝ) (V C : Ω → Prop) (ω : Ω) :
    cellPayoff kK kP kN V C ω = kN + (kK - kN) * (if V ω then 1 else 0) +
      (kP - kN) * (if ¬ V ω ∧ C ω then 1 else 0) := by
  unfold cellPayoff
  by_cases hv : V ω <;> by_cases hc : C ω <;> simp [hv, hc]

/-- Doc B (E1c): `F = κN + (κK-κN) Pr(V) + (κP-κN) Pr(Vᶜ ∩ C)`. -/
theorem threeCell_decomposition (L : Law Ω) (kK kP kN : ℝ) (V C : Ω → Prop) :
    threeCellPayoff L kK kP kN V C =
      kN + (kK - kN) * L.prob V + (kP - kN) * L.prob (fun ω => ¬ V ω ∧ C ω) := by
  unfold threeCellPayoff
  rw [show cellPayoff kK kP kN V C = fun ω => kN + (kK - kN) * (if V ω then 1 else 0) +
      (kP - kN) * (if ¬ V ω ∧ C ω then 1 else 0) from funext (cellPayoff_decomp kK kP kN V C)]
  rw [L.expect_add, L.expect_add, L.expect_const, L.expect_const_mul, L.expect_const_mul,
    L.expect_indicator, L.expect_indicator]

/-- Doc B (E1d), generic form: if the posting event grows by `H`, only `Vᶜ ∩ Cᶜ ∩ H` changes cell. -/
theorem threeCell_increment (L : Law Ω) (kK kP kN : ℝ) (V C C' H : Ω → Prop)
    (hC : ∀ ω, C' ω ↔ C ω ∨ H ω) :
    threeCellPayoff L kK kP kN V C' - threeCellPayoff L kK kP kN V C =
      (kP - kN) * L.prob (fun ω => ¬ V ω ∧ ¬ C ω ∧ H ω) := by
  rw [threeCell_decomposition, threeCell_decomposition]
  have h : L.prob (fun ω => ¬ V ω ∧ C' ω) =
      L.prob (fun ω => ¬ V ω ∧ C ω) + L.prob (fun ω => ¬ V ω ∧ ¬ C ω ∧ H ω) := by
    unfold Law.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    have hω := hC ω
    by_cases hv : V ω <;> by_cases hc : C ω <;> by_cases hh : H ω <;> simp_all
  rw [h]; ring

/-- When the benchmark can only be right if the correct answer was posted (`V ⊆ C`). -/
theorem prob_not_and_of_subset (L : Law Ω) (V C : Ω → Prop) (hVC : ∀ ω, V ω → C ω) :
    L.prob (fun ω => ¬ V ω ∧ C ω) = L.prob C - L.prob V := by
  have h : L.prob C = L.prob V + L.prob (fun ω => ¬ V ω ∧ C ω) := by
    unfold Law.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hv : V ω
    · simp [hv, hVC ω hv]
    · simp [hv]
  linarith

/-- Doc B (E1e), generic form: with `V ⊆ C`,
`F = κN + (κP-κN) Pr(C) + (κK-κP) Pr(V)`. -/
theorem threeCell_posted_decomposition (L : Law Ω) (kK kP kN : ℝ) (V C : Ω → Prop)
    (hVC : ∀ ω, V ω → C ω) :
    threeCellPayoff L kK kP kN V C = kN + (kP - kN) * L.prob C + (kK - kP) * L.prob V := by
  rw [threeCell_decomposition, prob_not_and_of_subset L V C hVC]; ring

theorem prob_prod_and {Λ : Type*} [Fintype Λ] (L : Law Ω) (M : Law Λ) (E : Ω → Prop) (F : Λ → Prop) :
    (L.prod M).prob (fun ω => E ω.1 ∧ F ω.2) = L.prob E * M.prob F := by
  rw [← Law.expect_indicator, ← L.expect_indicator, ← M.expect_indicator,
    ← Law.expect_prod_mul]
  congr 1
  funext ω
  by_cases he : E ω.1 <;> by_cases hf : F ω.2 <;> simp [he, hf]

end Generic

section Words
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem reaches_succ_iff {N : ℕ} (z : OrderedWord N A) (k : ℕ) (hk : k < N) (a : A) :
    reaches z (k+1) a ↔ reaches z k a ∨ z ⟨k, hk⟩ = some a := by
  constructor
  · rintro ⟨i, hi, hz⟩
    by_cases hik : i.val < k
    · exact Or.inl ⟨i, hik, hz⟩
    · right
      have hi' : i = ⟨k, hk⟩ := Fin.ext (by simp only; omega)
      rw [← hi']; exact hz
  · rintro (⟨i, hi, hz⟩ | h)
    · exact ⟨i, by omega, hz⟩
    · exact ⟨⟨k, hk⟩, by simp, h⟩

theorem prob_label_eq (π : Law (Option A)) (b : Option A) : π.prob (fun x => x = b) = π.mass b := by
  unfold Law.prob
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [hc]
  · simp

/-- First correct proposal exactly at zero-based position `k`: probability `(1-p)^k p`. -/
theorem first_hit_probability (π : Law (Option A)) (N k : ℕ) (hk : k < N) (a : A) :
    (iidWordLaw π N).prob (fun z => ¬ reaches z k a ∧ z ⟨k, hk⟩ = some a) =
      (1 - π.mass (some a))^k * π.mass (some a) := by
  have he : (fun z : OrderedWord N A => ¬ reaches z k a ∧ z ⟨k, hk⟩ = some a) =
      (fun z => ∀ i, (fun (i : Fin N) (x : Option A) =>
        (i.val < k → x ≠ some a) ∧ (i.val = k → x = some a)) i (z i)) := by
    funext z
    apply propext
    constructor
    · rintro ⟨hnr, hz⟩ i
      refine ⟨fun hi hzi => hnr ⟨i, hi, hzi⟩, fun hi => ?_⟩
      have hi' : i = ⟨k, hk⟩ := Fin.ext hi
      rw [hi']; exact hz
    · intro h
      exact ⟨fun ⟨i, hi, hzi⟩ => (h i).1 hi hzi, (h ⟨k, hk⟩).2 rfl⟩
  have hcoord (i : Fin N) :
      π.prob (fun x => (i.val < k → x ≠ some a) ∧ (i.val = k → x = some a)) =
        (if i.val < k then 1 - π.mass (some a) else 1) *
          (if i = ⟨k, hk⟩ then π.mass (some a) else 1) := by
    by_cases hi : i.val < k
    · have hne : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at hi; simp at hi
      have hne' : i.val ≠ k := by omega
      simp only [hi, true_implies, hne', false_implies, and_true, ↓reduceIte, hne, mul_one]
      exact prob_single_label_compl π (some a)
    · by_cases hik : i = ⟨k, hk⟩
      · subst hik
        simp only [lt_self_iff_false, false_implies, true_implies, true_and, ↓reduceIte, one_mul]
        exact prob_label_eq π (some a)
      · have hv : i.val ≠ k := fun h => hik (Fin.ext h)
        simp only [hi, false_implies, hv, and_self, ↓reduceIte, hik, mul_one]
        exact π.prob_true
  rw [he, iidWordLaw, prob_pi_forall (fun _ : Fin N => π)
    (fun (i : Fin N) (x : Option A) => (i.val < k → x ≠ some a) ∧ (i.val = k → x = some a))]
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib, Finset.prod_ite, Fintype.prod_ite_eq']
  simp [prefixPositions_card hk.le]

/-- Doc A E1 / Doc B (E1d) on actual iid proposals: with ANY fixed benchmark event `V` on the
same word, `F_{k+1}-F_k = (κP-κN) Pr(Vᶜ ∩ C_kᶜ ∩ {X_k = a*})` (zero-based position `k`). -/
theorem fixed_benchmark_marginal (π : Law (Option A)) (N k : ℕ) (hk : k < N) (a : A)
    (kK kP kN : ℝ) (V : OrderedWord N A → Prop) :
    threeCellPayoff (iidWordLaw π N) kK kP kN V (fun z => reaches z (k+1) a) -
      threeCellPayoff (iidWordLaw π N) kK kP kN V (fun z => reaches z k a) =
      (kP - kN) * (iidWordLaw π N).prob
        (fun z => ¬ V z ∧ ¬ reaches z k a ∧ z ⟨k, hk⟩ = some a) :=
  threeCell_increment _ kK kP kN V _ _ _ (fun z => reaches_succ_iff z k hk a)

/-- Doc A E1 bound: `|F_{k+1}-F_k| ≤ |κP-κN| p(1-p)^k`, for any fixed benchmark. -/
theorem fixed_benchmark_marginal_abs_le (π : Law (Option A)) (N k : ℕ) (hk : k < N) (a : A)
    (kK kP kN : ℝ) (V : OrderedWord N A → Prop) :
    |threeCellPayoff (iidWordLaw π N) kK kP kN V (fun z => reaches z (k+1) a) -
      threeCellPayoff (iidWordLaw π N) kK kP kN V (fun z => reaches z k a)| ≤
      |kP - kN| * (π.mass (some a) * (1 - π.mass (some a))^k) := by
  rw [fixed_benchmark_marginal π N k hk a, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [abs_of_nonneg (Law.prob_nonneg _ _)]
  calc
    _ ≤ (iidWordLaw π N).prob (fun z => ¬ reaches z k a ∧ z ⟨k, hk⟩ = some a) :=
      Law.prob_mono _ (fun z hz => hz.2)
    _ = _ := by rw [first_hit_probability]; ring

/-- Doc B: if the whole benchmark is independent of all proposer draws (an actual product law),
the marginal factors as `(κP-κN)(1-v)p(1-p)^k`. -/
theorem independent_benchmark_marginal {ΩB : Type*} [Fintype ΩB] (LB : Law ΩB) (VB : ΩB → Prop)
    (π : Law (Option A)) (N k : ℕ) (hk : k < N) (a : A) (kK kP kN : ℝ) :
    threeCellPayoff (LB.prod (iidWordLaw π N)) kK kP kN (fun ω => VB ω.1)
        (fun ω => reaches ω.2 (k+1) a) -
      threeCellPayoff (LB.prod (iidWordLaw π N)) kK kP kN (fun ω => VB ω.1)
        (fun ω => reaches ω.2 k a) =
      (kP - kN) * ((1 - LB.prob VB) * (π.mass (some a) * (1 - π.mass (some a))^k)) := by
  rw [threeCell_increment _ kK kP kN _ _ _ (fun ω => ω.2 ⟨k, hk⟩ = some a)
    (fun ω => reaches_succ_iff ω.2 k hk a)]
  rw [show (fun ω : ΩB × OrderedWord N A => ¬ VB ω.1 ∧ ¬ reaches ω.2 k a ∧ ω.2 ⟨k, hk⟩ = some a) =
      (fun ω => (fun x => ¬ VB x) ω.1 ∧ (fun z => ¬ reaches z k a ∧ z ⟨k, hk⟩ = some a) ω.2) from rfl,
    prob_prod_and LB (iidWordLaw π N) (fun x => ¬ VB x)
      (fun z => ¬ reaches z k a ∧ z ⟨k, hk⟩ = some a), LB.prob_compl, first_hit_probability]
  ring

/-- Doc B (E1e) on actual iid proposals with the benchmark a vote on the very `k` posted answers:
`F_k = κN + (κP-κN)[1-(1-p)^k] + (κK-κP) V_k`, `V_k` the actual vote accuracy. -/
theorem posted_benchmark_payoff (π : Law (Option A)) (k : ℕ) (a : A) (kK kP kN : ℝ) :
    threeCellPayoff (iidWordLaw π k) kK kP kN (fun z => correctVote z a) (fun z => reaches z k a) =
      kN + (kP - kN) * (1 - (1 - π.mass (some a))^k) + (kK - kP) * voteAccuracy π k a := by
  rw [threeCell_posted_decomposition _ _ _ _ _ _ (fun z hz => correctVote_reaches_full z a hz)]
  have hr := reach_full_probability π k a
  unfold reachProbability at hr
  rw [hr]
  rfl

/-- Doc B (E1f). -/
theorem posted_benchmark_marginal (π : Law (Option A)) (k : ℕ) (a : A) (kK kP kN : ℝ) :
    threeCellPayoff (iidWordLaw π (k+1)) kK kP kN (fun z => correctVote z a)
        (fun z => reaches z (k+1) a) -
      threeCellPayoff (iidWordLaw π k) kK kP kN (fun z => correctVote z a) (fun z => reaches z k a) =
      (kP - kN) * (π.mass (some a) * (1 - π.mass (some a))^k) +
        (kK - kP) * (voteAccuracy π (k+1) a - voteAccuracy π k a) := by
  rw [posted_benchmark_payoff, posted_benchmark_payoff, pow_succ]; ring

/-- Doc B (E1g): the premium marginal over the benchmark itself. -/
theorem posted_benchmark_premium_marginal (π : Law (Option A)) (k : ℕ) (a : A) (kK kP kN : ℝ) :
    (threeCellPayoff (iidWordLaw π (k+1)) kK kP kN (fun z => correctVote z a)
        (fun z => reaches z (k+1) a) - voteAccuracy π (k+1) a) -
      (threeCellPayoff (iidWordLaw π k) kK kP kN (fun z => correctVote z a)
        (fun z => reaches z k a) - voteAccuracy π k a) =
      (kP - kN) * (π.mass (some a) * (1 - π.mass (some a))^k) -
        (1 - kK + kP) * (voteAccuracy π (k+1) a - voteAccuracy π k a) := by
  rw [posted_benchmark_payoff, posted_benchmark_payoff, pow_succ]; ring

end Words

end MarginalIdentities

section PayoffGap

open SpawnAllocation

/-- Doc B (E4c): finite expected-regret bound for exact constant-fitness selection on complete
allocations, `f = c₀ + R > 0`: `R_max - E_{x_t} R ≤ (R_max-R_min) (1-s₀)/s₀ ρ^t`.
`R_max` is certified by `hmax`; the optimal set is the equality level set of `f` at `c₀+R_max`. -/
theorem selection_regret_bound {ι : Type*} [Fintype ι] (x : Law ι) (R : ι → ℝ)
    (c0 Rmax Rmin rho : ℝ) (hf : ∀ i, 0 < c0 + R i) (hmax : ∀ i, R i ≤ Rmax)
    (hmin : ∀ i, Rmin ≤ R i) (hpos : 0 < c0 + Rmax) (hrho : 0 ≤ rho) (hrho' : rho < 1)
    (hgap : ∀ i ∉ maximizers (fun i => c0 + R i) (c0 + Rmax), c0 + R i ≤ rho * (c0 + Rmax))
    (hstart : 0 < ∑ i ∈ maximizers (fun i => c0 + R i) (c0 + Rmax), x.mass i) (t : ℕ) :
    Rmax - Law1.mean (SilentGene.clonalTrajectory x (fun i => c0 + R i) t) R ≤
      (Rmax - Rmin) *
        (((1 - ∑ i ∈ maximizers (fun i => c0 + R i) (c0 + Rmax), x.mass i) /
          (∑ i ∈ maximizers (fun i => c0 + R i) (c0 + Rmax), x.mass i)) * rho^t) := by
  classical
  set f : ι → ℝ := fun i => c0 + R i with hfdef
  set M := maximizers f (c0 + Rmax) with hM
  set y := SilentGene.clonalTrajectory x f t with hy
  have hmass := suboptimal_mass_bound x hf (c0 + Rmax) rho (fun i => by simp [hmax i]) hpos
    hrho hrho' hgap hstart t
  have hy1 : ∑ i, y i = 1 := SilentGene.clonalTrajectory_total x hf t
  have hy0 : ∀ i, 0 ≤ y i := SilentGene.clonalTrajectory_nonneg x hf t
  obtain ⟨i0, hi0⟩ : M.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hstart
    simp at hstart
  have hspread : 0 ≤ Rmax - Rmin := by linarith [hmax i0, hmin i0]
  have hreg : Rmax - Law1.mean y R = ∑ i, y i * (Rmax - R i) := by
    unfold Law1.mean
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hy1, one_mul]
  have hsplit : ∑ i, y i * (Rmax - R i) = ∑ i ∈ Mᶜ, y i * (Rmax - R i) := by
    rw [← Finset.sum_add_sum_compl M]
    have h0 : ∑ i ∈ M, y i * (Rmax - R i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have he : f i = c0 + Rmax := (Finset.mem_filter.mp hi).2
      have : R i = Rmax := by simp only [f] at he; linarith
      rw [this]; ring
    rw [h0, zero_add]
  rw [hreg, hsplit]
  calc
    _ ≤ ∑ i ∈ Mᶜ, y i * (Rmax - Rmin) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (by linarith [hmin i]) (hy0 i))
    _ = (Rmax - Rmin) * ∑ i ∈ Mᶜ, y i := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hspread

end PayoffGap


/-! ## 4. Genotype-transition leftovers (Doc A C2, Doc B C.3/C.4) -/

section TransmissionLeftovers

open GenotypeTransition

/-- Doc A C2 signed four-coordinate recombination formulas, `D` the linkage disequilibrium:
`R_11 = y_11 - rD`, `R_10 = y_10 + rD`, `R_01 = y_01 + rD`, `R_00 = y_00 - rD`. -/
theorem recombine_signed (y : Law GenotypeTransition.Genotype) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (recombine y r h0 h1).mass (true,true) = y.mass (true,true) - r * linkage y ∧
    (recombine y r h0 h1).mass (true,false) = y.mass (true,false) + r * linkage y ∧
    (recombine y r h0 h1).mass (false,true) = y.mass (false,true) + r * linkage y ∧
    (recombine y r h0 h1).mass (false,false) = y.mass (false,false) - r * linkage y := by
  have hs := four_masses_sum y
  simp only [recombine_mass, linkage, boardMass, advocateMass]
  refine ⟨by ring, ?_, ?_, ?_⟩
  · linear_combination (r * (y.mass (true,false) + y.mass (true,true))) * hs
  · linear_combination (r * (y.mass (false,true) + y.mass (true,true))) * hs
  · linear_combination (r * (y.mass (false,false) - y.mass (true,true))) * hs

theorem recombine_voterMass (y : Law GenotypeTransition.Genotype) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    voterMass (recombine y r h0 h1) = voterMass y := by
  rw [voterMass_eq_one_sub_boardMass, voterMass_eq_one_sub_boardMass, recombine_boardMass]

/-- Board-conditional advocate frequency `q` and voter-conditional silent frequency `z`. -/
def condQ (y : Law GenotypeTransition.Genotype) : ℝ := y.mass (true,true) / boardMass y
def condZ (y : Law GenotypeTransition.Genotype) : ℝ := y.mass (false,true) / voterMass y

/-- On the interior, `h = Xq + (1-X)z`. -/
theorem advocate_conditional_decomposition (y : Law GenotypeTransition.Genotype)
    (hX : 0 < boardMass y) (hV : 0 < voterMass y) :
    advocateMass y = boardMass y * condQ y + (1 - boardMass y) * condZ y := by
  rw [← voterMass_eq_one_sub_boardMass]
  unfold condQ condZ advocateMass
  field_simp
  ring

/-- Doc A C2: `q_R = (1-r)q + rh = q - r(1-X)(q-z)`, positive compartments explicit. -/
theorem recombine_condQ (y : Law GenotypeTransition.Genotype) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hX : 0 < boardMass y) (hV : 0 < voterMass y) :
    condQ (recombine y r h0 h1) = (1 - r) * condQ y + r * advocateMass y ∧
      condQ (recombine y r h0 h1) = condQ y - r * (1 - boardMass y) * (condQ y - condZ y) := by
  have hq : condQ (recombine y r h0 h1) = (1 - r) * condQ y + r * advocateMass y := by
    unfold condQ
    rw [recombine_boardMass, recombine_mass]
    unfold boardMass advocateMass
    simp only
    unfold boardMass at hX
    field_simp
  refine ⟨hq, ?_⟩
  rw [hq, advocate_conditional_decomposition y hX hV]
  ring

/-- Doc A C2: `z_R = (1-r)z + rh = z + rX(q-z)`. -/
theorem recombine_condZ (y : Law GenotypeTransition.Genotype) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hX : 0 < boardMass y) (hV : 0 < voterMass y) :
    condZ (recombine y r h0 h1) = (1 - r) * condZ y + r * advocateMass y ∧
      condZ (recombine y r h0 h1) = condZ y + r * boardMass y * (condQ y - condZ y) := by
  have hz : condZ (recombine y r h0 h1) = (1 - r) * condZ y + r * advocateMass y := by
    unfold condZ
    rw [recombine_voterMass, recombine_mass]
    unfold voterMass advocateMass
    simp only
    unfold voterMass at hV
    field_simp
  refine ⟨hz, ?_⟩
  rw [hz, advocate_conditional_decomposition y hX hV]
  ring

/-- Doc A C2: `D = X(1-X)(q-z)` on the interior. -/
theorem linkage_conditional (y : Law GenotypeTransition.Genotype)
    (hX : 0 < boardMass y) (hV : 0 < voterMass y) :
    linkage y = boardMass y * (1 - boardMass y) * (condQ y - condZ y) := by
  have hs := four_masses_sum y
  have key : boardMass y * voterMass y * (condQ y - condZ y) =
      voterMass y * y.mass (true,true) - boardMass y * y.mass (false,true) := by
    unfold condQ condZ
    field_simp
  rw [← voterMass_eq_one_sub_boardMass, key]
  unfold linkage boardMass advocateMass voterMass
  linear_combination (-(y.mass (true,true))) * hs

/-- Effective recombination coefficient after elite mixing (Doc A C2): retaining elite
fraction `e` of the survivor law `y` and filling the rest with `R_r(y)` offspring is exactly
`R_{(1-e)r}(y)`. -/
theorem elite_mixing_recombination (y : Law GenotypeTransition.Genotype) (r e : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (he0 : 0 ≤ e) (he1 : e ≤ 1) (g : GenotypeTransition.Genotype) :
    (retainedOffspringLaw y (recombine y r hr0 hr1) e he0 he1).mass g =
      (recombine y ((1 - e) * r) (mul_nonneg (by linarith) hr0)
        (by nlinarith)).mass g := by
  unfold retainedOffspringLaw mixture
  simp only
  rw [recombine_mass, recombine_mass]
  ring

/-- With actual independent survivor-index crossover (`r_off = 1/2`), the population
coefficient is `(1-e)/2`. -/
theorem elite_independent_crossover {S : ℕ} (s : Fin S → GenotypeTransition.Genotype) (hS : 0 < S)
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (g : GenotypeTransition.Genotype) :
    (retainedOffspringLaw (survivorLaw s hS) (independentRosterCrossover s hS) e he0 he1).mass g =
      (recombine (survivorLaw s hS) ((1 - e) * (1/2)) (by nlinarith) (by nlinarith)).mass g := by
  rw [← elite_mixing_recombination (survivorLaw s hS) (1/2) e (by norm_num) (by norm_num) he0 he1 g]
  unfold retainedOffspringLaw mixture
  simp only
  rw [independentRosterCrossover_mass]

/-- With actual distinct-parent crossover (`r_off = S/(2(S-1))`), the population coefficient
is `(1-e) S/(2(S-1))`. -/
theorem elite_distinct_crossover {S : ℕ} (s : Fin S → GenotypeTransition.Genotype) (hS : 1 < S)
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (g : GenotypeTransition.Genotype) :
    (retainedOffspringLaw (survivorLaw s (by omega)) (distinctRosterCrossover s hS) e he0 he1).mass g =
      (recombine (survivorLaw s (by omega)) ((1 - e) * distinctRho S)
        (mul_nonneg (by linarith) (distinctRho_bounds hS).1)
        (by nlinarith [(distinctRho_bounds hS).1, (distinctRho_bounds hS).2])).mass g := by
  rw [← elite_mixing_recombination (survivorLaw s (by omega)) (distinctRho S) e
    (distinctRho_bounds hS).1 (distinctRho_bounds hS).2 he0 he1 g]
  unfold retainedOffspringLaw mixture
  simp only
  rw [distinctRosterCrossover_mass]

/-- Uniform-slot identification (Doc B (C4b)): for an actual survivor roster of size `S` and
`M` conditionally iid offspring, the expected genotype frequency of the next population of
`S+M` slots is the elite mixture with elite fraction `S/(S+M)`. -/
theorem uniform_slot_identification {S M : ℕ} (s : Fin S → GenotypeTransition.Genotype)
    (hS : 0 < S) (child : Law GenotypeTransition.Genotype) (g : GenotypeTransition.Genotype) :
    (broodHistogramLaw s child M).expect (fun n => (histogramCount n g : ℝ) / ((S : ℝ) + M)) =
      (retainedOffspringLaw (survivorLaw s hS) child ((S : ℝ) / ((S : ℝ) + M))
        (by positivity) (div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)])
          (by positivity))).mass g := by
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have hSM : (0:ℝ) < (S : ℝ) + M := by positivity
  simp only [div_eq_mul_inv]
  rw [Law.expect_mul_const, broodHistogram_expectedCount]
  unfold retainedOffspringLaw mixture
  simp only
  rw [survivorLaw_mass]
  field_simp
  ring


/-- Doc B C.5 second counterexample (selection plus recombination numeric witness): from
`x_00 = x_11 = 1/2`, `v = b = 1`, `c = 2`, exact selection gives `(1/3, 0, 0, 2/3)` and actual
independent-parent crossover gives silent mass `1/9` and voter mass `1/3`: the silent frequency
among voters rises from `0` to `1/3`. -/
def halfDiagonal : Law GenotypeTransition.Genotype where
  mass g := if g = (false,false) ∨ g = (true,true) then 1/2 else 0
  nonneg g := by split_ifs <;> norm_num
  total := by simp [Fintype.sum_prod_type]; norm_num

theorem selection_recombination_creates_silent :
    let y := selectionLaw halfDiagonal (SilentGene.fitness 1 1 2)
      (SilentGene.fitness_pos one_pos one_pos two_pos)
    SilentGene.silentAmongVoters halfDiagonal.mass = 0 ∧
      y.mass (false,false) = 1/3 ∧ y.mass (true,true) = 2/3 ∧
      y.mass (false,true) = 0 ∧ y.mass (true,false) = 0 ∧
      (independentCrossover y).mass (false,true) = 1/9 ∧
      voterMass (independentCrossover y) = 1/3 ∧
      (independentCrossover y).mass (false,true) / voterMass (independentCrossover y) = 1/3 := by
  intro y
  have hy : ∀ g, y.mass g = Law1.step halfDiagonal.mass (SilentGene.fitness 1 1 2) g := fun g => rfl
  have hmean : Law1.mean halfDiagonal.mass (SilentGene.fitness 1 1 2) = 3/2 := by
    norm_num [Law1.mean, Fintype.sum_prod_type, halfDiagonal, SilentGene.fitness]
  have h00 : y.mass (false,false) = 1/3 := by
    rw [hy]; unfold Law1.step; rw [hmean]; norm_num [halfDiagonal, SilentGene.fitness]
  have h11 : y.mass (true,true) = 2/3 := by
    rw [hy]; unfold Law1.step; rw [hmean]; norm_num [halfDiagonal, SilentGene.fitness]
  have h01 : y.mass (false,true) = 0 := by
    rw [hy]; unfold Law1.step; rw [hmean]; simp [halfDiagonal, SilentGene.fitness]
  have h10 : y.mass (true,false) = 0 := by
    rw [hy]; unfold Law1.step; rw [hmean]; simp [halfDiagonal, SilentGene.fitness]
  have hR : ∀ g, (independentCrossover y).mass g =
      (recombine y (1/2) (by norm_num) (by norm_num)).mass g := independentCrossover_mass y
  have hR01 : (independentCrossover y).mass (false,true) = 1/9 := by
    rw [hR, recombine_mass]; simp only; simp only [h00, h01, h11]; norm_num
  have hV : voterMass (independentCrossover y) = 1/3 := by
    unfold voterMass
    rw [hR, hR, recombine_mass, recombine_mass]; simp only; simp only [h00, h01, h11, h10]; norm_num
  refine ⟨?_, h00, h11, h01, h10, hR01, hV, ?_⟩
  · simp [SilentGene.silentAmongVoters, halfDiagonal]
  · rw [hR01, hV]; norm_num


/-! ### Doc A C4 mutation-order countermodel (all individuals: selection, `R_r`, B and A flips) -/

theorem mutate_board_coordinate (q : Law GenotypeTransition.Genotype) (muB muA : ℝ)
    (hB0 : 0 ≤ muB) (hB1 : muB ≤ 1) (hA0 : 0 ≤ muA) (hA1 : muA ≤ 1) :
    (mutate q muB muA hB0 hB1 hA0 hA1).mass (true,true) =
      muA*((1-muB)*boardMass q+muB*voterMass q)+
        (1-2*muA)*((1-muB)*q.mass (true,true)+muB*q.mass (false,true)) := by
  unfold voterMass boardMass
  simp only [mutate_mass, Fintype.sum_prod_type, Fintype.sum_bool]
  simp
  ring

theorem mutate_boardMass (q : Law GenotypeTransition.Genotype) (muB muA : ℝ)
    (hB0 : 0 ≤ muB) (hB1 : muB ≤ 1) (hA0 : 0 ≤ muA) (hA1 : muA ≤ 1) :
    boardMass (mutate q muB muA hB0 hB1 hA0 hA1) = (1-muB)*boardMass q+muB*voterMass q := by
  have h := mutate_voterMass q muB muA hB0 hB1 hA0 hA1
  have h1 := voterMass_eq_one_sub_boardMass (mutate q muB muA hB0 hB1 hA0 hA1)
  have h2 := voterMass_eq_one_sub_boardMass q
  linear_combination h1 - h - h2

/-- Parameters of Doc A's all-individual lifecycle: `c ≥ b`, `μ_B, μ_A ≤ 1/2`. -/
structure OrderModel where
  v : ℝ
  b : ℝ
  c : ℝ
  r : ℝ
  muB : ℝ
  muA : ℝ
  v_pos : 0 < v
  b_pos : 0 < b
  bc : b ≤ c
  r0 : 0 ≤ r
  r1 : r ≤ 1
  muB0 : 0 ≤ muB
  muB_half : muB ≤ 1/2
  muA0 : 0 ≤ muA
  muA_half : muA ≤ 1/2

namespace OrderModel

variable (m : OrderModel)

theorem c_pos : 0 < m.c := lt_of_lt_of_le m.b_pos m.bc

def selected (x : Law GenotypeTransition.Genotype) : Law GenotypeTransition.Genotype :=
  selectionLaw x (SilentGene.fitness m.v m.b m.c) (SilentGene.fitness_pos m.v_pos m.b_pos m.c_pos)

def recombined (x : Law GenotypeTransition.Genotype) : Law GenotypeTransition.Genotype :=
  recombine (m.selected x) m.r m.r0 m.r1

/-- One generation: selection, recombination `R_r`, then independent B and A flips. -/
def step (x : Law GenotypeTransition.Genotype) : Law GenotypeTransition.Genotype :=
  mutate (m.recombined x) m.muB m.muA m.muB0 (by linarith [m.muB_half]) m.muA0
    (by linarith [m.muA_half])

def orbit (x : Law GenotypeTransition.Genotype) : ℕ → Law GenotypeTransition.Genotype
  | 0 => x
  | t+1 => m.step (orbit x t)

theorem selected_compartments (x : Law GenotypeTransition.Genotype) (hX : 0 < boardMass x)
    (hV : 0 < voterMass x) : 0 < boardMass (m.selected x) ∧ 0 < voterMass (m.selected x) := by
  have hm := Law1.mean_pos x.nonneg x.total
    (SilentGene.fitness_pos m.v_pos m.b_pos m.c_pos)
  have h10 := x.nonneg (true,false)
  have h11 := x.nonneg (true,true)
  unfold boardMass voterMass at *
  simp only [selected, selectionLaw, Law1.step, SilentGene.fitness, Bool.false_eq_true, ↓reduceIte]
  rw [← add_div, ← add_div]
  constructor
  · apply div_pos _ hm
    rcases lt_or_eq_of_le h10 with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos h m.b_pos) (mul_nonneg h11 m.c_pos.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg h10 m.b_pos.le) (mul_pos (by linarith) m.c_pos)
  · exact div_pos (by rw [← add_mul]; exact mul_pos hV m.v_pos) hm

theorem selected_condZ (x : Law GenotypeTransition.Genotype) (hV : 0 < voterMass x) :
    condZ (m.selected x) = condZ x :=
  SilentGene.silent_frequency_preserved x m.v_pos m.b_pos m.c_pos hV

theorem selected_condQ_ge (x : Law GenotypeTransition.Genotype) (hX : 0 < boardMass x) :
    condQ x ≤ condQ (m.selected x) := by
  have h := SilentGene.advocate_frequency_step x m.v_pos m.b_pos m.c_pos hX
  change condQ (m.selected x) = _ at h
  rw [h]
  have h10 := x.nonneg (true,false)
  have h11 := x.nonneg (true,true)
  have hd : 0 < m.b * x.mass (true,false) + m.c * x.mass (true,true) := by
    unfold boardMass at hX
    rcases lt_or_eq_of_le h10 with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos m.b_pos h) (mul_nonneg m.c_pos.le h11)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg m.b_pos.le h10) (mul_pos m.c_pos (by linarith))
  unfold condQ
  rw [div_le_div_iff₀ hX hd]
  unfold boardMass
  nlinarith [mul_nonneg (mul_nonneg h10 h11) (sub_nonneg.mpr m.bc)]

/-- One generation of the countermodel: both roles stay present, `q ≥ z` is preserved, and
`z' ≥ μ_A + (1-2μ_A) z`. -/
theorem step_order (x : Law GenotypeTransition.Genotype) (hX : 0 < boardMass x)
    (hV : 0 < voterMass x) (hqz : condZ x ≤ condQ x) :
    0 < boardMass (m.step x) ∧ 0 < voterMass (m.step x) ∧
      condZ (m.step x) ≤ condQ (m.step x) ∧
      m.muA + (1 - 2*m.muA) * condZ x ≤ condZ (m.step x) := by
  obtain ⟨hXy, hVy⟩ := m.selected_compartments x hX hV
  have hzy := m.selected_condZ x hV
  have hqy := m.selected_condQ_ge x hX
  set y := m.selected x with hydef
  set R := m.recombined x with hRdef
  have hRy : R = recombine y m.r m.r0 m.r1 := rfl
  have hXR : boardMass R = boardMass y := by rw [hRy, recombine_boardMass]
  have hVR : voterMass R = voterMass y := by rw [hRy, recombine_voterMass]
  have hzR := (recombine_condZ y m.r m.r0 m.r1 hXy hVy).2
  have hqR := (recombine_condQ y m.r m.r0 m.r1 hXy hVy).2
  rw [← hRy] at hzR hqR
  set X := boardMass y
  set V := voterMass y
  set qy := condQ y
  set zy := condZ y
  have hVX : V = 1 - X := voterMass_eq_one_sub_boardMass y
  have hzR_ge : zy ≤ condZ R := by
    rw [hzR]; nlinarith [mul_nonneg (mul_nonneg m.r0 hXy.le) (sub_nonneg.mpr (hzy ▸ hqz.trans hqy))]
  have hqzR : condZ R ≤ condQ R := by
    rw [hzR, hqR]
    have : 0 ≤ qy - zy := by rw [hzy]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr m.r1) this]
  have hR01 : R.mass (false,true) = V * condZ R := by
    unfold condZ; rw [hVR]; field_simp
  have hR11 : R.mass (true,true) = X * condQ R := by
    unfold condQ; rw [hXR]; field_simp
  set zR := condZ R
  set qR := condQ R
  set a := m.muA
  set bB := m.muB
  have hstep : m.step x = mutate R bB a m.muB0 (by linarith [m.muB_half]) m.muA0
      (by linarith [m.muA_half]) := rfl
  have hX' : boardMass (m.step x) = (1-bB)*X + bB*V := by
    rw [hstep, mutate_boardMass, hXR, hVR]
  have hV' : voterMass (m.step x) = (1-bB)*V + bB*X := by
    rw [hstep, mutate_voterMass, hXR, hVR]
  have h01' : (m.step x).mass (false,true) = a*((1-bB)*V + bB*X) + (1-2*a)*((1-bB)*(V*zR) + bB*(X*qR)) := by
    rw [hstep, mutate_silent_coordinate, hXR, hVR, hR01, hR11]
  have h11' : (m.step x).mass (true,true) = a*((1-bB)*X + bB*V) + (1-2*a)*((1-bB)*(X*qR) + bB*(V*zR)) := by
    rw [hstep, mutate_board_coordinate, hXR, hVR, hR01, hR11]
  have hb0 := m.muB0
  have hb1 := m.muB_half
  have ha0 := m.muA0
  have ha1 := m.muA_half
  have hXpos : 0 < (1-bB)*X + bB*V := by nlinarith
  have hVpos : 0 < (1-bB)*V + bB*X := by nlinarith
  refine ⟨by rw [hX']; exact hXpos, by rw [hV']; exact hVpos, ?_, ?_⟩
  · unfold condZ condQ
    rw [hX', hV', h01', h11', div_le_div_iff₀ hVpos hXpos]
    have key : (a*((1-bB)*X + bB*V) + (1-2*a)*((1-bB)*(X*qR) + bB*(V*zR))) * ((1-bB)*V + bB*X) -
        (a*((1-bB)*V + bB*X) + (1-2*a)*((1-bB)*(V*zR) + bB*(X*qR))) * ((1-bB)*X + bB*V) =
        (1-2*a)*(1-2*bB)*X*V*(qR - zR) := by ring
    have : 0 ≤ (1-2*a)*(1-2*bB)*X*V*(qR - zR) := by
      apply mul_nonneg _ (sub_nonneg.mpr hqzR)
      apply mul_nonneg _ hVy.le
      apply mul_nonneg _ hXy.le
      apply mul_nonneg <;> linarith
    linarith
  · rw [← hzy]
    unfold condZ
    rw [hV', h01', le_div_iff₀ hVpos]
    have key : a*((1-bB)*V + bB*X) + (1-2*a)*((1-bB)*(V*zR) + bB*(X*qR)) -
        (a + (1 - 2*a)*zy) * ((1-bB)*V + bB*X) =
        (1-2*a)*((1-bB)*V*(zR - zy) + bB*X*(qR - zy)) := by ring
    have hzq : zy ≤ qR := hzR_ge.trans hqzR
    have : 0 ≤ (1-2*a)*((1-bB)*V*(zR - zy) + bB*X*(qR - zy)) := by
      apply mul_nonneg (by linarith)
      apply add_nonneg
      · apply mul_nonneg (mul_nonneg (by linarith) hVy.le) (sub_nonneg.mpr hzR_ge)
      · apply mul_nonneg (mul_nonneg hb0 hXy.le) (sub_nonneg.mpr hzq)
    linarith

/-- Doc A C4 countermodel: starting with both roles present and `q_0 ≥ z_0`, for every `t`
both roles stay present, `q_t ≥ z_t`, and `z_{t+1} ≥ μ_A + (1-2μ_A) z_t`. -/
theorem orbit_order (x : Law GenotypeTransition.Genotype) (hX : 0 < boardMass x)
    (hV : 0 < voterMass x) (hqz : condZ x ≤ condQ x) (t : ℕ) :
    (0 < boardMass (m.orbit x t) ∧ 0 < voterMass (m.orbit x t) ∧
      condZ (m.orbit x t) ≤ condQ (m.orbit x t)) ∧
      m.muA + (1 - 2*m.muA) * condZ (m.orbit x t) ≤ condZ (m.orbit x (t+1)) := by
  have hinv : ∀ t, 0 < boardMass (m.orbit x t) ∧ 0 < voterMass (m.orbit x t) ∧
      condZ (m.orbit x t) ≤ condQ (m.orbit x t) := by
    intro t
    induction t with
    | zero => exact ⟨hX, hV, hqz⟩
    | succ t ih =>
      obtain ⟨h1, h2, h3, _⟩ := m.step_order _ ih.1 ih.2.1 ih.2.2
      exact ⟨h1, h2, h3⟩
  refine ⟨hinv t, ?_⟩
  exact (m.step_order _ (hinv t).1 (hinv t).2.1 (hinv t).2.2).2.2.2

/-- Consequently `z_t` dominates the neutral mutation trajectory from `z_0`. -/
theorem orbit_ge_neutral (x : Law GenotypeTransition.Genotype) (hX : 0 < boardMass x)
    (hV : 0 < voterMass x) (hqz : condZ x ≤ condQ x) (t : ℕ) :
    silentRecursion m.muA (condZ x) t ≤ condZ (m.orbit x t) := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [silentRecursion_succ]
    have h := (m.orbit_order x hX hV hqz t).2
    have hc : 0 ≤ 1 - 2*m.muA := by linarith [m.muA_half]
    nlinarith [mul_le_mul_of_nonneg_left ih hc]

end OrderModel


/-! ### Doc A C4 arbitrary-survivor conditional expected-ratio binomial formula -/

/-- Binomial mixture `Σ_{j ≤ n} C(n,j) x^j (1-x)^{n-j} T(j)`. -/
def binomialMix (x : ℝ) (n : ℕ) (T : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * x^j * (1-x)^(n-j) * T j

theorem binomialMix_succ (x : ℝ) (n : ℕ) (T : ℕ → ℝ) :
    binomialMix x (n+1) T = x * binomialMix x n (fun j => T (j+1)) + (1-x) * binomialMix x n T := by
  unfold binomialMix
  rw [Finset.sum_range_succ']
  have h1 : ∀ i ∈ Finset.range (n+1),
      ((n+1).choose (i+1) : ℝ) * x^(i+1) * (1-x)^(n+1-(i+1)) * T (i+1) =
        x * ((n.choose i : ℝ) * x^i * (1-x)^(n-i) * T (i+1)) +
          (n.choose (i+1) : ℝ) * x^(i+1) * (1-x)^(n-i) * T (i+1) := by
    intro i _
    rw [Nat.choose_succ_succ, Nat.cast_add, Nat.add_sub_add_right]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : (∑ i ∈ Finset.range (n+1), (n.choose (i+1) : ℝ) * x^(i+1) * (1-x)^(n-i) * T (i+1)) =
      (1-x) * ∑ i ∈ Finset.range n, (n.choose (i+1) : ℝ) * x^(i+1) * (1-x)^(n-(i+1)) * T (i+1) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, zero_mul,
      add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [show n - i = (n - (i+1)) + 1 by omega, pow_succ]
    ring
  rw [h2, Finset.sum_range_succ' (fun j => (n.choose j : ℝ) * x^j * (1-x)^(n-j) * T j)]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, one_mul, mul_one]
  ring

theorem iid_expect_succ (θ : Law GenotypeTransition.Genotype) (O : ℕ)
    (F : (Fin (O+1) → GenotypeTransition.Genotype) → ℝ) :
    (Epistemic.iidAlphabetLaw θ (O+1)).expect F =
      ∑ g, θ.mass g * (Epistemic.iidAlphabetLaw θ O).expect (fun w => F (Fin.cons g w)) := by
  unfold Epistemic.iidAlphabetLaw Law.expect Law1.mean Law.pi
  simp only
  rw [← (Fin.consEquiv (fun _ : Fin (O+1) => GenotypeTransition.Genotype)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem silentCountR_cons {O : ℕ} (g : GenotypeTransition.Genotype)
    (w : Fin O → GenotypeTransition.Genotype) :
    silentCountR (Fin.cons g w : Fin (O+1) → GenotypeTransition.Genotype) =
      (if g.1 then 0 else if g.2 then 1 else 0) + silentCountR w := by
  unfold silentCountR; rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]

theorem voterCountR_cons {O : ℕ} (g : GenotypeTransition.Genotype)
    (w : Fin O → GenotypeTransition.Genotype) :
    voterCountR (Fin.cons g w : Fin (O+1) → GenotypeTransition.Genotype) =
      (if g.1 then 0 else 1) + voterCountR w := by
  unfold voterCountR; rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]

/-- Doc A C4 exact finite-population expected level, general form: for `O` conditionally iid
offspring with law `θ`, voter mass `θ_V = θ_00+θ_01` and `θ_01 = θ_V ζ`, and ANY real survivor
counts `n_V, n_01`, the expected realized ratio `E[(n_01+K)/(n_V+J)]` is the binomial mixture
`Σ_j C(O,j) θ_V^j (1-θ_V)^{O-j} (n_01+jζ)/(n_V+j)`, with Lean's `x/0 = 0` convention on both sides. -/
theorem iid_ratio_binomial (θ : Law GenotypeTransition.Genotype) (ζ : ℝ)
    (hζ : θ.mass (false,true) = (θ.mass (false,false) + θ.mass (false,true)) * ζ) (O : ℕ) :
    ∀ nV n01 : ℝ, (Epistemic.iidAlphabetLaw θ O).expect
        (fun w => (n01 + silentCountR w) / (nV + voterCountR w)) =
      binomialMix (θ.mass (false,false) + θ.mass (false,true)) O
        (fun j => (n01 + j * ζ) / (nV + j)) := by
  induction O with
  | zero =>
    intro nV n01
    have hc : (fun w : Fin 0 → GenotypeTransition.Genotype =>
        (n01 + silentCountR w) / (nV + voterCountR w)) = fun _ => n01 / nV := by
      funext w; simp [silentCountR, voterCountR]
    rw [hc, Law.expect_const]
    simp [binomialMix]
  | succ O ih =>
    intro nV n01
    rw [iid_expect_succ]
    simp_rw [silentCountR_cons, voterCountR_cons]
    have hih : ∀ g : GenotypeTransition.Genotype,
        (Epistemic.iidAlphabetLaw θ O).expect (fun w =>
          (n01 + ((if g.1 then 0 else if g.2 then 1 else 0) + silentCountR w)) /
            (nV + ((if g.1 then 0 else 1) + voterCountR w))) =
        binomialMix (θ.mass (false,false) + θ.mass (false,true)) O
          (fun j => ((n01 + (if g.1 then 0 else if g.2 then 1 else 0)) + j * ζ) /
            ((nV + (if g.1 then 0 else 1)) + j)) := by
      intro g
      rw [← ih (nV + (if g.1 then 0 else 1)) (n01 + (if g.1 then 0 else if g.2 then 1 else 0))]
      congr 1; funext w; ring_nf
    simp_rw [hih]
    rw [binomialMix_succ]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, add_zero]
    have hs := four_masses_sum θ
    set x := θ.mass (false,false) + θ.mass (false,true) with hx
    have hy : 1 - x = θ.mass (true,false) + θ.mass (true,true) := by rw [hx]; linarith
    rw [hy]
    unfold binomialMix
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hD : nV + 1 + (j : ℝ) = nV + ((j + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hD]
    simp only [div_eq_mul_inv]
    push_cast
    linear_combination ((O.choose j : ℝ) * x^j * (1-x)^(O-j) * (nV + ((j:ℝ) + 1))⁻¹) * hζ

/-- Doc A C4 for an actual survivor roster: the exact conditional expected silent ratio after
`M` conditionally iid offspring, `Σ_j C(M,j) θ_V^j (1-θ_V)^{M-j} (n_01+jζ)/(n_V+j)`. -/
theorem nextSilentExpectation_binomial {S : ℕ} (s : Fin S → GenotypeTransition.Genotype)
    (θ : Law GenotypeTransition.Genotype) (M : ℕ) (ζ : ℝ)
    (hζ : θ.mass (false,true) = (θ.mass (false,false) + θ.mass (false,true)) * ζ) :
    nextSilentExpectation s θ M =
      binomialMix (θ.mass (false,false) + θ.mass (false,true)) M
        (fun j => (silentCountR s + j * ζ) / (voterCountR s + j)) := by
  unfold nextSilentExpectation populationSilentRatio
  simp_rw [nextRoster_silentCountR, nextRoster_voterCountR]
  exact iid_ratio_binomial θ ζ hζ M _ _

/-- With positive child voter mass, `ζ = θ_01/θ_V` is the child's voter-conditional allele
frequency. -/
theorem nextSilentExpectation_binomial_pos {S : ℕ} (s : Fin S → GenotypeTransition.Genotype)
    (θ : Law GenotypeTransition.Genotype) (M : ℕ) (hV : 0 < voterMass θ) :
    nextSilentExpectation s θ M =
      binomialMix (voterMass θ) M
        (fun j => (silentCountR s + j * (θ.mass (false,true) / voterMass θ)) /
          (voterCountR s + j)) := by
  apply nextSilentExpectation_binomial
  unfold voterMass at hV ⊢
  field_simp

/-- With zero child voter mass, the value is `n_01/n_V` (zero when `n_V = 0`). -/
theorem nextSilentExpectation_no_voter_children {S : ℕ} (s : Fin S → GenotypeTransition.Genotype)
    (θ : Law GenotypeTransition.Genotype) (M : ℕ) (hV : voterMass θ = 0) :
    nextSilentExpectation s θ M = silentCountR s / voterCountR s := by
  have h00 := θ.nonneg (false,false)
  have h01 := θ.nonneg (false,true)
  unfold voterMass at hV
  have h01' : θ.mass (false,true) = 0 := by linarith
  rw [nextSilentExpectation_binomial s θ M 0 (by rw [h01']; ring), hV]
  unfold binomialMix
  rw [Finset.sum_range_succ']
  simp


/-! ### Doc B (C4h): lossless full-state kernel and its genotype projection (C4f) -/

section FullState

open scoped Classical

variable {Ω Λ Ξ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Ξ]

theorem law_map_bind (L : Law Ω) (K : Ω → Law Λ) (f : Λ → Ξ) :
    (L.bind K).map f = L.bind (fun ω => (K ω).map f) := by
  classical
  apply Epistemic.law_eq_of_mass_eq
  funext ξ
  simp only [Law.map, Law.prob, Law.bind]
  have h : ∀ η, (if f η = ξ then ∑ ω, L.mass ω * (K ω).mass η else 0) =
      ∑ ω, L.mass ω * (if f η = ξ then (K ω).mass η else 0) := by
    intro η; split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

theorem law_bind_map (L : Law Ω) (f : Ω → Λ) (K : Λ → Law Ξ) :
    (L.map f).bind K = L.bind (fun ω => K (f ω)) := by
  classical
  apply Epistemic.law_eq_of_mass_eq
  funext ξ
  simp only [Law.map, Law.prob, Law.bind]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_eq_single (f ω)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem law_map_map (L : Law Ω) (f : Ω → Λ) (g : Λ → Ξ) :
    (L.map f).map g = L.map (fun ω => g (f ω)) := by
  classical
  apply Epistemic.law_eq_of_mass_eq
  funext ξ
  simp only [Law.map, Law.prob]
  have h : ∀ η, (if g η = ξ then ∑ ω, (if f ω = η then L.mass ω else 0) else 0) =
      ∑ ω, if f ω = η then (if g η = ξ then L.mass ω else 0) else 0 := by
    intro η; by_cases hg : g η = ξ <;> simp [hg]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_ite_eq]
  simp

/-- Doc B (C4h): the full finite-horizon state kernel.  `r σ` is the current-generation
evaluation-outcome law, `sel σ ω` the deterministic ordered survivor roster once all scores and
tie metadata are known, `child` the offspring law, and `Φ` updates every state field. -/
def fullStateKernel {State Outcome : Type*} [Fintype State] [Fintype Outcome] {S M : ℕ}
    (r : Kernel State Outcome) (sel : State → Outcome → (Fin S → GenotypeTransition.Genotype))
    (child : (Fin S → GenotypeTransition.Genotype) → Law GenotypeTransition.Genotype)
    (Φ : State → Outcome → (Fin M → GenotypeTransition.Genotype) → State) : Kernel State State :=
  fun σ => (r σ).bind (fun ω => (Epistemic.iidAlphabetLaw (child (sel σ ω)) M).map (Φ σ ω))

/-- Doc B (C4h) mass formula, every row normalized by construction. -/
theorem fullStateKernel_mass {State Outcome : Type*} [Fintype State] [Fintype Outcome] {S M : ℕ}
    (r : Kernel State Outcome) (sel : State → Outcome → (Fin S → GenotypeTransition.Genotype))
    (child : (Fin S → GenotypeTransition.Genotype) → Law GenotypeTransition.Genotype)
    (Φ : State → Outcome → (Fin M → GenotypeTransition.Genotype) → State) (σ σ' : State) :
    (fullStateKernel r sel child Φ σ).mass σ' =
      ∑ ω, (r σ).mass ω * ∑ w : Fin M → GenotypeTransition.Genotype,
        if Φ σ ω w = σ' then ∏ j, (child (sel σ ω)).mass (w j) else 0 := by
  classical
  simp only [fullStateKernel, Law.bind, Law.map, Law.prob, Epistemic.iidAlphabetLaw, Law.pi]

/-- Lossless projection: if every state update's genotype histogram is the histogram of the
next roster (survivors then offspring), the histogram pushforward of the full kernel is exactly
the conditional histogram kernel (C4f) with survivor law `(r σ).map (sel σ)`. -/
theorem fullStateKernel_projection {State Outcome : Type*} [Fintype State] [Fintype Outcome]
    {S M : ℕ} (r : Kernel State Outcome)
    (sel : State → Outcome → (Fin S → GenotypeTransition.Genotype))
    (child : (Fin S → GenotypeTransition.Genotype) → Law GenotypeTransition.Genotype)
    (Φ : State → Outcome → (Fin M → GenotypeTransition.Genotype) → State)
    (n : State → GenotypeTransition.Histogram (S+M))
    (hΦ : ∀ σ ω w, n (Φ σ ω w) = GenotypeTransition.histogram (GenotypeTransition.nextRoster (sel σ ω) w))
    (σ : State) :
    (fullStateKernel r sel child Φ σ).map n =
      GenotypeTransition.histogramKernel (M := M) (fun σ => (r σ).map (sel σ)) child σ := by
  unfold fullStateKernel GenotypeTransition.histogramKernel
  rw [law_map_bind, law_bind_map]
  congr 1
  funext ω
  rw [law_map_map]
  unfold GenotypeTransition.broodHistogramLaw
  congr 1
  funext w
  exact hΦ σ ω w

end FullState

end TransmissionLeftovers


/-! ## 5. Correlated-answer leftovers (Doc B D.2 (D2b), Doc A D2 clone blocks) -/

section CorrelatedLeftovers

open Epistemic CorrelatedAnswers
open scoped Classical

section WrongMode
variable {A : Type*} [Fintype A]

/-- The margin variable `Y = 1[X = w] - 1[X = a*]`. -/
def marginY (a w : A) (x : Option A) : ℝ :=
  (if x = some w then 1 else 0) - (if x = some a then 1 else 0)

theorem marginY_mean (π : Law (Option A)) (a w : A) :
    π.expect (marginY a w) = π.mass (some w) - π.mass (some a) := by
  unfold marginY
  rw [π.expect_sub, π.expect_indicator, π.expect_indicator, prob_label_eq, prob_label_eq]

theorem marginY_variance (π : Law (Option A)) (a w : A) (haw : a ≠ w) :
    π.variance (marginY a w) =
      π.mass (some a) + π.mass (some w) - (π.mass (some w) - π.mass (some a))^2 := by
  rw [π.variance_eq, marginY_mean]
  have hsq : (fun x => marginY a w x ^ 2) =
      (fun x => (if x = some w then (1:ℝ) else 0) + (if x = some a then 1 else 0)) := by
    funext x
    unfold marginY
    have hwa : w ≠ a := fun h => haw h.symm
    by_cases hw : x = some w <;> by_cases ha : x = some a <;> simp [hw, ha, haw, hwa]
  rw [hsq, π.expect_add, π.expect_indicator, π.expect_indicator, prob_label_eq, prob_label_eq]
  ring

omit [Fintype A] in
theorem marginY_count_sum {n : ℕ} (a w : A) (z : OrderedWord n A) :
    (∑ i, marginY a w (z i)) = (labelCount z (some w) : ℝ) - labelCount z (some a) := by
  rw [labelCount_eq_sum, labelCount_eq_sum, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold marginY
  by_cases hw : z i = some w <;> by_cases ha : z i = some a <;> simp [hw, ha]

/-- Doc B (D2b), count form (valid for ANY plurality tie rule): if a wrong readable label `w`
has mass `q` exceeding the correct mass `p`, `δ = q-p > 0`, then on `n ≥ 1` iid answers
`Pr(count(a*) ≥ count(w)) ≤ (p+q-δ²)/(nδ²) ≤ 1/(nδ²)`. -/
theorem wrong_mode_count_bound (π : Law (Option A)) (a w : A) (haw : a ≠ w) {n : ℕ} (hn : 0 < n)
    (hδ : π.mass (some a) < π.mass (some w)) :
    (iidWordLaw π n).prob (fun z => labelCount z (some w) ≤ labelCount z (some a)) ≤
        (π.mass (some a) + π.mass (some w) - (π.mass (some w) - π.mass (some a))^2) /
          ((n : ℝ) * (π.mass (some w) - π.mass (some a))^2) ∧
      (π.mass (some a) + π.mass (some w) - (π.mass (some w) - π.mass (some a))^2) /
          ((n : ℝ) * (π.mass (some w) - π.mass (some a))^2) ≤
        1 / ((n : ℝ) * (π.mass (some w) - π.mass (some a))^2) := by
  set p := π.mass (some a)
  set q := π.mass (some w)
  have hd : 0 < q - p := sub_pos.mpr hδ
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨hmean, hvar⟩ := FiniteProbability.Law.iid_average hn π (marginY a w)
  rw [marginY_mean] at hmean
  rw [marginY_variance π a w haw] at hvar
  set P := Law.pi (fun _ : Fin n => π)
  set avg := fun z : Fin n → Option A => (∑ i, marginY a w (z i)) / (n : ℝ)
  have hcheb := P.chebyshev avg hd
  have hevent : (iidWordLaw π n).prob (fun z => labelCount z (some w) ≤ labelCount z (some a)) ≤
      P.prob (fun z => q - p ≤ |avg z - P.expect avg|) := by
    apply Law.prob_mono
    intro z hz
    have hle : avg z ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hnR.le
      rw [marginY_count_sum]
      have : (labelCount z (some w) : ℝ) ≤ labelCount z (some a) := by exact_mod_cast hz
      linarith
    change q - p ≤ |avg z - P.expect avg|
    rw [show P.expect avg = q - p from hmean]
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hpq : p + q ≤ 1 := by
    have h2 : ({some a, some w} : Finset (Option A)).sum π.mass ≤ ∑ x, π.mass x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => π.nonneg x)
    rw [Finset.sum_pair (fun h => haw (Option.some_inj.mp h)), π.total] at h2
    exact h2
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ _ := hevent
      _ ≤ P.variance avg / (q - p)^2 := hcheb
      _ = _ := by
        rw [show P.variance avg = (p + q - (q - p)^2) / n from hvar]
        field_simp
  · apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (q - p)]

/-- Doc B (D2b) for the actual first-appearance plurality: its accuracy obeys the same bound. -/
theorem wrong_mode_accuracy_bound (π : Law (Option A)) (a w : A) (haw : a ≠ w) {n : ℕ} (hn : 0 < n)
    (hδ : π.mass (some a) < π.mass (some w)) :
    voteAccuracy π n a ≤
      (π.mass (some a) + π.mass (some w) - (π.mass (some w) - π.mass (some a))^2) /
        ((n : ℝ) * (π.mass (some w) - π.mass (some a))^2) := by
  refine le_trans ?_ (wrong_mode_count_bound π a w haw hn hδ).1
  exact Law.prob_mono _ (fun z hz => plurality_dominates_readable z a hz w)

end WrongMode

section CloneBlocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Clone-block sizes `k_l = #{i : c(i) = l}`. -/
def blockSize {n : ℕ} (c : Fin n → ι) (l : ι) : ℝ := ((Finset.univ.filter (fun i => c i = l)).card : ℝ)

theorem blockSize_sum {n : ℕ} (c : Fin n → ι) : ∑ l, blockSize c l = n := by
  calc
    ∑ l, blockSize c l = ∑ l, ∑ i ∈ Finset.univ.filter (fun i => c i = l), (1:ℝ) := by
      simp [blockSize]
    _ = ∑ _i : Fin n, (1:ℝ) := Finset.sum_fiberwise' Finset.univ c (fun _ => (1:ℝ))
    _ = n := by simp

theorem clone_sum_blocks {n : ℕ} (c : Fin n → ι) (z : ι → Bool) :
    (∑ i, bitValue (z (c i))) = ∑ l, blockSize c l * bitValue (z l) := by
  rw [← Finset.sum_fiberwise' Finset.univ c (fun l => bitValue (z l))]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

/-- Explicit clone-block reduction of the correlation denominator (Doc A D2): for answers
copied from independent Bernoulli(p) lineages by a class map `c`, `0<p<1`,
`n + 2 Σ_{i<j} ρ_ij = Σ_l k_l²`; hence the correlation effective size is `n²/Σ_l k_l²`,
recovering D1. -/
theorem clone_block_reduction {n : ℕ} (hn : 0 < n) (c : Fin n → ι) (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    (n : ℝ) + 2 * correlationSum (cloneLaw (ι := ι) p hp.le hp'.le)
        (fun i z => bitValue (z (c i))) p = ∑ l, blockSize c l ^ 2 ∧
      correlatedEffectiveSize (cloneLaw (ι := ι) p hp.le hp'.le)
        (fun i z => bitValue (z (c i))) p = effectiveCopies (blockSize c) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hX : ∀ i (z : ι → Bool), bitValue (z (c i)) = 0 ∨ bitValue (z (c i)) = 1 := by
    intro i z; unfold bitValue; by_cases h : z (c i) <;> simp [h]
  have hm : ∀ i, (cloneLaw (ι := ι) p hp.le hp'.le).expect (fun z => bitValue (z (c i))) = p := by
    intro i
    unfold cloneLaw
    rw [Law.expect_pi_coord (fun _ => MutationBaseline.bernoulli p hp.le hp'.le) (c i) bitValue]
    exact bernoulli_bit_mean p hp.le hp'.le
  have hv1 := correlated_variance hn (cloneLaw (ι := ι) p hp.le hp'.le)
    (fun i z => bitValue (z (c i))) p hp hp' hX hm
  have hfun : (fun z : ι → Bool => (∑ i, bitValue (z (c i))) / (n : ℝ)) =
      cloneAverage (blockSize c) := by
    funext z
    unfold cloneAverage
    rw [clone_sum_blocks, blockSize_sum]
  rw [hfun, clone_variance, blockSize_sum] at hv1
  have hpq : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have hkey : (n : ℝ) + 2 * correlationSum (cloneLaw (ι := ι) p hp.le hp'.le)
      (fun i z => bitValue (z (c i))) p = ∑ l, blockSize c l ^ 2 := by
    have h2 : p * (1 - p) / (n : ℝ)^2 * (∑ l, blockSize c l ^ 2) =
        p * (1 - p) / (n : ℝ)^2 * ((n : ℝ) + 2 * correlationSum (cloneLaw (ι := ι) p hp.le hp'.le)
          (fun i z => bitValue (z (c i))) p) := by
      rw [← hv1]; ring
    have hne : p * (1 - p) / (n : ℝ)^2 ≠ 0 := by positivity
    exact (mul_left_cancel₀ hne h2).symm
  refine ⟨hkey, ?_⟩
  unfold correlatedEffectiveSize effectiveCopies
  rw [hkey, blockSize_sum]

end CloneBlocks

section DecisionValue
variable {Θ Ω D : Type*} [Fintype Θ] [Fintype Ω] [Fintype D] [Nonempty D]

/-- Doc B D.2 (optional): the finite optimal decision value with `n` conditionally iid
observations, `V_n = Σ_x max_d Σ_θ λ_θ π_θ^{⊗n}(x) U(θ,d)`. -/
def decisionValue (lam : Θ → ℝ) (π : Θ → Law Ω) (U : Θ → D → ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → Ω, Finset.univ.sup' Finset.univ_nonempty
    (fun d => ∑ θ, lam θ * (∏ i, (π θ).mass (x i)) * U θ d)

/-- Doc B D.2 (optional): information cannot decrease, `V_n ≤ V_{n+1}`, for any real prior
weights and payoffs (no strict improvement is claimed). -/
theorem decisionValue_mono (lam : Θ → ℝ) (π : Θ → Law Ω) (U : Θ → D → ℝ) (n : ℕ) :
    decisionValue lam π U n ≤ decisionValue lam π U (n+1) := by
  unfold decisionValue
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Ω)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sup'_le
  intro d _
  have hsplit : (∑ θ, lam θ * (∏ i, (π θ).mass (x i)) * U θ d) =
      ∑ a, ∑ θ, lam θ * (∏ i : Fin (n+1), (π θ).mass
        ((Fin.consEquiv (fun _ : Fin (n+1) => Ω)) (a, x) i)) * U θ d := by
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro θ _
    have h1 : (∑ a, lam θ * ((π θ).mass a * ∏ i, (π θ).mass (x i)) * U θ d) =
        lam θ * (∏ i, (π θ).mass (x i)) * U θ d * ∑ a, (π θ).mass a := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [h1, (π θ).total, mul_one]
  rw [hsplit]
  apply Finset.sum_le_sum
  intro a _
  exact Finset.le_sup' (fun d => ∑ θ, lam θ * (∏ i : Fin (n+1), (π θ).mass
    ((Fin.consEquiv (fun _ : Fin (n+1) => Ω)) (a, x) i)) * U θ d) (Finset.mem_univ d)

theorem decisionValue_monotone (lam : Θ → ℝ) (π : Θ → Law Ω) (U : Θ → D → ℝ) :
    Monotone (decisionValue lam π U) :=
  monotone_nat_of_le_succ (decisionValue_mono lam π U)

end DecisionValue

end CorrelatedLeftovers


/-! ## 6. Replay matrix-power formula (Doc A B7.1) -/

section Replay

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Finite transition matrix of a normalized kernel. -/
def transitionMatrix (K : Kernel Ω Ω) : Matrix Ω Ω ℝ := fun z z' => (K z).mass z'

/-- Generation-dependent composition `K_0 K_1 ⋯ K_{T-1}` of normalized kernels. -/
def kernelProd (Ks : ℕ → Kernel Ω Ω) : ℕ → Kernel Ω Ω
  | 0 => fun z => NoisySelection.pointLaw z
  | T+1 => Kernel.comp (kernelProd Ks T) (Ks T)

/-- The matrix product `M_0 M_1 ⋯ M_{T-1}`. -/
def matrixProd (Ks : ℕ → Kernel Ω Ω) : ℕ → Matrix Ω Ω ℝ
  | 0 => 1
  | T+1 => matrixProd Ks T * transitionMatrix (Ks T)

/-- The law of the replayed state `Z_T`, generation by generation. -/
def replayLaw (μ0 : Law Ω) (Ks : ℕ → Kernel Ω Ω) : ℕ → Law Ω
  | 0 => μ0
  | T+1 => (replayLaw μ0 Ks T).bind (Ks T)

theorem kernelProd_mass (Ks : ℕ → Kernel Ω Ω) (T : ℕ) (z z' : Ω) :
    (kernelProd Ks T z).mass z' = matrixProd Ks T z z' := by
  induction T generalizing z' with
  | zero =>
    simp only [kernelProd, matrixProd, NoisySelection.pointLaw, Matrix.one_apply]
    by_cases h : z = z' <;> simp [h, eq_comm]
  | succ T ih =>
    simp only [kernelProd, matrixProd, Kernel.comp_mass, Matrix.mul_apply, ih]
    rfl

/-- Every power/product row is a normalized law: nonnegative entries, row sums one. -/
theorem matrixProd_stochastic (Ks : ℕ → Kernel Ω Ω) (T : ℕ) (z : Ω) :
    (∀ z', 0 ≤ matrixProd Ks T z z') ∧ ∑ z', matrixProd Ks T z z' = 1 := by
  simp only [← kernelProd_mass]
  exact ⟨(kernelProd Ks T z).nonneg, (kernelProd Ks T z).total⟩

theorem replayLaw_mass (μ0 : Law Ω) (Ks : ℕ → Kernel Ω Ω) (T : ℕ) (z' : Ω) :
    (replayLaw μ0 Ks T).mass z' = ∑ z, μ0.mass z * (kernelProd Ks T z).mass z' := by
  induction T generalizing z' with
  | zero =>
    simp only [replayLaw, kernelProd, NoisySelection.pointLaw, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]; simp
  | succ T ih =>
    simp only [replayLaw, kernelProd, Law.bind, Kernel.comp_mass, ih, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro z _
    apply Finset.sum_congr rfl; intro u _
    ring

/-- Doc A (B7.1), generation-dependent form:
`E φ(Z_T) = Σ_{z,z'} μ_0(z) (M_0⋯M_{T-1})(z,z') φ(z')`. -/
theorem replay_expectation (μ0 : Law Ω) (Ks : ℕ → Kernel Ω Ω) (T : ℕ) (φ : Ω → ℝ) :
    (replayLaw μ0 Ks T).expect φ = ∑ z, ∑ z', μ0.mass z * matrixProd Ks T z z' * φ z' := by
  unfold Law.expect Law1.mean
  simp_rw [replayLaw_mass, kernelProd_mass, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem matrixProd_const (K : Kernel Ω Ω) (T : ℕ) :
    matrixProd (fun _ => K) T = transitionMatrix K ^ T := by
  induction T with
  | zero => rfl
  | succ T ih => rw [matrixProd, ih, pow_succ]

/-- Doc A (B7.1), time-homogeneous form: `E φ(Z_T) = Σ_{z,z'} μ_0(z) K^T(z,z') φ(z')`. -/
theorem replay_expectation_pow (μ0 : Law Ω) (K : Kernel Ω Ω) (T : ℕ) (φ : Ω → ℝ) :
    (replayLaw μ0 (fun _ => K) T).expect φ =
      ∑ z, ∑ z', μ0.mass z * (transitionMatrix K ^ T) z z' * φ z' := by
  rw [replay_expectation, matrixProd_const]

end Replay


/-! ## 7. Referee G3: the C.5 recursion is not a multigeneration random-voter-slot law

Exact finite model (referee G3): `P = 4`, `S = 2`; boards outrank voters, uniform ties within
role (the survivor set is uniform over role-top sets); no crossover (each offspring copies one
uniformly drawn survivor, `survivorLaw`); no board-locus mutation; offspring-only advocate
mutation `μ = 1/10` (existing `mutate`); two conditionally iid offspring (`iidAlphabetLaw`);
next roster = survivors then offspring (`nextRoster`); start `00,01,00,10`.  The random voter
slot is a uniformly drawn slot of the random population, conditioned on being a voter. -/

section G3Refuter

open GenotypeTransition NoisySelection Epistemic
open scoped Classical

abbrev Gt := GenotypeTransition.Genotype

/-- Boards outrank voters: a voter survives only if every excluded individual is a voter. -/
def RoleTopSet {P : ℕ} (z : Fin P → Gt) (A : Finset (Fin P)) : Prop :=
  ∀ i ∈ A, ∀ j ∉ A, (z i).1 = false → (z j).1 = false

def roleTopSets {P S : ℕ} (z : Fin P → Gt) : Finset (Survivors P S) :=
  Finset.univ.filter (fun A => RoleTopSet z A.val)

theorem roleTopSets_nonempty {P S : ℕ} (hSP : S ≤ P) (z : Fin P → Gt) :
    (roleTopSets (S := S) z).Nonempty := by
  let score : Fin P → ℝ := fun i => if (z i).1 then 1 else 0
  refine ⟨lexSurvivors hSP score (fun _ => 0), ?_⟩
  simp only [roleTopSets, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i hi j hj hiv
  have h := lexSurvivors_topSet hSP score (fun _ => 0) i hi j hj
  simp only [score, hiv, Bool.false_eq_true, ↓reduceIte] at h
  cases hzj : (z j).1
  · rfl
  · simp [hzj] at h; linarith

/-- Uniform ties within role: the survivor set is uniform over the role-top sets. -/
def roleSelectionLaw {P S : ℕ} (hSP : S ≤ P) (z : Fin P → Gt) : Law (Survivors P S) where
  mass A := if A ∈ roleTopSets (S := S) z then 1 / ((roleTopSets (S := S) z).card : ℝ) else 0
  nonneg A := by split_ifs <;> positivity
  total := by
    have hc : (0:ℝ) < (roleTopSets (S := S) z).card := by
      exact_mod_cast (roleTopSets_nonempty hSP z).card_pos
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    field_simp

theorem roleSelection_expect {P S : ℕ} (hSP : S ≤ P) (z : Fin P → Gt) (F : Survivors P S → ℝ) :
    (roleSelectionLaw hSP z).expect F =
      (∑ A ∈ roleTopSets (S := S) z, F A) / ((roleTopSets (S := S) z).card : ℝ) := by
  unfold Law.expect Law1.mean
  simp only [roleSelectionLaw, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  ring

/-- Order-free sums over an actual selected roster. -/
theorem sum_selectedRoster {P S : ℕ} {M : Type*} [AddCommMonoid M] (z : Fin P → Gt)
    (A : Survivors P S) (F : Gt → M) :
    ∑ k, F (selectedRoster z A k) = ∑ i ∈ A.val, F (z i) := by
  unfold selectedRoster
  rw [← Finset.sum_coe_sort A.val]
  exact Fintype.sum_equiv (A.val.orderIsoOfFin A.property).toEquiv _ _ (fun k => rfl)

def boardSet {P : ℕ} (z : Fin P → Gt) : Finset (Fin P) := Finset.univ.filter (fun i => (z i).1 = true)

/-- With at least `S` boards, every role-top survivor set consists of boards. -/
theorem roleTop_all_boards {P S : ℕ} (z : Fin P → Gt) (hB : S ≤ (boardSet z).card)
    (A : Survivors P S) (hA : A ∈ roleTopSets (S := S) z) : ∀ i ∈ A.val, (z i).1 = true := by
  intro i hi
  by_contra hv
  have hv' : (z i).1 = false := by simpa using hv
  have hA' : RoleTopSet z A.val := (Finset.mem_filter.mp hA).2
  have hsub : insert i (boardSet z) ⊆ A.val := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · by_contra hjA
      have := hA' i hi j hjA hv'
      have hjb : (z j).1 = true := (Finset.mem_filter.mp hj).2
      rw [this] at hjb; exact Bool.false_ne_true hjb
  have hiB : i ∉ boardSet z := by simp [boardSet, hv']
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hiB, A.property] at hc
  omega

/-- The survivor set containing `b` and `j`, as a total function (a fixed default when `b = j`). -/
def pairSet (b j : Fin 4) : Survivors 4 2 :=
  if h : b = j then ⟨{0, 1}, by decide⟩ else ⟨{b, j}, Finset.card_pair h⟩

/-- With exactly one board `b`, the role-top sets are the three pairs `{b, j}`. -/
theorem roleTop_one_board_sum (z : Fin 4 → Gt) (b : Fin 4) (hb : (z b).1 = true)
    (hv : ∀ j, j ≠ b → (z j).1 = false) (G : Survivors 4 2 → ℝ) :
    ∑ A ∈ roleTopSets (S := 2) z, G A = ∑ j ∈ Finset.univ.erase b, G (pairSet b j) := by
  have hmem : ∀ A : Survivors 4 2, A ∈ roleTopSets (S := 2) z ↔ b ∈ A.val := by
    intro A
    simp only [roleTopSets, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hA
      by_contra hbA
      obtain ⟨i, hi⟩ : A.val.Nonempty := Finset.card_pos.mp (by rw [A.property]; norm_num)
      have hib : i ≠ b := fun h => hbA (h ▸ hi)
      have := hA i hi b hbA (hv i hib)
      rw [hb] at this; exact absurd this (by decide)
    · intro hbA i _ j hj _
      exact hv j (fun h => hj (h ▸ hbA))
  symm
  apply Finset.sum_bij (fun j _ => pairSet b j)
  · intro j hj
    have hjb : b ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    rw [hmem]; simp [pairSet, hjb]
  · intro j1 hj1 j2 hj2 h
    have h1 : b ≠ j1 := fun h' => (Finset.mem_erase.mp hj1).1 h'.symm
    have h2 : b ≠ j2 := fun h' => (Finset.mem_erase.mp hj2).1 h'.symm
    simp only [pairSet, h1, h2, ↓reduceDIte, Subtype.mk.injEq] at h
    have : j1 ∈ ({b, j2} : Finset (Fin 4)) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j1)
    rcases Finset.mem_insert.mp this with h3 | h3
    · exact absurd h3.symm h1
    · exact Finset.mem_singleton.mp h3
  · intro A hA
    have hbA := (hmem A).mp hA
    obtain ⟨x, y, hxy, hA2⟩ := Finset.card_eq_two.mp A.property
    rw [hA2] at hbA
    rcases Finset.mem_insert.mp hbA with hbx | hby
    · refine ⟨y, Finset.mem_erase.mpr ⟨fun h => hxy (hbx ▸ h.symm ▸ rfl), Finset.mem_univ y⟩, ?_⟩
      have hb' : b ≠ y := by rw [hbx]; exact hxy
      apply Subtype.ext
      simp only [pairSet, hb', ↓reduceDIte]
      rw [hA2, hbx]
    · have hby' := Finset.mem_singleton.mp hby
      refine ⟨x, Finset.mem_erase.mpr ⟨fun h => hxy (h.trans hby'), Finset.mem_univ x⟩, ?_⟩
      have hb' : b ≠ x := by rw [hby']; exact fun h => hxy h.symm
      apply Subtype.ext
      simp only [pairSet, hb', ↓reduceDIte]
      rw [hA2, hby', Finset.pair_comm]
  · intro j _; rfl

theorem roleTop_one_board_card (z : Fin 4 → Gt) (b : Fin 4) (hb : (z b).1 = true)
    (hv : ∀ j, j ≠ b → (z j).1 = false) :
    ((roleTopSets (S := 2) z).card : ℝ) = 3 := by
  have h := roleTop_one_board_sum z b hb hv (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ b)]
  simp

theorem one_board_of_card (z : Fin 4 → Gt) (h1 : (boardSet z).card = 1) :
    ∃ b, (z b).1 = true ∧ ∀ j, j ≠ b → (z j).1 = false := by
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h1
  refine ⟨b, ?_, fun j hj => ?_⟩
  · have : b ∈ boardSet z := by rw [hb]; exact Finset.mem_singleton_self b
    exact (Finset.mem_filter.mp this).2
  · have : j ∉ boardSet z := by rw [hb]; simpa using hj
    simpa [boardSet] using this

/-- Expectation over the uniform role-top law, one board: average over the three pairs. -/
theorem roleSelection_one_board (z : Fin 4 → Gt) (h1 : (boardSet z).card = 1)
    (ψ : Gt → ℝ) (hψ : ∀ g : Gt, g.1 = true → ψ g = 0) :
    (roleSelectionLaw (S := 2) (by norm_num) z).expect (fun A => ∑ i ∈ A.val, ψ (z i)) =
      (∑ i, ψ (z i)) / 3 := by
  obtain ⟨b, hb, hv⟩ := one_board_of_card z h1
  rw [roleSelection_expect, roleTop_one_board_card z b hb hv, roleTop_one_board_sum z b hb hv]
  congr 1
  have hpair : ∀ j ∈ Finset.univ.erase b, (∑ i ∈ (pairSet b j).val, ψ (z i)) = ψ (z j) := by
    intro j hj
    have hjb : b ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    simp only [pairSet, hjb, ↓reduceDIte]
    rw [Finset.sum_pair hjb, hψ _ hb, zero_add]
  rw [Finset.sum_congr rfl hpair, Finset.sum_erase (f := fun i => ψ (z i)) Finset.univ (hψ _ hb)]

theorem roleSelection_many_boards {P S : ℕ} (hSP : S ≤ P) (z : Fin P → Gt)
    (hB : S ≤ (boardSet z).card) (ψ : Gt → ℝ) (hψ : ∀ g : Gt, g.1 = true → ψ g = 0) :
    (roleSelectionLaw hSP z).expect (fun A => ∑ i ∈ A.val, ψ (z i)) = 0 := by
  rw [roleSelection_expect]
  rw [Finset.sum_eq_zero (fun A hA => Finset.sum_eq_zero
    (fun i hi => hψ _ (roleTop_all_boards z hB A hA i hi)))]
  simp

/-- One offspring: a uniformly drawn survivor's genotype (no crossover), then the existing
mutation kernel with board rate `0` and advocate rate `1/10`. -/
def g3Child {S : ℕ} (s : Fin S → Gt) (hS : 0 < S) : Law Gt :=
  mutate (survivorLaw s hS) 0 (1/10) le_rfl zero_le_one (by norm_num) (by norm_num)

/-- One generation of the exact finite G3 lifecycle. -/
def g3Step (z : Fin 4 → Gt) : Law (Fin 4 → Gt) :=
  (roleSelectionLaw (S := 2) (by norm_num) z).bind (fun A =>
    (iidAlphabetLaw (g3Child (selectedRoster z A) (by norm_num)) 2).map
      (fun w => (nextRoster (selectedRoster z A) w : Fin 4 → Gt)))

def g3Start : Fin 4 → Gt := ![(false,false), (false,true), (false,false), (true,false)]

theorem g3Start_0 : g3Start 0 = (false,false) := rfl
theorem g3Start_1 : g3Start 1 = (false,true) := rfl
theorem g3Start_2 : g3Start 2 = (false,false) := rfl
theorem g3Start_3 : g3Start 3 = (true,false) := rfl

/-- The exact law of the population at generation `t`. -/
def g3Law : ℕ → Law (Fin 4 → Gt)
  | 0 => pointLaw g3Start
  | t+1 => (g3Law t).bind g3Step

/-- Per-individual weights: survivors' carriers plus their expected carrier offspring. -/
def psiSilent (g : Gt) : ℝ :=
  if g = (false,true) then 19/10 else if g = (false,false) then 1/10 else 0

def psiVoter (g : Gt) : ℝ := if g.1 then 0 else 2

theorem psiSilent_board (g : Gt) (hg : g.1 = true) : psiSilent g = 0 := by
  rcases g with ⟨b, a⟩; simp at hg; subst hg; simp [psiSilent]

theorem psiVoter_board (g : Gt) (hg : g.1 = true) : psiVoter g = 0 := by
  simp [psiVoter, hg]

theorem g3Child_silent {S : ℕ} (s : Fin S → Gt) (hS : 0 < S) :
    (g3Child s hS).mass (false,true) =
      (1/10) * voterMass (survivorLaw s hS) + (8/10) * (survivorLaw s hS).mass (false,true) := by
  unfold g3Child
  rw [mutate_silent_coordinate]
  ring

theorem g3Child_voter {S : ℕ} (s : Fin S → Gt) (hS : 0 < S) :
    voterMass (g3Child s hS) = voterMass (survivorLaw s hS) := by
  unfold g3Child
  rw [mutate_voterMass]
  ring

theorem g3Step_silent (z : Fin 4 → Gt) :
    (g3Step z).expect silentCountR =
      (roleSelectionLaw (S := 2) (by norm_num) z).expect (fun A => ∑ i ∈ A.val, psiSilent (z i)) := by
  unfold g3Step
  rw [Law.expect_bind]
  congr 1
  funext A
  rw [Law.expect_map]
  have h1 : (fun w : Fin 2 → Gt => silentCountR (nextRoster (selectedRoster z A) w : Fin 4 → Gt)) =
      (fun w => silentCountR (selectedRoster z A) + silentCountR w) :=
    funext (fun w => nextRoster_silentCountR (selectedRoster z A) w)
  rw [h1, Law.expect_add, Law.expect_const, iid_silentCountR_mean, g3Child_silent,
    ← sum_selectedRoster z A psiSilent]
  unfold voterMass
  rw [survivorLaw_mass_indicator, survivorLaw_mass_indicator]
  unfold silentCountR
  simp only [Fin.sum_univ_two]
  generalize selectedRoster z A 0 = g0
  generalize selectedRoster z A 1 = g1
  rcases g0 with ⟨_|_, _|_⟩ <;> rcases g1 with ⟨_|_, _|_⟩ <;> norm_num [psiSilent]

theorem g3Step_voter (z : Fin 4 → Gt) :
    (g3Step z).expect voterCountR =
      (roleSelectionLaw (S := 2) (by norm_num) z).expect (fun A => ∑ i ∈ A.val, psiVoter (z i)) := by
  unfold g3Step
  rw [Law.expect_bind]
  congr 1
  funext A
  rw [Law.expect_map]
  have h1 : (fun w : Fin 2 → Gt => voterCountR (nextRoster (selectedRoster z A) w : Fin 4 → Gt)) =
      (fun w => voterCountR (selectedRoster z A) + voterCountR w) :=
    funext (fun w => nextRoster_voterCountR (selectedRoster z A) w)
  rw [h1, Law.expect_add, Law.expect_const, iid_voterCountR_mean, g3Child_voter,
    ← sum_selectedRoster z A psiVoter]
  unfold voterMass
  rw [survivorLaw_mass_indicator, survivorLaw_mass_indicator]
  unfold voterCountR
  simp only [Fin.sum_univ_two]
  generalize selectedRoster z A 0 = g0
  generalize selectedRoster z A 1 = g1
  rcases g0 with ⟨_|_, _|_⟩ <;> rcases g1 with ⟨_|_, _|_⟩ <;> norm_num [psiVoter]

theorem pointLaw_bind_expect {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (z : Ω) (K : Kernel Ω Λ)
    (F : Λ → ℝ) : ((pointLaw z).bind K).expect F = (K z).expect F := by
  rw [Law.expect_bind]
  unfold Law.expect Law1.mean pointLaw
  simp

theorem g3Start_boards : (boardSet g3Start).card = 1 := by decide

theorem g3_t1_silent : (g3Law 1).expect silentCountR = 7/10 := by
  change ((pointLaw g3Start).bind g3Step).expect silentCountR = _
  rw [pointLaw_bind_expect, g3Step_silent,
    roleSelection_one_board g3Start g3Start_boards psiSilent psiSilent_board, Fin.sum_univ_four]
  norm_num [g3Start_0, g3Start_1, g3Start_2, g3Start_3, psiSilent]

theorem g3_t1_voter : (g3Law 1).expect voterCountR = 2 := by
  change ((pointLaw g3Start).bind g3Step).expect voterCountR = _
  rw [pointLaw_bind_expect, g3Step_voter,
    roleSelection_one_board g3Start g3Start_boards psiVoter psiVoter_board, Fin.sum_univ_four]
  norm_num [g3Start_0, g3Start_1, g3Start_2, g3Start_3, psiVoter]


theorem boardSet_card_eq {P : ℕ} (z : Fin P → Gt) :
    (boardSet z).card = ∑ i, if (z i).1 = true then 1 else 0 := by
  unfold boardSet; rw [Finset.card_filter]

theorem boardSet_nextRoster {S M : ℕ} (s : Fin S → Gt) (w : Fin M → Gt) :
    (boardSet (nextRoster s w)).card = (boardSet s).card + (boardSet w).card := by
  rw [boardSet_card_eq, boardSet_card_eq, boardSet_card_eq, Fin.sum_univ_add]
  simp [nextRoster]

/-- The voter indicator. -/
def voterInd (g : Gt) : ℝ := if g.1 then 0 else 1

/-- After one survivor set with exactly one board, the next generation's role-top expectation
is zero unless both offspring are voters. -/
theorem next_generation_pointwise (s w : Fin 2 → Gt) (hs : (boardSet s).card = 1)
    (ψ : Gt → ℝ) (hψ : ∀ g : Gt, g.1 = true → ψ g = 0) :
    (roleSelectionLaw (S := 2) (by norm_num) (nextRoster s w : Fin 4 → Gt)).expect
        (fun A => ∑ i ∈ A.val, ψ ((nextRoster s w : Fin 4 → Gt) i)) =
      voterInd (w 0) * voterInd (w 1) * ((∑ k, ψ (s k)) + ψ (w 0) + ψ (w 1)) / 3 := by
  have hc := boardSet_nextRoster s w
  have hw : (boardSet w).card = (if (w 0).1 = true then 1 else 0) + (if (w 1).1 = true then 1 else 0) := by
    rw [boardSet_card_eq, Fin.sum_univ_two]
  rw [hs, hw] at hc
  cases h0 : (w 0).1 <;> cases h1 : (w 1).1
  · rw [h0, h1] at hc
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hc
    rw [roleSelection_one_board _ hc ψ hψ]
    rw [show (∑ i : Fin 4, ψ ((nextRoster s w : Fin 4 → Gt) i)) =
      ∑ i : Fin (2+2), ψ (nextRoster s w i) from rfl, Fin.sum_univ_add]
    simp only [nextRoster, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two, voterInd, h0,
      h1, Bool.false_eq_true, ↓reduceIte, one_mul]
    ring
  all_goals
    rw [roleSelection_many_boards _ _ (by rw [h0, h1] at hc; simp at hc; omega) ψ hψ]
    simp [voterInd, h0, h1]

/-- Expectation of the pointwise formula under two conditionally iid offspring. -/
theorem brood_expect (θ : Law Gt) (c : ℝ) (ψ : Gt → ℝ) :
    (iidAlphabetLaw θ 2).expect
        (fun w => voterInd (w 0) * voterInd (w 1) * (c + ψ (w 0) + ψ (w 1)) / 3) =
      (c * (θ.expect voterInd)^2 +
        2 * θ.expect voterInd * θ.expect (fun g => voterInd g * ψ g)) / 3 := by
  unfold iidAlphabetLaw
  have hp : (fun w : Fin 2 → Gt => voterInd (w 0) * voterInd (w 1) * (c + ψ (w 0) + ψ (w 1)) / 3) =
      (fun w => (c/3) * (voterInd (w 0) * voterInd (w 1)) +
        (1/3) * ((voterInd (w 0) * ψ (w 0)) * voterInd (w 1)) +
        (1/3) * (voterInd (w 0) * (voterInd (w 1) * ψ (w 1)))) := by
    funext w; ring
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have e1 := Law.expect_pi_coord_mul (fun _ : Fin 2 => θ) h01 voterInd voterInd
  have e2 := Law.expect_pi_coord_mul (fun _ : Fin 2 => θ) h01 (fun g => voterInd g * ψ g) voterInd
  have e3 := Law.expect_pi_coord_mul (fun _ : Fin 2 => θ) h01 voterInd (fun g => voterInd g * ψ g)
  rw [hp, Law.expect_add, Law.expect_add, Law.expect_const_mul, Law.expect_const_mul,
    Law.expect_const_mul, e1, e2, e3]
  ring

theorem expect_voterInd (θ : Law Gt) : θ.expect voterInd = θ.mass (false,false) + θ.mass (false,true) := by
  simp [Law.expect, Law1.mean, Fintype.sum_prod_type, voterInd]
  ring

theorem expect_voterInd_silent (θ : Law Gt) :
    θ.expect (fun g => voterInd g * psiSilent g) =
      θ.mass (false,false) * (1/10) + θ.mass (false,true) * (19/10) := by
  simp [Law.expect, Law1.mean, Fintype.sum_prod_type, voterInd, psiSilent]
  ring

theorem expect_voterInd_voter (θ : Law Gt) :
    θ.expect (fun g => voterInd g * psiVoter g) = 2 * (θ.mass (false,false) + θ.mass (false,true)) := by
  simp [Law.expect, Law1.mean, Fintype.sum_prod_type, voterInd, psiVoter]
  ring

/-- The survivor law after selecting the board `3` and the voter `j` from the start. -/
theorem pair_survivor_mass (j : Fin 4) (hj : (3 : Fin 4) ≠ j) (g : Gt) :
    (survivorLaw (selectedRoster g3Start (pairSet 3 j)) (by norm_num)).mass g =
      ((if g3Start 3 = g then 1 else 0) + (if g3Start j = g then 1 else 0)) / 2 := by
  rw [survivorLaw_mass_indicator, sum_selectedRoster g3Start (pairSet 3 j)
    (fun h => if h = g then (1:ℝ) else 0)]
  simp only [pairSet, hj, ↓reduceDIte]
  rw [Finset.sum_pair hj]
  norm_num

theorem pair_board_card (j : Fin 4) (hj : (3 : Fin 4) ≠ j) (hjv : (g3Start j).1 = false) :
    (boardSet (selectedRoster g3Start (pairSet 3 j))).card = 1 := by
  rw [boardSet_card_eq, sum_selectedRoster g3Start (pairSet 3 j)
    (fun h => if h.1 = true then 1 else 0)]
  simp only [pairSet, hj, ↓reduceDIte]
  rw [Finset.sum_pair hj, hjv, g3Start_3]
  rfl

theorem pair_psi_sum (j : Fin 4) (hj : (3 : Fin 4) ≠ j) (ψ : Gt → ℝ) :
    ∑ k, ψ (selectedRoster g3Start (pairSet 3 j) k) = ψ (g3Start 3) + ψ (g3Start j) := by
  rw [sum_selectedRoster g3Start (pairSet 3 j) ψ]
  simp only [pairSet, hj, ↓reduceDIte]
  rw [Finset.sum_pair hj]

/-- Second-generation conditional expectation after selecting the pair `{3, j}` first. -/
theorem second_generation_pair (j : Fin 4) (hj : (3 : Fin 4) ≠ j) (hjv : (g3Start j).1 = false)
    (ψ : Gt → ℝ) (hψ : ∀ g : Gt, g.1 = true → ψ g = 0) :
    (iidAlphabetLaw (g3Child (selectedRoster g3Start (pairSet 3 j)) (by norm_num)) 2).expect
        (fun w => (roleSelectionLaw (S := 2) (by norm_num)
          (nextRoster (selectedRoster g3Start (pairSet 3 j)) w : Fin 4 → Gt)).expect
          (fun A => ∑ i ∈ A.val, ψ ((nextRoster (selectedRoster g3Start (pairSet 3 j)) w : Fin 4 → Gt) i))) =
      let θ := g3Child (selectedRoster g3Start (pairSet 3 j)) (by norm_num)
      ((ψ (g3Start 3) + ψ (g3Start j)) * (θ.expect voterInd)^2 +
        2 * θ.expect voterInd * θ.expect (fun g => voterInd g * ψ g)) / 3 := by
  have hpt : (fun w : Fin 2 → Gt => (roleSelectionLaw (S := 2) (by norm_num)
      (nextRoster (selectedRoster g3Start (pairSet 3 j)) w : Fin 4 → Gt)).expect
      (fun A => ∑ i ∈ A.val, ψ ((nextRoster (selectedRoster g3Start (pairSet 3 j)) w : Fin 4 → Gt) i))) =
      (fun w => voterInd (w 0) * voterInd (w 1) *
        ((ψ (g3Start 3) + ψ (g3Start j)) + ψ (w 0) + ψ (w 1)) / 3) := by
    funext w
    rw [next_generation_pointwise _ w (pair_board_card j hj hjv) ψ hψ, pair_psi_sum j hj]
  rw [hpt, brood_expect]


theorem theta_expect_voterInd {S : ℕ} (s : Fin S → Gt) (hS : 0 < S) :
    (g3Child s hS).expect voterInd = voterMass (survivorLaw s hS) := by
  rw [expect_voterInd]; exact g3Child_voter s hS

theorem theta_expect_silent {S : ℕ} (s : Fin S → Gt) (hS : 0 < S) :
    (g3Child s hS).expect (fun g => voterInd g * psiSilent g) =
      voterMass (survivorLaw s hS) / 10 + (18/10) * ((1/10) * voterMass (survivorLaw s hS) +
        (8/10) * (survivorLaw s hS).mass (false,true)) := by
  rw [expect_voterInd_silent, ← g3Child_silent, ← g3Child_voter s hS]
  unfold voterMass
  ring

theorem theta_expect_voter {S : ℕ} (s : Fin S → Gt) (hS : 0 < S) :
    (g3Child s hS).expect (fun g => voterInd g * psiVoter g) = 2 * voterMass (survivorLaw s hS) := by
  rw [expect_voterInd_voter, ← g3Child_voter s hS]; rfl

theorem g3Start_voters : ∀ j : Fin 4, j ≠ 3 → (g3Start j).1 = false := by decide

/-- Two-generation reduction: the second generation's expected count is an average over the
three first-generation survivor pairs `{3, j}` of the exact second-generation values. -/
theorem g3_two_step (F : (Fin 4 → Gt) → ℝ) (ψ : Gt → ℝ) (hψ : ∀ g : Gt, g.1 = true → ψ g = 0)
    (hstep : ∀ z, (g3Step z).expect F =
      (roleSelectionLaw (S := 2) (by norm_num) z).expect (fun A => ∑ i ∈ A.val, ψ (z i))) :
    (g3Law 2).expect F = (∑ j ∈ Finset.univ.erase (3 : Fin 4),
      ((ψ (g3Start 3) + ψ (g3Start j)) *
          ((g3Child (selectedRoster g3Start (pairSet 3 j)) (by norm_num)).expect voterInd)^2 +
        2 * (g3Child (selectedRoster g3Start (pairSet 3 j)) (by norm_num)).expect voterInd *
          (g3Child (selectedRoster g3Start (pairSet 3 j)) (by norm_num)).expect
            (fun g => voterInd g * ψ g)) / 3) / 3 := by
  change ((g3Law 1).bind g3Step).expect F = _
  rw [Law.expect_bind]
  simp_rw [hstep]
  change ((pointLaw g3Start).bind g3Step).expect _ = _
  rw [pointLaw_bind_expect]
  unfold g3Step
  rw [Law.expect_bind, roleSelection_expect, roleTop_one_board_card g3Start 3 rfl g3Start_voters,
    roleTop_one_board_sum g3Start 3 rfl g3Start_voters]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj3 : (3 : Fin 4) ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
  rw [Law.expect_map]
  exact second_generation_pair j hj3 (g3Start_voters j (fun h => hj3 h.symm)) ψ hψ

theorem erase_three : (Finset.univ.erase (3 : Fin 4)) = {0, 1, 2} := by
  ext j; fin_cases j <;> simp

theorem pair_voterMass (j : Fin 4) (hj : (3 : Fin 4) ≠ j) :
    voterMass (survivorLaw (selectedRoster g3Start (pairSet 3 j)) (by norm_num)) =
      ((if g3Start 3 = (false,false) then 1 else 0) + (if g3Start j = (false,false) then 1 else 0)) / 2 +
      ((if g3Start 3 = (false,true) then 1 else 0) + (if g3Start j = (false,true) then 1 else 0)) / 2 := by
  unfold voterMass
  rw [pair_survivor_mass j hj, pair_survivor_mass j hj]

/-- Exact second-generation expected silent-carrier count: `37/200`. -/
theorem g3_t2_silent : (g3Law 2).expect silentCountR = 37/200 := by
  rw [g3_two_step silentCountR psiSilent psiSilent_board g3Step_silent, erase_three]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [theta_expect_voterInd, theta_expect_silent]
  rw [pair_voterMass 0 (by decide), pair_voterMass 1 (by decide), pair_voterMass 2 (by decide),
    pair_survivor_mass 0 (by decide), pair_survivor_mass 1 (by decide),
    pair_survivor_mass 2 (by decide)]
  norm_num [g3Start_0, g3Start_1, g3Start_2, g3Start_3, psiSilent]

/-- Exact second-generation expected voter count: `1/2`. -/
theorem g3_t2_voter : (g3Law 2).expect voterCountR = 1/2 := by
  rw [g3_two_step voterCountR psiVoter psiVoter_board g3Step_voter, erase_three]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [theta_expect_voterInd, theta_expect_voter]
  rw [pair_voterMass 0 (by decide), pair_voterMass 1 (by decide), pair_voterMass 2 (by decide)]
  norm_num [g3Start_0, g3Start_1, g3Start_2, g3Start_3, psiVoter]

/-- A uniformly drawn slot of the random population. -/
def slotLaw (L : Law (Fin 4 → Gt)) : Law Gt :=
  (L.prod (uniformIndex 4 (by norm_num))).map (fun p => p.1 p.2)

theorem mass_eq_expect_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (K : Law Ω) (g : Ω) :
    K.mass g = K.expect (fun x => if x = g then 1 else 0) := by
  unfold Law.expect Law1.mean
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem slotLaw_mass (L : Law (Fin 4 → Gt)) (g : Gt) :
    (slotLaw L).mass g = L.expect (fun z => (wordCount z g : ℝ)) / 4 := by
  rw [mass_eq_expect_indicator, slotLaw, Law.expect_map, expect_prod_iterated]
  have h : ∀ z : Fin 4 → Gt, (uniformIndex 4 (by norm_num)).expect
      (fun i => if z i = g then (1:ℝ) else 0) = (wordCount z g : ℝ) * (1/4) := by
    intro z
    rw [wordCount_real_eq_sum]
    simp only [Law.expect, Law1.mean, uniformIndex, Nat.cast_ofNat]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> norm_num
  simp only [h]
  rw [Law.expect_mul_const]
  ring

theorem voterCountR_eq_counts {P : ℕ} (z : Fin P → Gt) :
    voterCountR z = (wordCount z (false,false) : ℝ) + wordCount z (false,true) := by
  rw [wordCount_real_eq_sum, wordCount_real_eq_sum, ← Finset.sum_add_distrib]
  unfold voterCountR
  apply Finset.sum_congr rfl
  intro i _
  rcases z i with ⟨_|_, _|_⟩ <;> simp

/-- The silent frequency in a uniformly drawn VOTER slot: the slot law's conditional
frequency, which is the ratio of expected counts. -/
def slotSilentFrequency (L : Law (Fin 4 → Gt)) : ℝ :=
  (slotLaw L).mass (false,true) / voterMass (slotLaw L)

theorem slotSilentFrequency_eq (L : Law (Fin 4 → Gt)) :
    slotSilentFrequency L = L.expect silentCountR / L.expect voterCountR := by
  unfold slotSilentFrequency voterMass
  simp only [slotLaw_mass]
  have h1 : silentCountR = fun z : Fin 4 → Gt => (wordCount z (false,true) : ℝ) :=
    funext (fun z => silentCountR_eq_count z)
  have h2 : voterCountR = fun z : Fin 4 → Gt =>
      (wordCount z (false,false) : ℝ) + wordCount z (false,true) :=
    funext (fun z => voterCountR_eq_counts z)
  rw [h1, h2, Law.expect_add]
  rw [← add_div, div_div_div_cancel_right₀ (by norm_num : (4:ℝ) ≠ 0)]

theorem pointLaw_expect {Ω : Type*} [Fintype Ω] (z : Ω) (F : Ω → ℝ) : (pointLaw z).expect F = F z := by
  unfold Law.expect Law1.mean pointLaw; simp

/-- Referee G3 refuter (exact).  In the finite model `P=4, S=2` started at `00,01,00,10`, the
random-voter-slot silent frequency is `1/3, 7/20, 37/100` at `t = 0, 1, 2`, while the C.5
deterministic recursion with `η = (1-S/P)μ = 1/20` gives `1/3, 7/20, 73/200`: they agree for one
step and disagree at `t = 2`. -/
theorem g3_refuter :
    slotSilentFrequency (g3Law 0) = 1/3 ∧
      slotSilentFrequency (g3Law 1) = 7/20 ∧
      slotSilentFrequency (g3Law 2) = 37/100 ∧
      silentRecursion ((1 - 2/4) * (1/10)) (1/3) 1 = 7/20 ∧
      silentRecursion ((1 - 2/4) * (1/10)) (1/3) 2 = 73/200 ∧
      slotSilentFrequency (g3Law 2) ≠ silentRecursion ((1 - 2/4) * (1/10)) (1/3) 2 := by
  have h0 : slotSilentFrequency (g3Law 0) = 1/3 := by
    rw [slotSilentFrequency_eq]
    change (pointLaw g3Start).expect silentCountR / (pointLaw g3Start).expect voterCountR = _
    rw [pointLaw_expect, pointLaw_expect]
    unfold silentCountR voterCountR
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    norm_num [g3Start_0, g3Start_1, g3Start_2, g3Start_3]
  have h1 : slotSilentFrequency (g3Law 1) = 7/20 := by
    rw [slotSilentFrequency_eq, g3_t1_silent, g3_t1_voter]; norm_num
  have h2 : slotSilentFrequency (g3Law 2) = 37/100 := by
    rw [slotSilentFrequency_eq, g3_t2_silent, g3_t2_voter]; norm_num
  have r1 : silentRecursion ((1 - 2/4) * (1/10)) (1/3) 1 = 7/20 := by
    norm_num [silentRecursion]
  have r2 : silentRecursion ((1 - 2/4) * (1/10)) (1/3) 2 = 73/200 := by
    norm_num [silentRecursion]
  refine ⟨h0, h1, h2, r1, r2, ?_⟩
  rw [h2, r2]; norm_num

end G3Refuter

end
end SEKernel.Closeout.GenesSpawn

#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_zero
#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_succ
#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_closed
#print axioms SEKernel.Closeout.GenesSpawn.silent_fixed_point_iff
#print axioms SEKernel.Closeout.GenesSpawn.silent_half_fixed
#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_distance
#print axioms SEKernel.Closeout.GenesSpawn.silent_contraction
#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_tendsto
#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_from_zero
#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_monotone_from_zero
#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_from_zero_bounds
#print axioms SEKernel.Closeout.GenesSpawn.silentRecursion_not_monotone_above_half
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.select_mass
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.select_voterShare_pos
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.next_voterShare
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.next_silent_mass
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.next_silent_frequency
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.orbit_voterShare_pos
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.orbit_silent_frequency
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.orbit_silent_closed
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.eta_nonneg
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.eta_le_mu
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.orbit_monotone_from_zero
#print axioms SEKernel.Closeout.GenesSpawn.SilentLifecycle.orbit_tendsto_half
#print axioms SEKernel.Closeout.GenesSpawn.docB_silent_example
#print axioms SEKernel.Closeout.GenesSpawn.scalar_y_denominator_pos
#print axioms SEKernel.Closeout.GenesSpawn.scalar_y_increment
#print axioms SEKernel.Closeout.GenesSpawn.scalar_y_increases_iff
#print axioms SEKernel.Closeout.GenesSpawn.scalar_y_endpoints
#print axioms SEKernel.Closeout.GenesSpawn.actual_y_step
#print axioms SEKernel.Closeout.GenesSpawn.actual_B_step
#print axioms SEKernel.Closeout.GenesSpawn.slot_eq_iff
#print axioms SEKernel.Closeout.GenesSpawn.prefixClosed_of_threshold
#print axioms SEKernel.Closeout.GenesSpawn.nextSlot_not_mem
#print axioms SEKernel.Closeout.GenesSpawn.lastSlot_mem
#print axioms SEKernel.Closeout.GenesSpawn.not_mem_le_next
#print axioms SEKernel.Closeout.GenesSpawn.mem_ge_last
#print axioms SEKernel.Closeout.GenesSpawn.insert_next_prefix
#print axioms SEKernel.Closeout.GenesSpawn.swap_prefix
#print axioms SEKernel.Closeout.GenesSpawn.optimal_implies_exchange
#print axioms SEKernel.Closeout.GenesSpawn.exchange_implies_certificate
#print axioms SEKernel.Closeout.GenesSpawn.prefix_optimal_iff_exchange
#print axioms SEKernel.Closeout.GenesSpawn.mem_prefixSet
#print axioms SEKernel.Closeout.GenesSpawn.prefixSet_closed
#print axioms SEKernel.Closeout.GenesSpawn.taskCount_prefixSet
#print axioms SEKernel.Closeout.GenesSpawn.prefixSet_card
#print axioms SEKernel.Closeout.GenesSpawn.prefixSet_taskCount
#print axioms SEKernel.Closeout.GenesSpawn.toPrefix_taskCount
#print axioms SEKernel.Closeout.GenesSpawn.reachObjective_eq_slotValue
#print axioms SEKernel.Closeout.GenesSpawn.exists_optimal_nat_allocation
#print axioms SEKernel.Closeout.GenesSpawn.nat_optimal_iff_prefix_optimal
#print axioms SEKernel.Closeout.GenesSpawn.nat_allocation_optimal_iff
#print axioms SEKernel.Closeout.GenesSpawn.nat_allocation_optimal_iff_shadow_price
#print axioms SEKernel.Closeout.GenesSpawn.cellPayoff_decomp
#print axioms SEKernel.Closeout.GenesSpawn.threeCell_decomposition
#print axioms SEKernel.Closeout.GenesSpawn.threeCell_increment
#print axioms SEKernel.Closeout.GenesSpawn.prob_not_and_of_subset
#print axioms SEKernel.Closeout.GenesSpawn.threeCell_posted_decomposition
#print axioms SEKernel.Closeout.GenesSpawn.prob_prod_and
#print axioms SEKernel.Closeout.GenesSpawn.reaches_succ_iff
#print axioms SEKernel.Closeout.GenesSpawn.prob_label_eq
#print axioms SEKernel.Closeout.GenesSpawn.first_hit_probability
#print axioms SEKernel.Closeout.GenesSpawn.fixed_benchmark_marginal
#print axioms SEKernel.Closeout.GenesSpawn.fixed_benchmark_marginal_abs_le
#print axioms SEKernel.Closeout.GenesSpawn.independent_benchmark_marginal
#print axioms SEKernel.Closeout.GenesSpawn.posted_benchmark_payoff
#print axioms SEKernel.Closeout.GenesSpawn.posted_benchmark_marginal
#print axioms SEKernel.Closeout.GenesSpawn.posted_benchmark_premium_marginal
#print axioms SEKernel.Closeout.GenesSpawn.selection_regret_bound
#print axioms SEKernel.Closeout.GenesSpawn.recombine_signed
#print axioms SEKernel.Closeout.GenesSpawn.recombine_voterMass
#print axioms SEKernel.Closeout.GenesSpawn.advocate_conditional_decomposition
#print axioms SEKernel.Closeout.GenesSpawn.recombine_condQ
#print axioms SEKernel.Closeout.GenesSpawn.recombine_condZ
#print axioms SEKernel.Closeout.GenesSpawn.linkage_conditional
#print axioms SEKernel.Closeout.GenesSpawn.elite_mixing_recombination
#print axioms SEKernel.Closeout.GenesSpawn.elite_independent_crossover
#print axioms SEKernel.Closeout.GenesSpawn.elite_distinct_crossover
#print axioms SEKernel.Closeout.GenesSpawn.uniform_slot_identification
#print axioms SEKernel.Closeout.GenesSpawn.selection_recombination_creates_silent
#print axioms SEKernel.Closeout.GenesSpawn.mutate_board_coordinate
#print axioms SEKernel.Closeout.GenesSpawn.mutate_boardMass
#print axioms SEKernel.Closeout.GenesSpawn.OrderModel.c_pos
#print axioms SEKernel.Closeout.GenesSpawn.OrderModel.selected_compartments
#print axioms SEKernel.Closeout.GenesSpawn.OrderModel.selected_condZ
#print axioms SEKernel.Closeout.GenesSpawn.OrderModel.selected_condQ_ge
#print axioms SEKernel.Closeout.GenesSpawn.OrderModel.step_order
#print axioms SEKernel.Closeout.GenesSpawn.OrderModel.orbit_order
#print axioms SEKernel.Closeout.GenesSpawn.OrderModel.orbit_ge_neutral
#print axioms SEKernel.Closeout.GenesSpawn.binomialMix_succ
#print axioms SEKernel.Closeout.GenesSpawn.iid_expect_succ
#print axioms SEKernel.Closeout.GenesSpawn.silentCountR_cons
#print axioms SEKernel.Closeout.GenesSpawn.voterCountR_cons
#print axioms SEKernel.Closeout.GenesSpawn.iid_ratio_binomial
#print axioms SEKernel.Closeout.GenesSpawn.nextSilentExpectation_binomial
#print axioms SEKernel.Closeout.GenesSpawn.nextSilentExpectation_binomial_pos
#print axioms SEKernel.Closeout.GenesSpawn.nextSilentExpectation_no_voter_children
#print axioms SEKernel.Closeout.GenesSpawn.law_map_bind
#print axioms SEKernel.Closeout.GenesSpawn.law_bind_map
#print axioms SEKernel.Closeout.GenesSpawn.law_map_map
#print axioms SEKernel.Closeout.GenesSpawn.fullStateKernel_mass
#print axioms SEKernel.Closeout.GenesSpawn.fullStateKernel_projection
#print axioms SEKernel.Closeout.GenesSpawn.marginY_mean
#print axioms SEKernel.Closeout.GenesSpawn.marginY_variance
#print axioms SEKernel.Closeout.GenesSpawn.marginY_count_sum
#print axioms SEKernel.Closeout.GenesSpawn.wrong_mode_count_bound
#print axioms SEKernel.Closeout.GenesSpawn.wrong_mode_accuracy_bound
#print axioms SEKernel.Closeout.GenesSpawn.blockSize_sum
#print axioms SEKernel.Closeout.GenesSpawn.clone_sum_blocks
#print axioms SEKernel.Closeout.GenesSpawn.clone_block_reduction
#print axioms SEKernel.Closeout.GenesSpawn.decisionValue_mono
#print axioms SEKernel.Closeout.GenesSpawn.decisionValue_monotone
#print axioms SEKernel.Closeout.GenesSpawn.kernelProd_mass
#print axioms SEKernel.Closeout.GenesSpawn.matrixProd_stochastic
#print axioms SEKernel.Closeout.GenesSpawn.replayLaw_mass
#print axioms SEKernel.Closeout.GenesSpawn.replay_expectation
#print axioms SEKernel.Closeout.GenesSpawn.matrixProd_const
#print axioms SEKernel.Closeout.GenesSpawn.replay_expectation_pow
#print axioms SEKernel.Closeout.GenesSpawn.roleTopSets_nonempty
#print axioms SEKernel.Closeout.GenesSpawn.roleSelection_expect
#print axioms SEKernel.Closeout.GenesSpawn.sum_selectedRoster
#print axioms SEKernel.Closeout.GenesSpawn.roleTop_all_boards
#print axioms SEKernel.Closeout.GenesSpawn.roleTop_one_board_sum
#print axioms SEKernel.Closeout.GenesSpawn.roleTop_one_board_card
#print axioms SEKernel.Closeout.GenesSpawn.one_board_of_card
#print axioms SEKernel.Closeout.GenesSpawn.roleSelection_one_board
#print axioms SEKernel.Closeout.GenesSpawn.roleSelection_many_boards
#print axioms SEKernel.Closeout.GenesSpawn.g3Start_0
#print axioms SEKernel.Closeout.GenesSpawn.g3Start_1
#print axioms SEKernel.Closeout.GenesSpawn.g3Start_2
#print axioms SEKernel.Closeout.GenesSpawn.g3Start_3
#print axioms SEKernel.Closeout.GenesSpawn.psiSilent_board
#print axioms SEKernel.Closeout.GenesSpawn.psiVoter_board
#print axioms SEKernel.Closeout.GenesSpawn.g3Child_silent
#print axioms SEKernel.Closeout.GenesSpawn.g3Child_voter
#print axioms SEKernel.Closeout.GenesSpawn.g3Step_silent
#print axioms SEKernel.Closeout.GenesSpawn.g3Step_voter
#print axioms SEKernel.Closeout.GenesSpawn.pointLaw_bind_expect
#print axioms SEKernel.Closeout.GenesSpawn.g3Start_boards
#print axioms SEKernel.Closeout.GenesSpawn.g3_t1_silent
#print axioms SEKernel.Closeout.GenesSpawn.g3_t1_voter
#print axioms SEKernel.Closeout.GenesSpawn.boardSet_card_eq
#print axioms SEKernel.Closeout.GenesSpawn.boardSet_nextRoster
#print axioms SEKernel.Closeout.GenesSpawn.next_generation_pointwise
#print axioms SEKernel.Closeout.GenesSpawn.brood_expect
#print axioms SEKernel.Closeout.GenesSpawn.expect_voterInd
#print axioms SEKernel.Closeout.GenesSpawn.expect_voterInd_silent
#print axioms SEKernel.Closeout.GenesSpawn.expect_voterInd_voter
#print axioms SEKernel.Closeout.GenesSpawn.pair_survivor_mass
#print axioms SEKernel.Closeout.GenesSpawn.pair_board_card
#print axioms SEKernel.Closeout.GenesSpawn.pair_psi_sum
#print axioms SEKernel.Closeout.GenesSpawn.second_generation_pair
#print axioms SEKernel.Closeout.GenesSpawn.theta_expect_voterInd
#print axioms SEKernel.Closeout.GenesSpawn.theta_expect_silent
#print axioms SEKernel.Closeout.GenesSpawn.theta_expect_voter
#print axioms SEKernel.Closeout.GenesSpawn.g3Start_voters
#print axioms SEKernel.Closeout.GenesSpawn.g3_two_step
#print axioms SEKernel.Closeout.GenesSpawn.erase_three
#print axioms SEKernel.Closeout.GenesSpawn.pair_voterMass
#print axioms SEKernel.Closeout.GenesSpawn.g3_t2_silent
#print axioms SEKernel.Closeout.GenesSpawn.g3_t2_voter
#print axioms SEKernel.Closeout.GenesSpawn.mass_eq_expect_indicator
#print axioms SEKernel.Closeout.GenesSpawn.slotLaw_mass
#print axioms SEKernel.Closeout.GenesSpawn.voterCountR_eq_counts
#print axioms SEKernel.Closeout.GenesSpawn.slotSilentFrequency_eq
#print axioms SEKernel.Closeout.GenesSpawn.pointLaw_expect
#print axioms SEKernel.Closeout.GenesSpawn.g3_refuter
