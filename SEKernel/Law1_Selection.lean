/-
SEKernel / Law1_Selection.lean
Law 1 (Strategic Selection) — arXiv:2512.07901 §3, discrete-time kernel form.

Discrete-time finite-type replicator: state `x` on the simplex, fitness
vector `f > 0`, update `x'_j = x_j f_j / f̄(x)`.  Deviations from the paper's
continuous-time statements are handoff-pre-approved and recorded
(STATEMENTS.md, AQ-1..AQ-4).

Main results:
* `selection_gain`        — Prop 3.1 (Price), selection term exact:
  `Σ_j x'_j f_j − f̄ = Var_x(f)/f̄`.
* `price_decomposition`   — the full discrete Price identity
  `f̄(x') − f̄(x) = Var/f̄ + E_disc`.
* `SS1_discrete`          — Theorem 3.3 (SS-1): under discrete H-γ,
  `f̄(x') − f̄(x) ≥ (1−γ)·Var/f̄ ≥ 0`.
* `SS1_equality_iff`      — the equality case: change = 0 ↔ Var = 0.
* `variance_eq_zero_iff`  — Var = 0 ↔ all supported types have mean fitness.
* `elimination_single_*`  — Theorem 3.5 (SS-2a), single-type ratio
  domination: exact geometric decay and `x_d(t) → 0`.
* `elimination_mixture`   — Theorem 3.5 (SS-2a), mixture domination in
  geometric-mean form (AQ-2), via the paper's log-contrast — including the
  Step-4 simplification found in Phase 0 (the product `Π x_k^{α_k} ≤ 1`
  bound makes survival-of-the-mixture unnecessary).
* `frontier_support`      — Theorem 3.6 (SS-2b), conditional on the
  hull-domination interface (AQ-3).
* `basin_decrease`, `basin_instability`, `basin_no_recovery` —
  Theorem 3.7 (Basin Limitation), discrete orbit form (AQ-4).

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace Law1

open Finset Filter

variable {ι : Type*} [Fintype ι]

/-- Mean performance `f̄(x) = Σ_j x_j f_j` (Definition 2.3). -/
def mean (x f : ι → ℝ) : ℝ := ∑ j, x j * f j

/-- Performance variance `Var_x(f) = Σ_j x_j (f_j − f̄)²` (Definition 2.3). -/
def variance (x f : ι → ℝ) : ℝ := ∑ j, x j * (f j - mean x f) ^ 2

/-- One step of the discrete-time replicator: `x'_j = x_j f_j / f̄(x)`. -/
noncomputable def step (x f : ι → ℝ) : ι → ℝ := fun j => x j * f j / mean x f

theorem variance_nonneg {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j) :
    0 ≤ variance x f :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hx j) (sq_nonneg _)

theorem mean_pos {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j) (hsum : ∑ j, x j = 1)
    (hf : ∀ j, 0 < f j) : 0 < mean x f := by
  obtain ⟨j₀, _, hj₀⟩ : ∃ j ∈ Finset.univ, x j ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero (f := x)
    rw [hsum]; exact one_ne_zero
  exact Finset.sum_pos'
    (fun j _ => mul_nonneg (hx j) (le_of_lt (hf j)))
    ⟨j₀, Finset.mem_univ _,
      mul_pos (lt_of_le_of_ne (hx j₀) (Ne.symm hj₀)) (hf j₀)⟩

/-- Second-moment form of the variance (uses `Σ x = 1`). -/
theorem variance_eq {x f : ι → ℝ} (hsum : ∑ j, x j = 1) :
    variance x f = (∑ j, x j * f j ^ 2) - (mean x f) ^ 2 := by
  have h : ∀ j ∈ Finset.univ, x j * (f j - mean x f) ^ 2
      = x j * f j ^ 2 - 2 * mean x f * (x j * f j) + (mean x f) ^ 2 * x j :=
    fun j _ => by ring
  rw [variance, Finset.sum_congr rfl h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hm : ∑ j, x j * f j = mean x f := rfl
  rw [hm, hsum]
  ring

/-- Var = 0 iff every supported type has exactly mean fitness (used for the
SS-1 equality characterisation and Corollary 3.4's `E`-set description). -/
theorem variance_eq_zero_iff {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j) :
    variance x f = 0 ↔ ∀ j, 0 < x j → f j = mean x f := by
  rw [variance, Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hx j) (sq_nonneg _))]
  constructor
  · intro h j hj
    have hterm := h j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hterm with h1 | h2
    · linarith
    · have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
      linarith
  · intro h j _
    rcases lt_or_eq_of_le (hx j) with hj | hj
    · rw [h j hj]
      simp
    · rw [← hj, zero_mul]

theorem step_nonneg {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j) (hf : ∀ j, 0 ≤ f j)
    (hm : 0 ≤ mean x f) (j : ι) : 0 ≤ step x f j :=
  div_nonneg (mul_nonneg (hx j) (hf j)) hm

/-- The replicator step stays on the simplex. -/
theorem step_sum {x f : ι → ℝ} (hm : mean x f ≠ 0) :
    ∑ j, step x f j = 1 := by
  simp only [step]
  rw [← Finset.sum_div]
  have h : ∑ j, x j * f j = mean x f := rfl
  rw [h, div_self hm]

/-- **Proposition 3.1 (Price), selection term exact:** the fitness-weighted
mean after one replicator step exceeds the old mean by exactly `Var/f̄`. -/
theorem selection_gain {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hsum : ∑ j, x j = 1) (hf : ∀ j, 0 < f j) :
    (∑ j, step x f j * f j) - mean x f = variance x f / mean x f := by
  have hm := mean_pos hx hsum hf
  have hm' : mean x f ≠ 0 := ne_of_gt hm
  have h1 : ∑ j, step x f j * f j = (∑ j, x j * f j ^ 2) / mean x f := by
    simp only [step]
    have h : ∀ j ∈ Finset.univ,
        x j * f j / mean x f * f j = x j * f j ^ 2 / mean x f :=
      fun j _ => by ring
    rw [Finset.sum_congr rfl h, ← Finset.sum_div]
  rw [h1, variance_eq hsum, sub_div]
  congr 1
  rw [pow_two, mul_div_assoc, div_self hm', mul_one]

/-- **Discrete Price decomposition** (Prop 3.1 / Definition of `E_disc`,
AQ-1): with `f'` the fitness vector at the stepped state,
`f̄(x') − f̄(x) = Var/f̄ + Σ_j x'_j (f'_j − f_j)`. -/
theorem price_decomposition {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hsum : ∑ j, x j = 1) (hf : ∀ j, 0 < f j) (f' : ι → ℝ) :
    mean (step x f) f' - mean x f
      = variance x f / mean x f + ∑ j, step x f j * (f' j - f j) := by
  have hgain := selection_gain hx hsum hf
  have hsplit : mean (step x f) f'
      = (∑ j, step x f j * f j) + ∑ j, step x f j * (f' j - f j) := by
    rw [mean, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  linarith

/-- **Theorem 3.3 (SS-1: Lyapunov Structure), discrete form.**  Under the
discrete H-γ bound `|E_disc| ≤ γ·Var/f̄` with `γ < 1`:
`f̄(x') − f̄(x) ≥ (1−γ)·Var/f̄ ≥ 0`. -/
theorem SS1_discrete {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hsum : ∑ j, x j = 1) (hf : ∀ j, 0 < f j) (f' : ι → ℝ) {γ : ℝ}
    (hγ1 : γ < 1)
    (hHγ : |∑ j, step x f j * (f' j - f j)|
      ≤ γ * (variance x f / mean x f)) :
    (1 - γ) * (variance x f / mean x f) ≤ mean (step x f) f' - mean x f
      ∧ 0 ≤ (1 - γ) * (variance x f / mean x f) := by
  have hm := mean_pos hx hsum hf
  have hvm : 0 ≤ variance x f / mean x f :=
    div_nonneg (variance_nonneg hx) (le_of_lt hm)
  have hdecomp := price_decomposition hx hsum hf f'
  have hE := abs_le.mp hHγ
  constructor
  · linarith [hE.1]
  · exact mul_nonneg (by linarith) hvm

/-- **SS-1 equality characterisation:** mean fitness stalls exactly at
selection equilibria (`Var = 0`). -/
theorem SS1_equality_iff {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hsum : ∑ j, x j = 1) (hf : ∀ j, 0 < f j) (f' : ι → ℝ) {γ : ℝ}
    (hγ1 : γ < 1)
    (hHγ : |∑ j, step x f j * (f' j - f j)|
      ≤ γ * (variance x f / mean x f)) :
    mean (step x f) f' = mean x f ↔ variance x f = 0 := by
  have hm := mean_pos hx hsum hf
  have hvar := variance_nonneg (f := f) hx
  have hdecomp := price_decomposition hx hsum hf f'
  have hE := abs_le.mp hHγ
  constructor
  · intro heq
    by_contra hne
    have hpos : 0 < variance x f := lt_of_le_of_ne hvar (Ne.symm hne)
    have hvm : 0 < variance x f / mean x f := div_pos hpos hm
    have h1γ : 0 < 1 - γ := by linarith
    nlinarith [mul_pos h1γ hvm]
  · intro h0
    have hVm : variance x f / mean x f = 0 := by rw [h0]; simp
    rw [hVm] at hHγ hdecomp
    have hE0 : ∑ j, step x f j * (f' j - f j) = 0 := by
      have := abs_nonneg (∑ j, step x f j * (f' j - f j))
      have habs : |∑ j, step x f j * (f' j - f j)| = 0 := by linarith [hHγ]
      exact abs_eq_zero.mp habs
    rw [hE0] at hdecomp
    linarith

/-! ### Orbits and elimination (SS-2a) -/

section Orbits

variable {x : ℕ → ι → ℝ} {f : ℕ → ι → ℝ}

/-- Simplex invariance along replicator orbits. -/
theorem orbit_invariant
    (hx0 : ∀ j, 0 ≤ x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t)) :
    ∀ t, (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1 := by
  intro t
  induction t with
  | zero => exact ⟨hx0, hsum0⟩
  | succ k ih =>
    have hm := mean_pos ih.1 ih.2 (hf k)
    rw [hstep k]
    exact ⟨step_nonneg ih.1 (fun j => (hf k j).le) hm.le,
      step_sum (ne_of_gt hm)⟩

/-- Positivity of a coordinate is preserved along orbits. -/
theorem orbit_pos_coord
    (hx0 : ∀ j, 0 ≤ x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t))
    {k : ι} (hk : 0 < x 0 k) : ∀ t, 0 < x t k := by
  intro t
  induction t with
  | zero => exact hk
  | succ s ih =>
    have hinv := orbit_invariant hx0 hsum0 hf hstep s
    have hm := mean_pos hinv.1 hinv.2 (hf s)
    rw [hstep s]
    exact div_pos (mul_pos ih (hf s k)) hm

/-- Coordinates are bounded by 1 on the simplex. -/
theorem coord_le_one {z : ι → ℝ} (hz : ∀ j, 0 ≤ z j) (hs : ∑ j, z j = 1)
    (k : ι) : z k ≤ 1 := by
  calc z k ≤ ∑ j, z j :=
        Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ k)
    _ = 1 := hs

/-- **Theorem 3.5 (SS-2a), single-type ratio domination — exact decay.**
If `f_d ≤ ρ·f_k` along the orbit, then
`x_t(d) · x_0(k) ≤ ρ^t · x_0(d) · x_t(k)`. -/
theorem elimination_single_bound
    (hx0 : ∀ j, 0 ≤ x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t))
    {d k : ι} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hdom : ∀ t, f t d ≤ ρ * f t k) (hk0 : 0 < x 0 k) :
    ∀ t, x t d * x 0 k ≤ ρ ^ t * x 0 d * x t k := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    have hinv := orbit_invariant hx0 hsum0 hf hstep t
    have hm := mean_pos hinv.1 hinv.2 (hf t)
    have hxk := orbit_pos_coord hx0 hsum0 hf hstep hk0 t
    have hxd : 0 ≤ x t d := hinv.1 d
    have key : x t d * x 0 k * f t d
        ≤ ρ ^ (t + 1) * x 0 d * (x t k * f t k) := by
      calc x t d * x 0 k * f t d
          ≤ (ρ ^ t * x 0 d * x t k) * f t d :=
            mul_le_mul_of_nonneg_right ih (hf t d).le
        _ ≤ (ρ ^ t * x 0 d * x t k) * (ρ * f t k) := by
            apply mul_le_mul_of_nonneg_left (hdom t)
            have := hx0 d
            positivity
        _ = ρ ^ (t + 1) * x 0 d * (x t k * f t k) := by ring
    rw [hstep t]
    simp only [step]
    calc x t d * f t d / mean (x t) (f t) * x 0 k
        = (x t d * x 0 k * f t d) / mean (x t) (f t) := by ring
      _ ≤ (ρ ^ (t + 1) * x 0 d * (x t k * f t k)) / mean (x t) (f t) := by
          gcongr
      _ = ρ ^ (t + 1) * x 0 d * (x t k * f t k / mean (x t) (f t)) := by
          ring

/-- SS-2a decay in closed form: `x_t(d) ≤ (x_0(d)/x_0(k)) · ρ^t`. -/
theorem elimination_single_decay
    (hx0 : ∀ j, 0 ≤ x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t))
    {d k : ι} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hdom : ∀ t, f t d ≤ ρ * f t k) (hk0 : 0 < x 0 k) :
    ∀ t, x t d ≤ x 0 d / x 0 k * ρ ^ t := by
  intro t
  have hb := elimination_single_bound hx0 hsum0 hf hstep hρ0 hdom hk0 t
  have hinv := orbit_invariant hx0 hsum0 hf hstep t
  have hk1 : x t k ≤ 1 := coord_le_one hinv.1 hinv.2 k
  rw [div_mul_eq_mul_div, le_div_iff₀ hk0]
  calc x t d * x 0 k ≤ ρ ^ t * x 0 d * x t k := hb
    _ ≤ ρ ^ t * x 0 d * 1 := by
        apply mul_le_mul_of_nonneg_left hk1
        have := hx0 d
        positivity
    _ = x 0 d * ρ ^ t := by ring

/-- **Theorem 3.5 (SS-2a), single-type domination — elimination:**
`x_t(d) → 0`. -/
theorem elimination_single_tendsto
    (hx0 : ∀ j, 0 ≤ x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t))
    {d k : ι} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdom : ∀ t, f t d ≤ ρ * f t k) (hk0 : 0 < x 0 k) :
    Tendsto (fun t => x t d) atTop (nhds 0) := by
  apply squeeze_zero
    (fun t => (orbit_invariant hx0 hsum0 hf hstep t).1 d)
    (elimination_single_decay hx0 hsum0 hf hstep hρ0 hdom hk0)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  simpa using h.const_mul (x 0 d / x 0 k)

/-- Interior orbits stay interior. -/
theorem orbit_pos_all
    (hx0 : ∀ j, 0 < x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t)) :
    ∀ t j, 0 < x t j := fun t j =>
  orbit_pos_coord (fun i => (hx0 i).le) hsum0 hf hstep (hx0 j) t

/-- **Theorem 3.5 (SS-2a), mixture domination (geometric-mean form, AQ-2).**
Log-contrast argument with the Phase-0 simplification: since
`Σ_k α_k log x_t(k) ≤ 0` on the simplex, `x_t(d) ≤ exp(φ_t)` directly and the
paper's Step 4 (survival of the dominating mixture) is not needed.
`α` is a mixture with `α d = 0` (equivalently, supported off `d`). -/
theorem elimination_mixture
    (hx0 : ∀ j, 0 < x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t))
    (d : ι) (α : ι → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∑ k, α k = 1)
    {δ : ℝ}
    (hdom : ∀ t, Real.log (f t d)
      ≤ (∑ k, α k * Real.log (f t k)) - δ) :
    ∀ t, x t d ≤ Real.exp (Real.log (x 0 d)
      - ∑ k, α k * Real.log (x 0 k)) * Real.exp (-δ) ^ t := by
  have hpos : ∀ t j, 0 < x t j := orbit_pos_all hx0 hsum0 hf hstep
  set φ : ℕ → ℝ :=
    fun t => Real.log (x t d) - ∑ k, α k * Real.log (x t k) with hφ
  -- one-step change of the log-contrast
  have hφstep : ∀ t, φ (t + 1)
      = φ t + (Real.log (f t d) - ∑ k, α k * Real.log (f t k)) := by
    intro t
    have hinv := orbit_invariant (fun j => (hx0 j).le) hsum0 hf hstep t
    have hm := mean_pos hinv.1 hinv.2 (hf t)
    have hlog : ∀ j, Real.log (x (t + 1) j)
        = Real.log (x t j) + Real.log (f t j)
          - Real.log (mean (x t) (f t)) := by
      intro j
      rw [hstep t]
      simp only [step]
      rw [Real.log_div (mul_ne_zero (ne_of_gt (hpos t j))
        (ne_of_gt (hf t j))) (ne_of_gt hm),
        Real.log_mul (ne_of_gt (hpos t j)) (ne_of_gt (hf t j))]
    have hsumlog : ∑ k, α k * Real.log (x (t + 1) k)
        = (∑ k, α k * Real.log (x t k))
          + (∑ k, α k * Real.log (f t k))
          - Real.log (mean (x t) (f t)) := by
      calc ∑ k, α k * Real.log (x (t + 1) k)
          = ∑ k, (α k * Real.log (x t k) + α k * Real.log (f t k)
              - α k * Real.log (mean (x t) (f t))) :=
            Finset.sum_congr rfl fun k _ => by rw [hlog k]; ring
        _ = (∑ k, α k * Real.log (x t k))
            + (∑ k, α k * Real.log (f t k))
            - ∑ k, α k * Real.log (mean (x t) (f t)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        _ = (∑ k, α k * Real.log (x t k))
            + (∑ k, α k * Real.log (f t k))
            - Real.log (mean (x t) (f t)) := by
            rw [← Finset.sum_mul, hα1, one_mul]
    simp only [hφ]
    rw [hlog d, hsumlog]
    ring
  -- linear decay of the log-contrast
  have hφbound : ∀ t, φ t ≤ φ 0 - δ * t := by
    intro t
    induction t with
    | zero => simp
    | succ s ih =>
      have hstep' := hφstep s
      have hd := hdom s
      have : φ (s + 1) ≤ φ s - δ := by rw [hstep']; linarith
      calc φ (s + 1) ≤ (φ 0 - δ * s) - δ := by linarith
        _ = φ 0 - δ * (s + 1 : ℕ) := by push_cast; ring
  -- convert to the population share
  intro t
  have hinv := orbit_invariant (fun j => (hx0 j).le) hsum0 hf hstep t
  have hxd : x t d = Real.exp (φ t + ∑ k, α k * Real.log (x t k)) := by
    simp only [hφ, sub_add_cancel]
    exact (Real.exp_log (hpos t d)).symm
  have hsumlog0 : ∑ k, α k * Real.log (x t k) ≤ 0 :=
    Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonneg_of_nonpos (hα0 k)
        (Real.log_nonpos (hpos t k).le (coord_le_one hinv.1 hinv.2 k))
  calc x t d = Real.exp (φ t + ∑ k, α k * Real.log (x t k)) := hxd
    _ ≤ Real.exp (φ 0 - δ * t) := by
        apply Real.exp_le_exp.mpr
        linarith [hφbound t]
    _ = Real.exp (φ 0) * Real.exp (-δ) ^ t := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring

/-- SS-2a mixture domination — elimination: `x_t(d) → 0` when `δ > 0`. -/
theorem elimination_mixture_tendsto
    (hx0 : ∀ j, 0 < x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t))
    (d : ι) (α : ι → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∑ k, α k = 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ t, Real.log (f t d)
      ≤ (∑ k, α k * Real.log (f t k)) - δ) :
    Tendsto (fun t => x t d) atTop (nhds 0) := by
  apply squeeze_zero
    (fun t => (orbit_invariant (fun j => (hx0 j).le) hsum0 hf hstep t).1 d)
    (elimination_mixture hx0 hsum0 hf hstep d α hα0 hα1 hdom)
  have hlt : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hlt
  simpa using h.const_mul (Real.exp (Real.log (x 0 d)
    - ∑ k, α k * Real.log (x 0 k)))

/-- **Theorem 3.6 (SS-2b: Frontier Support), conditional form (AQ-3).**
If every non-frontier type is ratio-dominated along the orbit (the
hull-domination interface) and `x*` is a pointwise limit of the orbit, then
the support of `x*` lies in the frontier `F`. -/
theorem frontier_support
    (hx0 : ∀ j, 0 ≤ x 0 j) (hsum0 : ∑ j, x 0 j = 1)
    (hf : ∀ t j, 0 < f t j)
    (hstep : ∀ t, x (t + 1) = step (x t) (f t))
    (F : Set ι)
    (hdom : ∀ j ∉ F, ∃ (k : ι) (ρ : ℝ), 0 ≤ ρ ∧ ρ < 1 ∧
      (∀ t, f t j ≤ ρ * f t k) ∧ 0 < x 0 k)
    (xstar : ι → ℝ)
    (hlim : ∀ j, Tendsto (fun t => x t j) atTop (nhds (xstar j))) :
    ∀ j, 0 < xstar j → j ∈ F := by
  intro j hj
  by_contra hjF
  obtain ⟨k, ρ, hρ0, hρ1, hdomj, hk0⟩ := hdom j hjF
  have h0 : Tendsto (fun t => x t j) atTop (nhds 0) :=
    elimination_single_tendsto hx0 hsum0 hf hstep hρ0 hρ1 hdomj hk0
  have := tendsto_nhds_unique (hlim j) h0
  linarith

end Orbits

/-! ### Basin Limitation (Theorem 3.7, discrete orbit form) -/

section Basin

variable {y : ℕ → ℝ} {η : ℕ → ℝ} {g : ℝ → ℝ}

/-- One-step decrease inside a misalignment band: if `g < 0` on `(c, 1)` and
the orbit sits there, the aligned share strictly drops. -/
theorem basin_decrease
    (hstep : ∀ t, y (t + 1) = y t + η t * (y t * (1 - y t) * g (y t)))
    (hη : ∀ t, 0 < η t) {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ z, c < z → z < 1 → g z < 0)
    {t : ℕ} (h1 : c < y t) (h2 : y t < 1) : y (t + 1) < y t := by
  rw [hstep t]
  have hy0 : 0 < y t := lt_of_le_of_lt hc h1
  have hprod : y t * (1 - y t) * g (y t) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hy0 (by linarith)) (hg _ h1 h2)
  have hneg : η t * (y t * (1 - y t) * g (y t)) < 0 :=
    mul_neg_of_pos_of_neg (hη t) hprod
  linarith

/-- **Theorem 3.7(a) (Basin Limitation — instability of full alignment),
discrete form (AQ-4).**  If `g < 0` on `(c, 1)` and the orbit never reaches 1
exactly, the orbit cannot converge to full alignment. -/
theorem basin_instability
    (hstep : ∀ t, y (t + 1) = y t + η t * (y t * (1 - y t) * g (y t)))
    (hη : ∀ t, 0 < η t) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hg : ∀ z, c < z → z < 1 → g z < 0) (hlt : ∀ t, y t < 1) :
    ¬ Tendsto y atTop (nhds 1) := by
  intro h
  obtain ⟨T, hT⟩ : ∃ T, ∀ t ≥ T, c < y t :=
    Filter.eventually_atTop.mp (h.eventually (eventually_gt_nhds hc1))
  have hmono : ∀ n : ℕ, y (T + n) ≤ y T := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hdec := basin_decrease hstep hη hc0 hg
        (hT (T + k) (Nat.le_add_right T k)) (hlt (T + k))
      have harr : T + (k + 1) = (T + k) + 1 := by ring
      rw [harr]
      linarith
  obtain ⟨T', hT'⟩ : ∃ T', ∀ t ≥ T', y T < y t :=
    Filter.eventually_atTop.mp (h.eventually (eventually_gt_nhds (hlt T)))
  have h1 := hmono (max T T' - T)
  rw [Nat.add_sub_cancel' (le_max_left T T')] at h1
  have h2 := hT' (max T T') (le_max_right T T')
  linarith

/-- **Theorem 3.7(b) (Basin Limitation — point of no return), discrete form
(AQ-4).**  With the no-overshoot interface (`y ≤ x̃ ⟹ y' ≤ x̃`) and `x̃ < 1`:
once the aligned share falls to `x̃` or below, the orbit is trapped there and
cannot recover to full alignment. -/
theorem basin_no_recovery {xt : ℝ}
    (hno : ∀ t, y t ≤ xt → y (t + 1) ≤ xt) (hxt1 : xt < 1)
    {T : ℕ} (hT : y T ≤ xt) : ¬ Tendsto y atTop (nhds 1) := by
  intro h
  have htrap : ∀ n : ℕ, y (T + n) ≤ xt := by
    intro n
    induction n with
    | zero => simpa using hT
    | succ k ih =>
      have harr : T + (k + 1) = (T + k) + 1 := by ring
      rw [harr]
      exact hno (T + k) ih
  obtain ⟨T', hT'⟩ : ∃ T', ∀ t ≥ T', xt < y t :=
    Filter.eventually_atTop.mp (h.eventually (eventually_gt_nhds hxt1))
  have h1 := htrap (max T T' - T)
  rw [Nat.add_sub_cancel' (le_max_left T T')] at h1
  have h2 := hT' (max T T') (le_max_right T T')
  linarith

end Basin

end Law1
end SEKernel
