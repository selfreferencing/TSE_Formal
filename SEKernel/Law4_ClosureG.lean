/-
SEKernel / Law4_ClosureG.lean
Law 4 (G∞ Closure) — arXiv:2512.07901 §11, certificate form.

Block extensions of the N-level stack and the slack-budget calculus.
The paper's Lemma 11.3 and Theorem 11.7(d) invoke spectral-perturbation /
"Gershgorin" displays that are flagged for repair (STATEMENTS.md, AQ-10);
the kernel instead proves an exact **Certificate Extension Lemma** with an
explicit extended weight vector, which delivers the same downstream
conclusions (slack budget 11.4, safe stack depth 11.6, no-infinite-regress
11.8, closure clause 11.7(d)) with quantified margins.

Main results:
* `extension_cert`      — Certificate Extension Lemma: a small-gain
  certificate for Γ extends to the block matrix Γ̃ = [[Γ, b],[cᵀ, 0]]
  whenever the new couplings b, c are small in the weighted sense; the
  new weight is the explicit `w = ⟨b,v⟩ + m'`.  (Kernel form of
  Lemma 11.3 / Theorem 11.7(d).)
* `extension_cert_halfMargin` — the paper's σ/2 clause (11.7(d)) as the
  instance m' = m/2.
* `slack_budget`        — Lemma 11.4: retention factor (1−θ) per step
  keeps margin ≥ (1−θ)^M · σ₀ after M steps.
* `safe_stack_depth`    — Theorem 11.6: if each extension costs at least
  a θ-fraction of margin and the margin floor σ_min is respected, the
  depth obeys θ·M ≤ log(σ₀/σ_min).
* `no_infinite_regress` — Corollary 11.8: with per-step cost θ > 0 and a
  positive margin floor, no infinite admissible extension chain exists.

Zero custom axioms.
-/
import Mathlib
import SEKernel.Law3_Stability

namespace SEKernel
namespace SmallGain

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Block extension of the gain matrix (Definition 11.1): index `none` is the
new level; `Γ̃ = [[Γ, b],[cᵀ, 0]]` — rows/cols `some` are the old levels,
`b ℓ` the new→old coupling on row `some ℓ`, `c ℓ'` the old→new coupling on
row `none`. -/
def extendGain (Γ : L → L → ℝ) (b c : L → ℝ) :
    Option L → Option L → ℝ
  | some ℓ, some ℓ' => Γ ℓ ℓ'
  | some ℓ, none => b ℓ
  | none, some ℓ' => c ℓ'
  | none, none => 0

/-- Extended weight vector `(v, w)`. -/
def extendWeights (v : L → ℝ) (w : ℝ) : Option L → ℝ
  | some ℓ => v ℓ
  | none => w

/-- **Certificate Extension Lemma** (kernel form of Lemma 11.3 = G∞.1 and of
Theorem 11.7(d)).  If `v` certifies small gain for `Γ` with margin `m`, the
new→old couplings `b` are nonnegative, and the old→new couplings `c` satisfy
the weighted smallness condition `c ℓ · (⟨b,v⟩ + m') ≤ m − m'`, then the
explicit extended weights `(v, ⟨b,v⟩ + m')` certify small gain for the block
extension with margin `m'`. -/
theorem extension_cert {Γ : L → L → ℝ} {v : L → ℝ} {m m' : ℝ} {b c : L → ℝ}
    (hcert : SmallGainCert Γ v m)
    (hm' : 0 < m')
    (hb : ∀ ℓ, 0 ≤ b ℓ)
    (hsmall : ∀ ℓ, c ℓ * ((∑ ℓ', b ℓ' * v ℓ') + m') ≤ m - m') :
    SmallGainCert (extendGain Γ b c)
      (extendWeights v ((∑ ℓ', b ℓ' * v ℓ') + m')) m' := by
  have hbv : 0 ≤ ∑ ℓ', b ℓ' * v ℓ' :=
    Finset.sum_nonneg fun ℓ' _ => mul_nonneg (hb ℓ') (le_of_lt (hcert.pos ℓ'))
  constructor
  · -- positivity of extended weights
    intro k
    cases k with
    | some ℓ => exact hcert.pos ℓ
    | none =>
      show (0:ℝ) < (∑ ℓ', b ℓ' * v ℓ') + m'
      linarith
  · -- margins, per column
    intro k
    cases k with
    | some ℓ =>
      -- old column ℓ: margin m − c ℓ · w ≥ m'
      rw [Fintype.sum_option]
      show m' ≤ v ℓ - (c ℓ * ((∑ ℓ', b ℓ' * v ℓ') + m')
        + ∑ ℓ', Γ ℓ' ℓ * v ℓ')
      have hM := hcert.margin ℓ
      have hs := hsmall ℓ
      linarith
    | none =>
      -- new column: margin is exactly m'
      rw [Fintype.sum_option]
      show m' ≤ ((∑ ℓ', b ℓ' * v ℓ') + m')
        - (0 * ((∑ ℓ', b ℓ' * v ℓ') + m') + ∑ ℓ', b ℓ' * v ℓ')
      linarith [zero_mul ((∑ ℓ', b ℓ' * v ℓ') + m')]

/-- Theorem 11.7(d), the σ/2 clause: sufficiently small new couplings preserve
small gain with at least half the margin (instance `m' = m/2`). -/
theorem extension_cert_halfMargin {Γ : L → L → ℝ} {v : L → ℝ} {m : ℝ}
    {b c : L → ℝ}
    (hcert : SmallGainCert Γ v m) (hm : 0 < m)
    (hb : ∀ ℓ, 0 ≤ b ℓ)
    (hsmall : ∀ ℓ, c ℓ * ((∑ ℓ', b ℓ' * v ℓ') + m / 2) ≤ m / 2) :
    SmallGainCert (extendGain Γ b c)
      (extendWeights v ((∑ ℓ', b ℓ' * v ℓ') + m / 2)) (m / 2) := by
  refine extension_cert hcert (by linarith) hb ?_
  intro ℓ
  have := hsmall ℓ
  linarith

/-- Lemma 11.4 (G∞.4: Slack Budget): if every admissible extension retains at
least a `(1−θ)` fraction of the margin, then after `M` extensions the margin
is at least `(1−θ)^M · σ₀`. -/
theorem slack_budget {σ : ℕ → ℝ} {θ : ℝ} (hθ : θ ≤ 1)
    (hstep : ∀ k, (1 - θ) * σ k ≤ σ (k + 1)) :
    ∀ M, (1 - θ) ^ M * σ 0 ≤ σ M := by
  intro M
  induction M with
  | zero => simp
  | succ k ih =>
    have h1θ : 0 ≤ 1 - θ := by linarith
    calc (1 - θ) ^ (k + 1) * σ 0 = (1 - θ) * ((1 - θ) ^ k * σ 0) := by ring
      _ ≤ (1 - θ) * σ k := mul_le_mul_of_nonneg_left ih h1θ
      _ ≤ σ (k + 1) := hstep k

/-- Worst-case consumption: if each extension costs at least a θ-fraction of
margin, margins decay geometrically. -/
theorem slack_decay {σ : ℕ → ℝ} {θ : ℝ} (hθ : θ ≤ 1)
    (hcost : ∀ k, σ (k + 1) ≤ (1 - θ) * σ k) :
    ∀ M, σ M ≤ (1 - θ) ^ M * σ 0 := by
  intro M
  induction M with
  | zero => simp
  | succ k ih =>
    have h1θ : 0 ≤ 1 - θ := by linarith
    calc σ (k + 1) ≤ (1 - θ) * σ k := hcost k
      _ ≤ (1 - θ) * ((1 - θ) ^ k * σ 0) := mul_le_mul_of_nonneg_left ih h1θ
      _ = (1 - θ) ^ (k + 1) * σ 0 := by ring

/-- **Theorem 11.6 (G∞.5: Safe Stack Depth).**  If each extension consumes at
least a θ-fraction of the margin (`σ_{k+1} ≤ (1−θ)σ_k`), all margins respect
the floor `σ_min > 0` up to depth `M`, and `0 < θ < 1`, then

  `θ · M ≤ log (σ₀ / σ_min)`,

the paper's `M ≤ log(σ₀/σ_min)/θ`. -/
theorem safe_stack_depth {σ : ℕ → ℝ} {θ σmin : ℝ} {M : ℕ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcost : ∀ k, σ (k + 1) ≤ (1 - θ) * σ k)
    (hfloor : 0 < σmin) (hM : σmin ≤ σ M) :
    θ * M ≤ Real.log (σ 0 / σmin) := by
  have h0 : σmin ≤ (1 - θ) ^ M * σ 0 :=
    le_trans hM (slack_decay (le_of_lt hθ1) hcost M)
  have h1θ : 0 < 1 - θ := by linarith
  have hσ0 : 0 < σ 0 := by
    by_contra h
    push_neg at h
    have : (1 - θ) ^ M * σ 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (pow_pos h1θ M)) h
    linarith
  -- (1−θ) ≤ exp(−θ), hence (1−θ)^M ≤ exp(−θ)^M = exp(−θM)
  have hexp1 : 1 - θ ≤ Real.exp (-θ) := by
    have := Real.add_one_le_exp (-θ)
    linarith
  have hpow : (1 - θ) ^ M ≤ Real.exp (-θ) ^ M := by
    gcongr
  have hexpM : Real.exp (-θ) ^ M = Real.exp (-(θ * M)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hchain : σmin ≤ Real.exp (-(θ * M)) * σ 0 := by
    calc σmin ≤ (1 - θ) ^ M * σ 0 := h0
      _ ≤ Real.exp (-θ) ^ M * σ 0 :=
          mul_le_mul_of_nonneg_right hpow (le_of_lt hσ0)
      _ = Real.exp (-(θ * M)) * σ 0 := by rw [hexpM]
  -- multiply through by exp(θM):  exp(θM)·σmin ≤ σ₀
  have hkey : Real.exp (θ * M) * σmin ≤ σ 0 := by
    have hepos : (0:ℝ) < Real.exp (θ * M) := Real.exp_pos _
    have h2 := mul_le_mul_of_nonneg_left hchain (le_of_lt hepos)
    calc Real.exp (θ * M) * σmin
        ≤ Real.exp (θ * M) * (Real.exp (-(θ * M)) * σ 0) := h2
      _ = σ 0 := by
          rw [Real.exp_neg]
          field_simp
  -- pass to logs
  have hlog : Real.exp (θ * M) ≤ σ 0 / σmin := by
    rw [le_div_iff₀ hfloor]
    exact hkey
  calc θ * M = Real.log (Real.exp (θ * M)) := (Real.log_exp _).symm
    _ ≤ Real.log (σ 0 / σmin) := Real.log_le_log (Real.exp_pos _) hlog

/-- **Corollary 11.8 (No Infinite Regress).**  With per-step margin cost
`θ ∈ (0,1)` and a positive margin floor `σ_min`, an admissible extension chain
cannot be infinite: some finite depth already violates the floor.  ("Entities
cannot escape selection pressure by going meta.") -/
theorem no_infinite_regress {σ : ℕ → ℝ} {θ σmin : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcost : ∀ k, σ (k + 1) ≤ (1 - θ) * σ k)
    (hfloor : 0 < σmin)
    (hall : ∀ M, σmin ≤ σ M) : False := by
  have hσ0 : 0 < σ 0 := lt_of_lt_of_le hfloor (hall 0)
  obtain ⟨M, hMlt⟩ : ∃ M : ℕ, (1 - θ) ^ M < σmin / σ 0 :=
    exists_pow_lt_of_lt_one (div_pos hfloor hσ0) (by linarith)
  have h1 : σ M ≤ (1 - θ) ^ M * σ 0 := slack_decay (le_of_lt hθ1) hcost M
  have h2 : (1 - θ) ^ M * σ 0 < σmin := (lt_div_iff₀ hσ0).mp hMlt
  have := hall M
  linarith

end SmallGain
end SEKernel
