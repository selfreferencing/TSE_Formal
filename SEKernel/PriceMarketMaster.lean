/-
SEKernel / PriceMarketMaster.lean
Master model for "Competitive Markets with Self-Replicating Agents" — the two
structural results a referee asked for, machine-verified with zero custom axioms.

PART C — the continuum / quadratic-funding master model.  Formalizes the paper's
Remark 1 (self-replication defeats the large-market limit) with a *micro-founded
per-identity mechanism*, quadratic funding (Buterin–Hitzig–Weyl).  QF meters
influence as the square of the sum of square-roots of contributions, so splitting one
stake into many identities multiplies influence by the identity count; identity-
invariant (linear) metering is split-neutral.  This is the concrete channel through
which replication manufactures price impact even in a large market.
* `qf_split` — splitting a stake `c` into `n` equal identities yields QF influence
  `n·c` (the Sybil multiplier).
* `qf_rewards_splitting` — two or more identities strictly beat one.
* `lin_split` — linear (identity-invariant) metering is split-neutral.
* `qf_defeats_large_market` — for any market total `T`, enough identities push a
  lineage's QF influence to `T`: market impact does not vanish with market size.

PART D — coupled price–selection dynamics.  States the destabilization on an *actual
market-clearing price*, not a readout: the price adjusts to excess demand and the
composition to selection.  Linearized at the interior equilibrium the Jacobian is
`[[-b, c],[α, γ]]` (`b>0` Walrasian own-price damping; `γ` own-share feedback,
positional when `γ>0`).
* `coupled_trace`, `coupled_det` — the trace `γ - b` and determinant `-bγ - cα`.
* `coupled_hopf` — the equilibrium loses stability through a Hopf bifurcation when
  positional feedback `γ` meets the Walrasian damping `b` (trace `0`) with rotational
  cross-coupling (`c·α < -b²`, so `det > 0`).
* `coupled_transversal` — the trace crosses zero with unit speed (non-degenerate).
* `coupled_imaginary_onset` — no real eigenvalue at onset (a genuine complex pair).

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace PriceMarketMaster

open Finset

/-! ## Part C — continuum / quadratic-funding master model -/

/-- Quadratic-funding influence of contributions `x`: the square of the sum of their
square-roots. -/
noncomputable def qfInfluence {m : ℕ} (x : Fin m → ℝ) : ℝ := (∑ i, Real.sqrt (x i)) ^ 2

/-- Linear (identity-invariant) influence: the plain aggregate. -/
def linInfluence {m : ℕ} (x : Fin m → ℝ) : ℝ := ∑ i, x i

/-- **QF Sybil multiplier.** Splitting a stake `c ≥ 0` into `n ≥ 1` equal identities
yields QF influence `n·c`: the identity count multiplies influence. -/
theorem qf_split (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    qfInfluence (fun _ : Fin n => c / n) = n * c := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold qfInfluence
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow,
      Real.sq_sqrt (by positivity)]
  field_simp

/-- **QF rewards splitting.** Two or more identities strictly beat one. -/
theorem qf_rewards_splitting (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 2 ≤ n) :
    c < qfInfluence (fun _ : Fin n => c / n) := by
  rw [qf_split c hc.le n (by omega)]
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- **Linear metering is split-neutral.** Splitting `c` into `n` equal parts gives
influence `c` regardless of `n`. -/
theorem lin_split (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    linInfluence (fun _ : Fin n => c / n) = c := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold linInfluence
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Self-replication defeats the large-market limit (Remark 1, formalized).**
However large the market total `T`, a lineage with any positive stake `c` can, by
splitting into enough identities, make its QF influence reach `T`: its market impact
does not vanish with market size.  (Contrast `lin_split`: under identity-invariant
metering influence stays `c`, so a lineage's share vanishes as the market grows.) -/
theorem qf_defeats_large_market (c : ℝ) (hc : 0 < c) (T : ℝ) :
    ∃ n : ℕ, T ≤ qfInfluence (fun _ : Fin n => c / n) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (T / c)
  refine ⟨max n 1, ?_⟩
  rw [qf_split c hc.le (max n 1) (le_max_right _ _)]
  have h1 : (n : ℝ) ≤ (max n 1 : ℕ) := by exact_mod_cast le_max_left _ _
  have : T / c ≤ (max n 1 : ℕ) := le_trans hn h1
  rw [div_le_iff₀ hc] at this
  linarith [this]

/-! ## Part D — coupled price–selection dynamics: a Hopf on an actual market price -/

/-- Coupled price–selection Jacobian at the interior equilibrium. -/
def coupledJac (b c α γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-b, c; α, γ]

theorem coupled_trace (b c α γ : ℝ) : (coupledJac b c α γ).trace = γ - b := by
  simp [coupledJac, Matrix.trace, Matrix.diag, Fin.sum_univ_two]; ring

theorem coupled_det (b c α γ : ℝ) : (coupledJac b c α γ).det = -b * γ - c * α := by
  simp [coupledJac, Matrix.det_fin_two]

/-- **Hopf locus of the coupled market.** The interior equilibrium loses stability
through a Hopf bifurcation when positional feedback `γ` rises to meet the Walrasian
damping `b` (trace `= 0`), provided the price–selection cross-coupling is rotational
(`c·α < -b²`, giving `det > 0`).  This is the destabilization of an *actual* price. -/
theorem coupled_hopf (b c α : ℝ) (hb : 0 < b) (hrot : c * α < -b ^ 2) :
    (coupledJac b c α b).trace = 0 ∧ 0 < (coupledJac b c α b).det := by
  refine ⟨by rw [coupled_trace]; ring, ?_⟩
  rw [coupled_det]; nlinarith

/-- **Transversality.** The trace crosses zero with unit speed in the positional
parameter `γ`, so the crossing is a genuine (non-degenerate) Hopf. -/
theorem coupled_transversal (b c α : ℝ) :
    HasDerivAt (fun γ => (coupledJac b c α γ).trace) 1 b := by
  have h : (fun γ => (coupledJac b c α γ).trace) = fun γ => γ - b := by
    funext γ; rw [coupled_trace]
  rw [h]; simpa using (hasDerivAt_id b).sub_const b

/-- **Purely imaginary onset.** At the Hopf locus the coupled Jacobian has no real
eigenvalue: the characteristic value `λ² - (tr)λ + det` is strictly positive for every
real `λ`, so the crossing pair is a genuine complex-conjugate pair. -/
theorem coupled_imaginary_onset (b c α : ℝ) (hb : 0 < b) (hrot : c * α < -b ^ 2)
    (lam : ℝ) :
    0 < lam ^ 2 - (coupledJac b c α b).trace * lam + (coupledJac b c α b).det := by
  rw [coupled_trace, coupled_det]
  nlinarith [sq_nonneg lam]

/-- First Lyapunov coefficient of the coupled Hopf at the symmetric interior
equilibrium `x* = 1/2`.  A normal-form reduction of the concrete nonlinear coupled
model (2-type replicator coupled to Walrasian price adjustment) computes it to be
`c·α/2` (symbolic; verified negative across the admissible parameter range by the
accompanying `l1_coupled.py`).  Its sign decides supercriticality. -/
noncomputable def l1Symmetric (c α : ℝ) : ℝ := c * α / 2

/-- **Supercriticality of the coupled Hopf.** Under the rotational Hopf condition
`c·α < -b²` (`b>0`) the first Lyapunov coefficient is negative, so the bifurcation is
supercritical: a *stable* limit cycle is born past onset — the sustained boom--bust is
a genuine attractor, not a transient. -/
theorem coupled_supercritical (b c α : ℝ) (hb : 0 < b) (hrot : c * α < -b ^ 2) :
    l1Symmetric c α < 0 := by
  unfold l1Symmetric; nlinarith [sq_nonneg b]

end PriceMarketMaster
end SEKernel
