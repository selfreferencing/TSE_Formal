/-
SEKernel / JuryInversion.lean
The jury inversion: under replication, the effective epistemic sample is the
number of lineages, not the number of heads.

Setting.  `L` independent lineage signals, each of variance `σ2`.  Lineage `i`
is replicated `k i` times, and every clone repeats its lineage's signal exactly
(copies are perfectly correlated).  The head-counted estimate is the mean over
identities — the lineage signals weighted by head shares `k i / n`, where
`n = ∑ k`.  By independence across lineages its variance is
`σ2 * ∑ (k i / n) ^ 2`; that standard formula is taken as the definition
`trueVar`.  The head-counting institution instead attributes to itself the
variance of `n` independent voters, `σ2 / n` (`nominalVar`).

* `trueVar_eq_nEff` — the exact effective-sample identity: `trueVar = σ2 / nEff`
  with `nEff = n² / ∑ k i ²`.
* `trueVar_ge_lineage_bound` / `nEff_le_lineages` — the effective sample size
  is AT MOST the lineage count (Cauchy–Schwarz): cloning adds heads, never
  information.  Equality needs balanced replication; unbalanced replication is
  strictly worse (`nEff_unbalanced_lt_lineages`: lineage sizes (99, 1) give
  `nEff ≈ 1.02`, not 2).
* `jury_inversion` — once any lineage has actually spawned (`2 ≤ k j`), any
  institution that computes its uncertainty by the iid head-count formula
  `σ2 / n` reports strictly less variance than the truth:
  `nominalVar < σ2 / L ≤ trueVar`.  Condorcet's growing-jury guarantee tracks
  lineages (at best), not identities.

Scope note (external referee, 2026-07-29): `trueVar` is the standard
weighted-mean variance formula taken as a definition; a fully probabilistic
derivation from independent random lineage signals, and the partial-correlation
(design-effect) generalization `nEff(ρ) = n / (1 + (k−1)ρ)`, are the next
strengthenings.

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace JuryInversion

open Finset

variable {L : ℕ}

/-- Head share of lineage `i`: its clone count over the total head count. -/
noncomputable def headShare (k : Fin L → ℕ) (i : Fin L) : ℝ :=
  (k i : ℝ) / (∑ j, (k j : ℝ))

/-- Variance of the head-counted mean: independent lineage signals of variance
`σ2`, weighted by head shares (the standard variance formula for a weighted
mean of independent signals). -/
noncomputable def trueVar (σ2 : ℝ) (k : Fin L → ℕ) : ℝ :=
  σ2 * ∑ i, (headShare k i) ^ 2

/-- The variance the head-counting institution believes it has: `n`
independent voters. -/
noncomputable def nominalVar (σ2 : ℝ) (k : Fin L → ℕ) : ℝ :=
  σ2 / (∑ j, (k j : ℝ))

theorem headCount_pos (k : Fin L → ℕ) (hk : ∀ i, 1 ≤ k i) (hL : 0 < L) :
    (0 : ℝ) < ∑ j, (k j : ℝ) := by
  have h1 : ∀ j ∈ (univ : Finset (Fin L)), (1 : ℝ) ≤ (k j : ℝ) := by
    intro j _; exact_mod_cast hk j
  calc (0 : ℝ) < L := by exact_mod_cast hL
    _ = ∑ _j : Fin L, (1 : ℝ) := by simp
    _ ≤ ∑ j, (k j : ℝ) := Finset.sum_le_sum h1

theorem headShare_sum (k : Fin L → ℕ) (hk : ∀ i, 1 ≤ k i) (hL : 0 < L) :
    ∑ i, headShare k i = 1 := by
  have hn : (0 : ℝ) < ∑ j, (k j : ℝ) := headCount_pos k hk hL
  unfold headShare
  rw [← Finset.sum_div, div_self hn.ne']

/-- **Cloning adds heads, never information.**  However the `k i` are chosen,
the variance of the head-counted mean is at least `σ2 / L`: the effective
sample size is the number of independent lineages. -/
theorem trueVar_ge_lineage_bound (σ2 : ℝ) (hσ : 0 ≤ σ2) (k : Fin L → ℕ)
    (hk : ∀ i, 1 ≤ k i) (hL : 0 < L) :
    σ2 / L ≤ trueVar σ2 k := by
  have h1 : ∑ i, headShare k i = 1 := headShare_sum k hk hL
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hCS : (∑ i, headShare k i) ^ 2 ≤
      (∑ i, (headShare k i) ^ 2) * (L : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin L))
      (headShare k) (fun _ => 1)
    simpa using h
  rw [h1] at hCS
  norm_num at hCS
  have hS : 1 / (L : ℝ) ≤ ∑ i, (headShare k i) ^ 2 := by
    rw [div_le_iff₀ hL']
    exact hCS
  calc σ2 / L = σ2 * (1 / L) := by ring
    _ ≤ σ2 * ∑ i, (headShare k i) ^ 2 := mul_le_mul_of_nonneg_left hS hσ
    _ = trueVar σ2 k := rfl

/-- **The jury inversion.**  In any electorate where some lineage has actually
spawned (`2 ≤ k j`), the head-counting institution's nominal variance is
strictly below the lineage floor, which the true variance never crosses:
`nominalVar < σ2 / L ≤ trueVar`.  Head-counted epistemic democracy strictly
overstates its own reliability. -/
theorem jury_inversion (σ2 : ℝ) (hσ : 0 < σ2) (k : Fin L → ℕ)
    (hk : ∀ i, 1 ≤ k i) (hL : 0 < L) (j : Fin L) (hj : 2 ≤ k j) :
    nominalVar σ2 k < σ2 / L ∧ σ2 / L ≤ trueVar σ2 k := by
  refine ⟨?_, trueVar_ge_lineage_bound σ2 hσ.le k hk hL⟩
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  -- the head count strictly exceeds the lineage count
  have hnat : L + 1 ≤ ∑ i, k i := by
    have hsplit : k j + ∑ i ∈ univ.erase j, k i = ∑ i, k i :=
      Finset.add_sum_erase univ k (mem_univ j)
    have hbound : (univ.erase j).card ≤ ∑ i ∈ univ.erase j, k i := by
      calc (univ.erase j).card
          = ∑ _i ∈ univ.erase j, 1 := by simp
        _ ≤ ∑ i ∈ univ.erase j, k i :=
            Finset.sum_le_sum fun i _ => hk i
    have hcard : (univ.erase j).card = L - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ j)]
      simp
    omega
  have hn : (L : ℝ) < ∑ i, (k i : ℝ) := by
    have h' : ((L + 1 : ℕ) : ℝ) ≤ ((∑ i, k i : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at h'
    linarith
  have hnpos : (0 : ℝ) < ∑ i, (k i : ℝ) := lt_trans hL' hn
  unfold nominalVar
  rw [div_lt_div_iff₀ hnpos hL']
  nlinarith [hn, hσ]

/-! ## The exact effective sample size (referee-hardened form) -/

/-- Effective sample size of the cloned electorate: `n² / ∑ k i ²`. -/
noncomputable def nEff (k : Fin L → ℕ) : ℝ :=
  (∑ i, (k i : ℝ)) ^ 2 / ∑ i, ((k i : ℝ)) ^ 2

/-- The true variance is exactly `σ2 / nEff`: the head-counted electorate has
the precision of `nEff` independent voters, no more. -/
theorem trueVar_eq_nEff (σ2 : ℝ) (k : Fin L → ℕ) :
    trueVar σ2 k = σ2 / nEff k := by
  unfold trueVar nEff headShare
  simp only [div_pow]
  rw [← Finset.sum_div, div_div_eq_mul_div, mul_div_assoc]

/-- Sum of squared clone counts is positive when every lineage is inhabited. -/
theorem sumSq_pos (k : Fin L → ℕ) (hk : ∀ i, 1 ≤ k i) (hL : 0 < L) :
    (0 : ℝ) < ∑ i, ((k i : ℝ)) ^ 2 := by
  have h1 : ∀ i ∈ (univ : Finset (Fin L)), (1 : ℝ) ≤ ((k i : ℝ)) ^ 2 := by
    intro i _
    have hi : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hk i
    nlinarith
  calc (0 : ℝ) < L := by exact_mod_cast hL
    _ = ∑ _i : Fin L, (1 : ℝ) := by simp
    _ ≤ ∑ i, ((k i : ℝ)) ^ 2 := Finset.sum_le_sum h1

/-- **The effective sample never exceeds the lineage count** — and that is an
upper bound, not an identity: equality needs balanced replication. -/
theorem nEff_le_lineages (k : Fin L → ℕ) (hk : ∀ i, 1 ≤ k i) (hL : 0 < L) :
    nEff k ≤ L := by
  have hsq := sumSq_pos k hk hL
  have hCS : (∑ i, (k i : ℝ)) ^ 2 ≤
      (∑ i, ((k i : ℝ)) ^ 2) * (L : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin L))
      (fun i => (k i : ℝ)) (fun _ => 1)
    simpa using h
  unfold nEff
  rw [div_le_iff₀ hsq]
  nlinarith [hCS]

/-- **Unbalanced replication is strictly worse than the lineage bound.**  Two
lineages with clone counts (99, 1): one hundred heads, two lineages, but an
effective sample of `10000 / 9802 < 2` — barely more than one independent
voter. -/
theorem nEff_unbalanced_lt_lineages :
    nEff (![99, 1] : Fin 2 → ℕ) < 2 := by
  unfold nEff
  simp [Fin.sum_univ_two]
  norm_num

end JuryInversion
end SEKernel
