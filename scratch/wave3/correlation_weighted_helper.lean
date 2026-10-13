import SEKernel.CorrelatedAnswers

namespace SEKernel.CorrelatedAnswers
open FiniteProbability
open scoped BigOperators Classical
noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- Finite covariance is bilinear under deterministic scaling. -/
theorem covariance_const_mul (L : Law Ω) (a b : ℝ) (X Y : Ω → ℝ) :
    L.covariance (fun ω => a*X ω) (fun ω => b*Y ω)=a*b*L.covariance X Y := by
  unfold Law.covariance
  simp only [L.expect_const_mul]
  calc
    _ = L.expect (fun ω => (a*b)*((X ω-L.expect X)*(Y ω-L.expect Y))) := by
      congr 1
      funext ω
      ring
    _ = _ := L.expect_const_mul (a*b) _

/-- Actual variance of a weighted sum, with each unordered pair counted once. -/
theorem weighted_variance_upper_triangle {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (w : Fin n → ℝ) :
    L.variance (fun ω => ∑ i, w i*X i ω)=
      (∑ i, (w i)^2*L.variance (X i))+
        2*(∑ i, ∑ j, if i<j then w i*w j*L.covariance (X i) (X j) else 0) := by
  let Y := fun i ω => w i*X i ω
  have hsplit : (∑ i, ∑ j, L.covariance (Y i) (Y j)) =
      (∑ i, L.covariance (Y i) (Y i))+
        (∑ i, ∑ j, if i=j then 0 else L.covariance (Y i) (Y j)) := by
    have hpoint (i j : Fin n) : L.covariance (Y i) (Y j)=
        (if i=j then L.covariance (Y i) (Y i) else 0)+
          (if i=j then 0 else L.covariance (Y i) (Y j)) := by
      by_cases h : i=j <;> simp [h]
    calc
      _ = ∑ i, ∑ j, ((if i=j then L.covariance (Y i) (Y i) else 0)+
          (if i=j then 0 else L.covariance (Y i) (Y j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hpoint i j
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',
        Finset.sum_ite_eq,Finset.mem_univ,if_true]
  change L.variance (fun ω => ∑ i, Y i ω)=_
  rw [variance_sum_covariance,hsplit,covariance_off_diagonal]
  simp only [Y,covariance_self,Law.variance_const_mul,covariance_const_mul]

/-- For normalized weights this is the reciprocal variance-effective sample size. -/
def weightedCorrelationBracket {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (w : Fin n → ℝ) : ℝ :=
  (∑ i, (w i)^2)+2*(∑ i, ∑ j,
    if i<j then w i*w j*(L.covariance (X i) (X j)/(p*(1-p))) else 0)

/-- Normalized deterministic weights preserve the common Bernoulli mean. -/
theorem normalized_weighted_mean {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (w : Fin n → ℝ)
    (hsum : ∑ i, w i=1) (hm : ∀ i, L.expect (X i)=p) :
    L.expect (fun ω => ∑ i, w i*X i ω)=p := by
  rw [L.expect_sum]
  simp_rw [L.expect_const_mul,hm]
  rw [← Finset.sum_mul,hsum,one_mul]

/-- Exact Bernoulli weighted-correlation variance; independence is not assumed. -/
theorem weighted_correlated_variance {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hp : 0<p) (hp' : p<1)
    (hX : ∀ i ω, X i ω=0 ∨ X i ω=1) (hm : ∀ i, L.expect (X i)=p)
    (w : Fin n → ℝ) :
    L.variance (fun ω => ∑ i, w i*X i ω)=
      p*(1-p)*weightedCorrelationBracket L X p w := by
  rw [weighted_variance_upper_triangle]
  simp_rw [binary_variance L _ (hX _) p (hm _)]
  have hdiag : (∑ i, (w i)^2*(p*(1-p)))=p*(1-p)*(∑ i, (w i)^2) := by
    rw [← Finset.sum_mul]
    ring
  have hoff : (∑ i, ∑ j, if i<j then w i*w j*L.covariance (X i) (X j) else 0)=
      p*(1-p)*(∑ i, ∑ j,
        if i<j then w i*w j*(L.covariance (X i) (X j)/(p*(1-p))) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> field_simp [ne_of_gt hp,ne_of_gt (sub_pos.mpr hp')] <;> ring
  rw [hdiag,hoff]
  unfold weightedCorrelationBracket
  ring

/-- This reciprocal has a variance interpretation only for a positive bracket. -/
def weightedEffectiveSize {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (w : Fin n → ℝ) : ℝ :=
  1/weightedCorrelationBracket L X p w

/-- A normalized weighted average has variance p(1-p)/effective size. The
nonnegative, sum-one weights and the positive bracket are explicit. -/
theorem weighted_effective_identity {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hp : 0<p) (hp' : p<1)
    (hX : ∀ i ω, X i ω=0 ∨ X i ω=1) (hm : ∀ i, L.expect (X i)=p)
    (w : Fin n → ℝ) (hw : ∀ i, 0≤w i) (hsum : ∑ i, w i=1)
    (hbr : 0<weightedCorrelationBracket L X p w) :
    L.variance (fun ω => ∑ i, w i*X i ω)=p*(1-p)/weightedEffectiveSize L X p w := by
  rw [weighted_correlated_variance L X p hp hp' hX hm]
  unfold weightedEffectiveSize
  field_simp

end
end SEKernel.CorrelatedAnswers
