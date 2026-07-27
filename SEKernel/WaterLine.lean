/-
SEKernel / WaterLine.lean
Elementary algebraic certificates for the water-line theorems in
"The Water-Line Geometry of Congested Portfolio Choice".

This file formalizes the corrected Lean-ready appendix of the paper:
* T1: the exact KKT sum-of-squares identity and its sufficiency implication;
* T2: the explicit two-type barbell coefficients, Cramer solution, constant
  deployments, affine multipliers, and inactive-gap threshold;
* T4: the symmetric Cournot markup identity and its single-principal factor 2;
* T4/W5: the strict pseudo-gradient monotonicity identity and strictness.

Multiplier uniqueness is deliberately absent: the paper's condition (MU) is
needed for that statement.  The false componentwise W4 comparison is also
deliberately absent.

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace WaterLine

open Finset
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## T1 — exact water-line KKT certificates -/

/-- Quadratic water-line payoff from T1. -/
def payoff (c b x : Fin n → ℝ) (B κ : ℝ) : ℝ :=
  ∑ i, (b i * x i - (κ / B) * c i * (x i) ^ 2)

/-- Untruncated normalized return gap. -/
def rawGap (c ℓ b : Fin n → ℝ) (μ lam : ℝ) (i : Fin n) : ℝ :=
  b i / c i - μ - lam * (ℓ i / c i)

/-- Positive part of the normalized return gap. -/
def positiveGap (c ℓ b : Fin n → ℝ) (μ lam : ℝ) (i : Fin n) : ℝ :=
  max (rawGap c ℓ b μ lam i) 0

/-- Nonnegativity slack paired with `positiveGap`. -/
def kktSlack (c ℓ b : Fin n → ℝ) (μ lam : ℝ) (i : Fin n) : ℝ :=
  c i * max (-(rawGap c ℓ b μ lam i)) 0

/-- Water-line allocation associated with resource multipliers `μ, λ`. -/
def waterAllocation (c ℓ b : Fin n → ℝ) (B κ μ lam : ℝ) (i : Fin n) : ℝ :=
  (B / (2 * κ)) * positiveGap c ℓ b μ lam i

/-- **T1 scalar certificate.** The positive gap and nonnegativity slack are
nonnegative and complementary, and the water-line formula satisfies the exact
stationarity identity from the paper's Lean-ready appendix. -/
theorem waterLine_scalar_certificates
    (c ℓ b : Fin n → ℝ) (B κ μ lam : ℝ)
    (hc : ∀ i, 0 < c i) (hB : 0 < B) (hκ : 0 < κ) (i : Fin n) :
    0 ≤ positiveGap c ℓ b μ lam i ∧
      0 ≤ kktSlack c ℓ b μ lam i ∧
      kktSlack c ℓ b μ lam i * waterAllocation c ℓ b B κ μ lam i = 0 ∧
      b i - (2 * κ * c i / B) * waterAllocation c ℓ b B κ μ lam i =
        μ * c i + lam * ℓ i - kktSlack c ℓ b μ lam i := by
  have hci : c i ≠ 0 := ne_of_gt (hc i)
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  by_cases hr : 0 ≤ rawGap c ℓ b μ lam i
  · have hneg : -(rawGap c ℓ b μ lam i) ≤ 0 := neg_nonpos.mpr hr
    refine ⟨le_max_right _ _, ?_, ?_, ?_⟩
    · simp only [kktSlack, max_eq_right hneg, mul_zero, le_refl]
    · simp only [kktSlack, max_eq_right hneg, mul_zero, zero_mul]
    · simp only [waterAllocation, positiveGap, kktSlack, max_eq_left hr,
        max_eq_right hneg, mul_zero, sub_zero]
      unfold rawGap
      field_simp [hci, hB0, hκ0]
      ring
  · have hr' : rawGap c ℓ b μ lam i < 0 := lt_of_not_ge hr
    have hrle : rawGap c ℓ b μ lam i ≤ 0 := hr'.le
    have hneg : 0 ≤ -(rawGap c ℓ b μ lam i) := neg_nonneg.mpr hrle
    refine ⟨le_max_right _ _, ?_, ?_, ?_⟩
    · exact mul_nonneg (hc i).le (le_max_right _ _)
    · simp only [waterAllocation, positiveGap, max_eq_right hrle, mul_zero]
    · simp only [waterAllocation, positiveGap, kktSlack, max_eq_right hrle,
        max_eq_left hneg, mul_zero, sub_zero]
      unfold rawGap
      field_simp [hci]
      ring

/-- **T1 exact sum-of-squares identity.** Under complementary slackness, the
payoff difference from the water-line allocation to any comparison allocation
is exactly the sum of the quadratic distance, nonnegativity-slack payment, and
the two resource-slack payments in equation (LeanT1). -/
theorem waterLine_sum_of_squares
    (c ℓ b y : Fin n → ℝ) (B Q κ μ lam : ℝ)
    (hc : ∀ i, 0 < c i) (hB : 0 < B) (hκ : 0 < κ)
    (hμcomp :
      μ * (B - ∑ i, c i * waterAllocation c ℓ b B κ μ lam i) = 0)
    (hlamcomp :
      lam * (Q - ∑ i, ℓ i * waterAllocation c ℓ b B κ μ lam i) = 0) :
    payoff c b (waterAllocation c ℓ b B κ μ lam) B κ - payoff c b y B κ =
      (κ / B) *
          ∑ i, c i * (y i - waterAllocation c ℓ b B κ μ lam i) ^ 2 +
        ∑ i, kktSlack c ℓ b μ lam i * y i +
        μ * (B - ∑ i, c i * y i) +
        lam * (Q - ∑ i, ℓ i * y i) := by
  let x : Fin n → ℝ := waterAllocation c ℓ b B κ μ lam
  let s : Fin n → ℝ := kktSlack c ℓ b μ lam
  have hcert (i : Fin n) :=
    waterLine_scalar_certificates c ℓ b B κ μ lam hc hB hκ i
  have hsx (i : Fin n) : s i * x i = 0 := by
    exact (hcert i).2.2.1
  have hstat (i : Fin n) :
      b i - (2 * κ * c i / B) * x i =
        μ * c i + lam * ℓ i - s i := by
    exact (hcert i).2.2.2
  have hpoint (i : Fin n) :
      (b i * x i - (κ / B) * c i * (x i) ^ 2) -
          (b i * y i - (κ / B) * c i * (y i) ^ 2) =
        (κ / B) * c i * (y i - x i) ^ 2 +
          s i * y i +
          μ * c i * (x i - y i) +
          lam * ℓ i * (x i - y i) := by
    have hb :
        b i =
          (2 * κ * c i / B) * x i +
            μ * c i + lam * ℓ i - s i := by
      linarith [hstat i]
    rw [hb]
    linear_combination -(hsx i)
  have hsquare :
      ∑ i, (κ / B) * c i * (y i - x i) ^ 2 =
        (κ / B) * ∑ i, c i * (y i - x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmu :
      ∑ i, μ * c i * (x i - y i) =
        μ * ((∑ i, c i * x i) - ∑ i, c i * y i) := by
    calc
      ∑ i, μ * c i * (x i - y i) =
          ∑ i, (μ * (c i * x i) - μ * (c i * y i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i, μ * (c i * x i)) - ∑ i, μ * (c i * y i) := by
            rw [Finset.sum_sub_distrib]
      _ = μ * ((∑ i, c i * x i) - ∑ i, c i * y i) := by
            rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  have hlambda :
      ∑ i, lam * ℓ i * (x i - y i) =
        lam * ((∑ i, ℓ i * x i) - ∑ i, ℓ i * y i) := by
    calc
      ∑ i, lam * ℓ i * (x i - y i) =
          ∑ i, (lam * (ℓ i * x i) - lam * (ℓ i * y i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i, lam * (ℓ i * x i)) - ∑ i, lam * (ℓ i * y i) := by
            rw [Finset.sum_sub_distrib]
      _ = lam * ((∑ i, ℓ i * x i) - ∑ i, ℓ i * y i) := by
            rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  have hmu_budget :
      μ * ((∑ i, c i * x i) - ∑ i, c i * y i) =
        μ * (B - ∑ i, c i * y i) := by
    have hμcomp' : μ * (B - ∑ i, c i * x i) = 0 := by
      simpa [x] using hμcomp
    calc
      μ * ((∑ i, c i * x i) - ∑ i, c i * y i) =
          μ * (B - ∑ i, c i * y i) -
            μ * (B - ∑ i, c i * x i) := by ring
      _ = μ * (B - ∑ i, c i * y i) := by rw [hμcomp']; ring
  have hlambda_budget :
      lam * ((∑ i, ℓ i * x i) - ∑ i, ℓ i * y i) =
        lam * (Q - ∑ i, ℓ i * y i) := by
    have hlamcomp' : lam * (Q - ∑ i, ℓ i * x i) = 0 := by
      simpa [x] using hlamcomp
    calc
      lam * ((∑ i, ℓ i * x i) - ∑ i, ℓ i * y i) =
          lam * (Q - ∑ i, ℓ i * y i) -
            lam * (Q - ∑ i, ℓ i * x i) := by ring
      _ = lam * (Q - ∑ i, ℓ i * y i) := by rw [hlamcomp']; ring
  unfold payoff
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ i,
        ((b i * x i - (κ / B) * c i * (x i) ^ 2) -
          (b i * y i - (κ / B) * c i * (y i) ^ 2)) =
        ∑ i,
          ((κ / B) * c i * (y i - x i) ^ 2 +
            s i * y i +
            μ * c i * (x i - y i) +
            lam * ℓ i * (x i - y i)) := by
              apply Finset.sum_congr rfl
              intro i _
              exact hpoint i
    _ = (κ / B) * ∑ i, c i * (y i - x i) ^ 2 +
          ∑ i, s i * y i +
          μ * (B - ∑ i, c i * y i) +
          lam * (Q - ∑ i, ℓ i * y i) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_add_distrib, hsquare, hmu, hlambda, hmu_budget,
              hlambda_budget]
    _ = (κ / B) *
          ∑ i, c i * (y i - waterAllocation c ℓ b B κ μ lam i) ^ 2 +
        ∑ i, kktSlack c ℓ b μ lam i * y i +
        μ * (B - ∑ i, c i * y i) +
        lam * (Q - ∑ i, ℓ i * y i) := by rfl

/-- **T1 water-line sufficiency.** Any nonnegative comparison allocation
satisfying both resource inequalities has no larger payoff than a water-line
allocation satisfying complementary slackness.  This is the verification
direction used by the paper and requires no multiplier-uniqueness claim. -/
theorem waterLine_kkt_sufficient
    (c ℓ b y : Fin n → ℝ) (B Q κ μ lam : ℝ)
    (hc : ∀ i, 0 < c i) (_hℓ : ∀ i, 0 ≤ ℓ i)
    (hB : 0 < B) (_hQ : 0 < Q) (hκ : 0 < κ)
    (hμ : 0 ≤ μ) (hlam : 0 ≤ lam)
    (_hxBudget : ∑ i, c i * waterAllocation c ℓ b B κ μ lam i ≤ B)
    (_hxCapacity : ∑ i, ℓ i * waterAllocation c ℓ b B κ μ lam i ≤ Q)
    (hμcomp :
      μ * (B - ∑ i, c i * waterAllocation c ℓ b B κ μ lam i) = 0)
    (hlamcomp :
      lam * (Q - ∑ i, ℓ i * waterAllocation c ℓ b B κ μ lam i) = 0)
    (hy : ∀ i, 0 ≤ y i)
    (hyBudget : ∑ i, c i * y i ≤ B)
    (hyCapacity : ∑ i, ℓ i * y i ≤ Q) :
    payoff c b y B κ ≤
      payoff c b (waterAllocation c ℓ b B κ μ lam) B κ := by
  have hid :=
    waterLine_sum_of_squares c ℓ b y B Q κ μ lam hc hB hκ hμcomp hlamcomp
  have hsquare :
      0 ≤ (κ / B) *
        ∑ i, c i * (y i - waterAllocation c ℓ b B κ μ lam i) ^ 2 := by
    exact mul_nonneg (div_nonneg hκ.le hB.le)
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hc i).le (sq_nonneg _))
  have hslack :
      0 ≤ ∑ i, kktSlack c ℓ b μ lam i * y i := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg
      (waterLine_scalar_certificates c ℓ b B κ μ lam hc hB hκ i).2.1
      (hy i)
  have hbudget : 0 ≤ μ * (B - ∑ i, c i * y i) :=
    mul_nonneg hμ (sub_nonneg.mpr hyBudget)
  have hcapacity : 0 ≤ lam * (Q - ∑ i, ℓ i * y i) :=
    mul_nonneg hlam (sub_nonneg.mpr hyCapacity)
  linarith

/-! ## T2 — explicit two-type barbell cell -/

/-- Lower-coordinate coefficient `d_i` from T2. -/
def pairDi (ci ai aj abar : ℝ) : ℝ :=
  2 * (aj - abar) / (ci * (aj - ai))

/-- Upper-coordinate coefficient `d_j` from T2. -/
def pairDj (cj ai aj abar : ℝ) : ℝ :=
  2 * (abar - ai) / (cj * (aj - ai))

/-- Slope `v` of the affine gap derivative through `d_i,d_j`. -/
def pairV (ci cj ai aj abar : ℝ) : ℝ :=
  (pairDj cj ai aj abar - pairDi ci ai aj abar) / (aj - ai)

/-- Intercept `u` of the affine gap derivative through `d_i,d_j`. -/
def pairU (ci cj ai aj abar : ℝ) : ℝ :=
  pairDi ci ai aj abar - ai * pairV ci cj ai aj abar

/-- **T2 coefficient certificate.** The explicit barbell coefficients are
positive, satisfy both binding equations, and the affine function `u + v a`
interpolates them at the two active coordinates. -/
theorem barbell_coefficients
    (ci cj ai aj abar : ℝ)
    (hci : 0 < ci) (hcj : 0 < cj) (hai : ai < abar) (haj : abar < aj) :
    0 < pairDi ci ai aj abar ∧
      0 < pairDj cj ai aj abar ∧
      ci * pairDi ci ai aj abar + cj * pairDj cj ai aj abar = 2 ∧
      ci * ai * pairDi ci ai aj abar +
          cj * aj * pairDj cj ai aj abar = 2 * abar ∧
      pairU ci cj ai aj abar + pairV ci cj ai aj abar * ai =
        pairDi ci ai aj abar ∧
      pairU ci cj ai aj abar + pairV ci cj ai aj abar * aj =
        pairDj cj ai aj abar := by
  have hgap : 0 < aj - ai := sub_pos.mpr (lt_trans hai haj)
  have hdeni : 0 < ci * (aj - ai) := mul_pos hci hgap
  have hdenj : 0 < cj * (aj - ai) := mul_pos hcj hgap
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos (mul_pos (by norm_num) (sub_pos.mpr haj)) hdeni
  · exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hai)) hdenj
  · unfold pairDi pairDj
    field_simp [ne_of_gt hci, ne_of_gt hcj, ne_of_gt hgap]
    ring
  · unfold pairDi pairDj
    field_simp [ne_of_gt hci, ne_of_gt hcj, ne_of_gt hgap]
    ring
  · unfold pairU pairV pairDi pairDj
    field_simp [ne_of_gt hci, ne_of_gt hcj, ne_of_gt hgap]
    ring
  · unfold pairU pairV pairDi pairDj
    field_simp [ne_of_gt hci, ne_of_gt hcj, ne_of_gt hgap]
    ring

/-- **T2 two-by-two Cramer certificate.** The two binding equations uniquely
force the active normalized gaps to be `κ d_i` and `κ d_j`. -/
theorem barbell_gap_solution
    (ci cj ai aj abar κ gi gj : ℝ)
    (hci : 0 < ci) (hcj : 0 < cj) (hai : ai < abar) (haj : abar < aj)
    (hbudget : ci * gi + cj * gj = 2 * κ)
    (hcapacity : ci * ai * gi + cj * aj * gj = 2 * κ * abar) :
    gi = κ * pairDi ci ai aj abar ∧
      gj = κ * pairDj cj ai aj abar := by
  have hgap : 0 < aj - ai := sub_pos.mpr (lt_trans hai haj)
  have hdeni : ci * (aj - ai) ≠ 0 :=
    mul_ne_zero (ne_of_gt hci) (ne_of_gt hgap)
  have hdenj : cj * (aj - ai) ≠ 0 :=
    mul_ne_zero (ne_of_gt hcj) (ne_of_gt hgap)
  have hgi :
      ci * (aj - ai) * gi = 2 * κ * (aj - abar) := by
    calc
      ci * (aj - ai) * gi =
          aj * (ci * gi + cj * gj) -
            (ci * ai * gi + cj * aj * gj) := by ring
      _ = aj * (2 * κ) - 2 * κ * abar := by rw [hbudget, hcapacity]
      _ = 2 * κ * (aj - abar) := by ring
  have hgj :
      cj * (aj - ai) * gj = 2 * κ * (abar - ai) := by
    calc
      cj * (aj - ai) * gj =
          (ci * ai * gi + cj * aj * gj) -
            ai * (ci * gi + cj * gj) := by ring
      _ = 2 * κ * abar - ai * (2 * κ) := by rw [hbudget, hcapacity]
      _ = 2 * κ * (abar - ai) := by ring
  constructor
  · calc
      gi = (2 * κ * (aj - abar)) / (ci * (aj - ai)) := by
        apply (eq_div_iff hdeni).2
        nlinarith [hgi]
      _ = κ * pairDi ci ai aj abar := by
        unfold pairDi
        ring
  · calc
      gj = (2 * κ * (abar - ai)) / (cj * (aj - ai)) := by
        apply (eq_div_iff hdenj).2
        nlinarith [hgj]
      _ = κ * pairDj cj ai aj abar := by
        unfold pairDj
        ring

/-- **T2 constant-deployment certificate.** Deployments `B d_i/2` and
`B d_j/2` bind the budget and capacity resources exactly. -/
theorem barbell_constant_deployment_binding
    (ci cj ai aj abar B : ℝ)
    (hci : 0 < ci) (hcj : 0 < cj) (hai : ai < abar) (haj : abar < aj) :
    ci * (B * pairDi ci ai aj abar / 2) +
          cj * (B * pairDj cj ai aj abar / 2) = B ∧
      ci * ai * (B * pairDi ci ai aj abar / 2) +
          cj * aj * (B * pairDj cj ai aj abar / 2) = B * abar := by
  have hcert := barbell_coefficients ci cj ai aj abar hci hcj hai haj
  constructor
  · calc
      ci * (B * pairDi ci ai aj abar / 2) +
          cj * (B * pairDj cj ai aj abar / 2) =
          (B / 2) *
            (ci * pairDi ci ai aj abar + cj * pairDj cj ai aj abar) := by ring
      _ = B := by rw [hcert.2.2.1]; ring
  · calc
      ci * ai * (B * pairDi ci ai aj abar / 2) +
          cj * aj * (B * pairDj cj ai aj abar / 2) =
          (B / 2) *
            (ci * ai * pairDi ci ai aj abar +
              cj * aj * pairDj cj ai aj abar) := by ring
      _ = B * abar := by rw [hcert.2.2.2.1]; ring

/-- **T2 active-gap certificate.** The affine multiplier path
`μκ = μ* - κu`, `λκ = λ* - κv` produces the exact positive active gaps
`κd_i, κd_j`. -/
theorem barbell_active_gaps
    (ci cj ai aj abar κ mustar lamstar bti btj : ℝ)
    (hci : 0 < ci) (hcj : 0 < cj) (hai : ai < abar) (haj : abar < aj)
    (hκ : 0 < κ)
    (hbti : bti = mustar + lamstar * ai)
    (hbtj : btj = mustar + lamstar * aj) :
    bti - (mustar - κ * pairU ci cj ai aj abar) -
          (lamstar - κ * pairV ci cj ai aj abar) * ai =
        κ * pairDi ci ai aj abar ∧
      0 < κ * pairDi ci ai aj abar ∧
      btj - (mustar - κ * pairU ci cj ai aj abar) -
          (lamstar - κ * pairV ci cj ai aj abar) * aj =
        κ * pairDj cj ai aj abar ∧
      0 < κ * pairDj cj ai aj abar := by
  have hcert := barbell_coefficients ci cj ai aj abar hci hcj hai haj
  refine ⟨?_, mul_pos hκ hcert.1, ?_, mul_pos hκ hcert.2.1⟩
  · rw [hbti, ← hcert.2.2.2.2.1]
    ring
  · rw [hbtj, ← hcert.2.2.2.2.2]
    ring

/-- **T2 inactive-gap identity.** Along the affine multiplier path, an
inactive type's reduced gap is exactly `-ρ + κ (u + v a_k)`. -/
theorem barbell_inactive_gap_identity
    (ak btk mustar lamstar ρ κ u v : ℝ)
    (hbt : btk = mustar + lamstar * ak - ρ) :
    btk - (mustar - κ * u) - (lamstar - κ * v) * ak =
      -ρ + κ * (u + v * ak) := by
  rw [hbt]
  ring

/-- **T2 inactive threshold.** If `h_k ≤ 0`, every positive `κ` keeps the
inactive gap strict; if `h_k > 0`, the exact condition `κ < ρ/h_k` does so. -/
theorem barbell_inactive_gap_strict
    (ak btk mustar lamstar ρ κ u v : ℝ)
    (hbt : btk = mustar + lamstar * ak - ρ)
    (hρ : 0 < ρ) (hκ : 0 < κ)
    (hthreshold :
      u + v * ak ≤ 0 ∨
        (0 < u + v * ak ∧ κ < ρ / (u + v * ak))) :
    btk - (mustar - κ * u) - (lamstar - κ * v) * ak < 0 := by
  rw [barbell_inactive_gap_identity ak btk mustar lamstar ρ κ u v hbt]
  rcases hthreshold with hnonpos | ⟨hpos, hbelow⟩
  · have hprod : κ * (u + v * ak) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hκ.le hnonpos
    linarith
  · have hprod : κ * (u + v * ak) < ρ :=
      (lt_div_iff₀ hpos).mp hbelow
    linarith

/-- **T2 finite inactive-family certificate.** The pointwise threshold
conditions from the Lean-ready appendix imply strict exclusion of every type
outside the active pair.  This is the quantified `Fin n` form used to preserve
the support `{i,j}` inside the barbell cell. -/
theorem barbell_all_inactive_gaps
    (a bt ρ : Fin n → ℝ) (i j : Fin n)
    (mustar lamstar κ u v : ℝ) (hκ : 0 < κ)
    (hbt :
      ∀ k, k ≠ i → k ≠ j →
        bt k = mustar + lamstar * a k - ρ k)
    (hρ : ∀ k, k ≠ i → k ≠ j → 0 < ρ k)
    (hthreshold :
      ∀ k, k ≠ i → k ≠ j →
        u + v * a k ≤ 0 ∨
          (0 < u + v * a k ∧ κ < ρ k / (u + v * a k))) :
    ∀ k, k ≠ i → k ≠ j →
      bt k - (mustar - κ * u) - (lamstar - κ * v) * a k < 0 := by
  intro k hki hkj
  exact barbell_inactive_gap_strict
    (a k) (bt k) mustar lamstar (ρ k) κ u v
    (hbt k hki hkj) (hρ k hki hkj) hκ (hthreshold k hki hkj)

/-- **T2 multiplier threshold.** A positive affine multiplier remains positive
below its exact ratio threshold. -/
theorem affine_multiplier_positive_below_threshold
    (multiplier κ slope : ℝ)
    (_hmultiplier : 0 < multiplier) (hslope : 0 < slope)
    (hbelow : κ < multiplier / slope) :
    0 < multiplier - κ * slope := by
  have := (lt_div_iff₀ hslope).mp hbelow
  linarith

/-! ## T4 — symmetric Cournot markup -/

/-- **T4 Cournot markup identity.** At a symmetric `m`-principal profile, the
aggregate and own-deployment congestion terms combine into the exact factor
`1 + 1/m`. -/
theorem cournot_markup_identity
    (m : ℕ) (hm : 1 ≤ m) (b κ c N Btot : ℝ) (hBtot : Btot ≠ 0) :
    b - κ * (c * N / Btot) -
        κ * c * (N / (m : ℝ)) / Btot =
      b - κ * (1 + 1 / (m : ℝ)) * c * N / Btot := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm))
  field_simp [hBtot, hm0]
  ring

/-- **T4 single-principal specialization.** For `m = 1`, the symmetric
Cournot markup is the factor-2 planner water line. -/
theorem cournot_markup_single_principal
    (b κ c N Btot : ℝ) (hBtot : Btot ≠ 0) :
    b - κ * (c * N / Btot) - κ * c * N / Btot =
      b - 2 * κ * c * N / Btot := by
  field_simp [hBtot]
  ring

/-! ## T4/W5 — strict pseudo-gradient monotonicity -/

/-- Aggregate deployment of type `i` across all principals. -/
def aggregate {m : ℕ} (p : Fin m → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ α, p α i

/-- Principal `α`'s own-payoff pseudo-gradient at type `i`. -/
def pseudoGradient {m : ℕ}
    (c b : Fin n → ℝ) (Btot κ : ℝ)
    (p : Fin m → Fin n → ℝ) (α : Fin m) (i : Fin n) : ℝ :=
  b i - (κ / Btot) * c i * (aggregate p i + p α i)

/-- **T4/W5 strict pseudo-gradient identity.** The pairing of a profile
difference with its pseudo-gradient difference is exactly the negative
sum-of-squares certificate in equation (LeanT4mono). -/
theorem pseudoGradient_monotonicity_identity
    {m : ℕ} (c b : Fin n → ℝ) (Btot κ : ℝ)
    (p q : Fin m → Fin n → ℝ) :
    ∑ α, ∑ i,
        (p α i - q α i) *
          (pseudoGradient c b Btot κ p α i -
            pseudoGradient c b Btot κ q α i) =
      -(κ / Btot) *
        ∑ i, c i *
          (((∑ α, (p α i - q α i)) ^ 2) +
            ∑ α, (p α i - q α i) ^ 2) := by
  classical
  let d : Fin m → Fin n → ℝ := fun α i => p α i - q α i
  let D : Fin n → ℝ := fun i => ∑ α, d α i
  have haggregate (i : Fin n) :
      aggregate p i - aggregate q i = D i := by
    simp [aggregate, D, d, Finset.sum_sub_distrib]
  have hgradient (α : Fin m) (i : Fin n) :
      pseudoGradient c b Btot κ p α i -
          pseudoGradient c b Btot κ q α i =
        -(κ / Btot) * c i * (D i + d α i) := by
    calc
      pseudoGradient c b Btot κ p α i -
          pseudoGradient c b Btot κ q α i =
        -(κ / Btot) * c i *
          ((aggregate p i - aggregate q i) + (p α i - q α i)) := by
            unfold pseudoGradient
            ring
      _ = -(κ / Btot) * c i * (D i + d α i) := by
            rw [haggregate]
  have hquadratic (i : Fin n) :
      ∑ α, d α i * (D i + d α i) =
        (D i) ^ 2 + ∑ α, (d α i) ^ 2 := by
    calc
      ∑ α, d α i * (D i + d α i) =
          ∑ α, (d α i * D i + (d α i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro α _
            ring
      _ = (∑ α, d α i) * D i + ∑ α, (d α i) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = (D i) ^ 2 + ∑ α, (d α i) ^ 2 := by
            simp [D]
            ring
  calc
    ∑ α, ∑ i,
        (p α i - q α i) *
          (pseudoGradient c b Btot κ p α i -
            pseudoGradient c b Btot κ q α i) =
      ∑ i, ∑ α,
        d α i *
          (pseudoGradient c b Btot κ p α i -
            pseudoGradient c b Btot κ q α i) := by
              rw [Finset.sum_comm]
    _ = ∑ i, (-(κ / Btot) * c i) *
          ((D i) ^ 2 + ∑ α, (d α i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← hquadratic i, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro α _
            rw [hgradient]
            ring
    _ = -(κ / Btot) *
        ∑ i, c i *
          ((D i) ^ 2 + ∑ α, (d α i) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = -(κ / Btot) *
        ∑ i, c i *
          (((∑ α, (p α i - q α i)) ^ 2) +
            ∑ α, (p α i - q α i) ^ 2) := by
              rfl

/-- **T4/W5 strictness.** With positive congestion, budget, and type weights,
the pseudo-gradient pairing is strictly negative for distinct profiles.  This
is the algebraic engine used by T4 to rule out asymmetric equilibria. -/
theorem pseudoGradient_strict_monotonicity
    {m : ℕ} (c b : Fin n → ℝ) (Btot κ : ℝ)
    (p q : Fin m → Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (hBtot : 0 < Btot) (hκ : 0 < κ)
    (hpq : p ≠ q) :
    ∑ α, ∑ i,
        (p α i - q α i) *
          (pseudoGradient c b Btot κ p α i -
            pseudoGradient c b Btot κ q α i) < 0 := by
  classical
  have hexists : ∃ α i, p α i ≠ q α i := by
    by_contra h
    push_neg at h
    apply hpq
    funext α
    funext i
    exact h α i
  rcases hexists with ⟨α, i, hne⟩
  have hsquarepos : 0 < (p α i - q α i) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hinnersum :
      0 < ∑ β, (p β i - q β i) ^ 2 := by
    exact Finset.sum_pos'
      (fun β _ => sq_nonneg (p β i - q β i))
      ⟨α, Finset.mem_univ α, hsquarepos⟩
  have hinner :
      0 <
        (∑ β, (p β i - q β i)) ^ 2 +
          ∑ β, (p β i - q β i) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) hinnersum
  have hsum :
      0 <
        ∑ j, c j *
          (((∑ β, (p β j - q β j)) ^ 2) +
            ∑ β, (p β j - q β j) ^ 2) := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hc j).le
        (add_nonneg (sq_nonneg _)
          (Finset.sum_nonneg fun β _ => sq_nonneg _))
    · exact ⟨i, Finset.mem_univ i, mul_pos (hc i) hinner⟩
  rw [pseudoGradient_monotonicity_identity c b Btot κ p q]
  have hfactor : 0 < κ / Btot := div_pos hκ hBtot
  nlinarith [mul_pos hfactor hsum]

end

end WaterLine
end SEKernel
