/-
SEKernel / SpawnConflict.lean
Elementary ordered-field certificates for the Tier-3 conflict lemmas in
"The Theory of Strategic Evolution".

The results formalized here are the algebraic appendix lemmas W1--W8:
quadratic expansion and separability, user-cost elimination, lane
diagonalization, the Riccati identity, the no-threshold stability certificate,
the `d = 1` collapse, the peace-trigger threshold, and the dissipation bound.

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace SpawnConflict

noncomputable section

/-! ## W1 / A1 — quadratic expansion and separability -/

/-- **W1 / A1 quadratic expansion identity.** This is the expanded form of
the quadratic conflict expression used in the paper. -/
theorem quadratic_expansion_identity
    (x y b : ℝ) (hb : b ≠ 0) :
    1 / 2 + (x - y) / (4 * b) -
          ((x - b) ^ 2 - (y - b) ^ 2) / (8 * b ^ 2) =
      1 / 2 + (x - y) / (2 * b) - (x ^ 2 - y ^ 2) / (8 * b ^ 2) := by
  field_simp [hb]
  ring

/-- One-coordinate quadratic adjustment in the separable form of W1 / A1. -/
def quadraticAdjustment (b z : ℝ) : ℝ :=
  (z - b) / (4 * b) - (z - b) ^ 2 / (8 * b ^ 2)

/-- The quadratic conflict expression `φQ` from W1 / A1. -/
def phiQ (b x y : ℝ) : ℝ :=
  1 / 2 + (x - y) / (4 * b) -
    ((x - b) ^ 2 - (y - b) ^ 2) / (8 * b ^ 2)

/-- **W1 / A1 separability corollary.** The quadratic conflict expression is
the difference of two one-coordinate adjustments. -/
theorem phiQ_separable (b x y : ℝ) :
    phiQ b x y =
      1 / 2 + quadraticAdjustment b x - quadraticAdjustment b y := by
  unfold phiQ quadraticAdjustment
  ring

/-! ## W2 / A2 — user-cost elimination -/

/-- **W2 / A2 user-cost elimination (the T2 engine).** Eliminating the
continuation values gives the paper's exact user-cost equation. -/
theorem userCostElimination
    (δ p V2 V1 z a k χ d n q m ρ : ℝ)
    (hden : 1 - δ * p ≠ 0)
    (hV2 : V2 = p * (-z + δ * V2))
    (hV1 : V1 = a * (k + χ * d * n) + q * (-z + δ * V2))
    (hz : z = k + χ * d * n + m + ρ * n - δ * V1) :
    z =
      k * (1 - δ * a) + m + ρ * n +
        χ * d * n * (1 - δ * a) + δ * q * z / (1 - δ * p) := by
  have hlinear : (1 - δ * p) * (-z + δ * V2) = -z := by
    linear_combination δ * hV2
  have hcontinuation : -z + δ * V2 = -z / (1 - δ * p) := by
    apply (eq_div_iff hden).2
    calc
      (-z + δ * V2) * (1 - δ * p) =
          (1 - δ * p) * (-z + δ * V2) := by ring
      _ = -z := hlinear
  calc
    z = k + χ * d * n + m + ρ * n - δ * V1 := hz
    _ =
        k * (1 - δ * a) + m + ρ * n +
          χ * d * n * (1 - δ * a) + δ * q * z / (1 - δ * p) := by
      rw [hV1, hcontinuation]
      field_simp [hden]
      ring

/-- **W2 / A2 uncoupled corollary.** Setting `q = 0` and `χ = 0` in the T2
engine leaves the affine user cost `k (1 - δ a) + m + ρ n`. -/
theorem userCostElimination_uncoupled
    (δ p V2 V1 z a k m ρ n : ℝ)
    (hden : 1 - δ * p ≠ 0)
    (hV2 : V2 = p * (-z + δ * V2))
    (hV1 : V1 = a * k)
    (hz : z = k + m + ρ * n - δ * V1) :
    z = k * (1 - δ * a) + m + ρ * n := by
  have hV1' :
      V1 = a * (k + (0 : ℝ) * 0 * n) + 0 * (-z + δ * V2) := by
    simpa using hV1
  have hz' :
      z = k + (0 : ℝ) * 0 * n + m + ρ * n - δ * V1 := by
    simpa using hz
  simpa using
    (userCostElimination δ p V2 V1 z a k 0 0 n 0 m ρ
      hden hV2 hV1' hz')

/-- **W2 / A2 Tullock corollary.** Substituting `z = G/(4n)` into the
uncoupled user cost yields the quadratic equation.  The explicit hypothesis
`n ≠ 0` is necessary because division on `ℝ` is totalized at zero. -/
theorem userCostElimination_tullock
    (δ a z k m ρ n G : ℝ)
    (hn : n ≠ 0)
    (hz : z = k * (1 - δ * a) + m + ρ * n)
    (hTullock : z = G / (4 * n)) :
    ρ * n ^ 2 + (k * (1 - δ * a) + m) * n - G / 4 = 0 := by
  have h4n : 4 * n ≠ 0 := mul_ne_zero (by norm_num) hn
  have hcross : z * (4 * n) = G := (eq_div_iff h4n).mp hTullock
  rw [hz] at hcross
  nlinarith [hcross]

/-! ## W3 / A3--A4 — lane diagonalization -/

/-- **W3 / A3 lane diagonalization.** Symmetric and antisymmetric lane
coordinates diagonalize the affine two-lane system. -/
theorem lane_diagonalization
    (x1 x2 c p q n1 n2 : ℝ)
    (hx1 : x1 = c + p * n1 + q * n2)
    (hx2 : x2 = c + q * n1 + p * n2) :
    x1 + x2 = 2 * c + (p + q) * (n1 + n2) ∧
      x1 - x2 = (p - q) * (n1 - n2) := by
  constructor <;> nlinarith [hx1, hx2]

/-- **W3 / A4 lane-equation diagonalization.** Adding and subtracting the two
lane equations produces the symmetric and antisymmetric scalar equations. -/
theorem lane_system_diagonalization
    (A B p q χ a : ℝ)
    (h1 : A * p + B * q + χ * a = 0)
    (h2 : A * q + B * p = 0) :
    (A + B) * (p + q) + χ * a = 0 ∧
      (A - B) * (p - q) + χ * a = 0 := by
  constructor
  · linear_combination h1 + h2
  · linear_combination h1 - h2

/-- **W3 / A4 lane-slope formulas.** When both diagonal coefficients are
nonzero, the symmetric and antisymmetric slopes have the displayed forms. -/
theorem lane_slope_formulas
    (A B p q χ a : ℝ)
    (h1 : A * p + B * q + χ * a = 0)
    (h2 : A * q + B * p = 0)
    (hsum : A + B ≠ 0)
    (hdiff : A - B ≠ 0) :
    p + q = -(χ * a) / (A + B) ∧
      p - q = -(χ * a) / (A - B) := by
  obtain ⟨hplus, hminus⟩ :=
    lane_system_diagonalization A B p q χ a h1 h2
  constructor
  · apply (eq_div_iff hsum).2
    nlinarith [hplus]
  · apply (eq_div_iff hdiff).2
    nlinarith [hminus]

/-! ## W4 / A5 — Riccati polynomial equivalence -/

/-- **W4 / A5 Riccati polynomial equivalence.** Substituting
`D = H + χ + δΠ` turns the fixed-point equation into the paper's quadratic
polynomial, and conversely. -/
theorem riccatiPolynomialEquiv
    (P D H χ δ a : ℝ)
    (hD : D = H + χ + δ * P) :
    P * D = χ * a ^ 2 * (H + δ * P) ↔
      δ * P ^ 2 + (H + χ - δ * χ * a ^ 2) * P -
          χ * a ^ 2 * H = 0 := by
  rw [hD]
  constructor <;> intro h <;> nlinarith [h]

/-! ## W5 / A6 — no-threshold stability certificate -/

/-- **W5 / A6 no-threshold stability certificate (T4B core).** The feedback
ratio is nonnegative, never exceeds `a`, is strictly below one, and is strictly
below `a` whenever `a > 0`. -/
theorem noThresholdStability
    (H χ δ P a D : ℝ)
    (hH : 0 < H) (hχ : 0 ≤ χ) (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (ha : 0 ≤ a) (ha1 : a < 1)
    (hD : D = H + χ + δ * P) :
    D - χ > 0 ∧
      0 ≤ χ * a / D ∧
      χ * a / D ≤ a ∧
      χ * a / D < 1 ∧
      (0 < a → χ * a / D < a) := by
  have hδP : 0 ≤ δ * P := mul_nonneg hδ hP
  have hgap : 0 < D - χ := by
    rw [hD]
    nlinarith
  have hDpos : 0 < D := by
    nlinarith [hχ]
  have hnonneg : 0 ≤ χ * a / D :=
    div_nonneg (mul_nonneg hχ ha) hDpos.le
  have hproduct : 0 ≤ a * (D - χ) :=
    mul_nonneg ha hgap.le
  have hle : χ * a / D ≤ a := by
    apply (div_le_iff₀ hDpos).2
    nlinarith [hproduct]
  have hlt1 : χ * a / D < 1 := lt_of_le_of_lt hle ha1
  refine ⟨hgap, hnonneg, hle, hlt1, ?_⟩
  intro hapos
  have hstrictProduct : 0 < a * (D - χ) :=
    mul_pos hapos hgap
  apply (div_lt_iff₀ hDpos).2
  nlinarith [hstrictProduct]

/-! ## W6 / A7 — the `d = 1` collapse -/

/-- **W6 / A7 dynamic `d = 1` collapse.** If `a = 0`, the nonnegative
Riccati solution is necessarily `Π = 0`. -/
theorem riccatiCollapse
    (a H χ δ P : ℝ)
    (ha : a = 0) (hH : 0 < H)
    (hχ : 0 ≤ χ) (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (hriccati :
      P * (H + χ + δ * P) = χ * a ^ 2 * (H + δ * P)) :
    P = 0 := by
  have hDpos : 0 < H + χ + δ * P := by
    have hδP : 0 ≤ δ * P := mul_nonneg hδ hP
    nlinarith
  have hproduct : P * (H + χ + δ * P) = 0 := by
    simpa [ha] using hriccati
  rcases mul_eq_zero.mp hproduct with hPzero | hDzero
  · exact hPzero
  · exact (ne_of_gt hDpos hDzero).elim

/-- **W6 / A7 static `d = 1` instance.** With zero congestion terms, the
static condition solves to `n = G/(4(k+m))`.  The assumption `G > 0`, standard
in the paper's contest environment, is needed to rule out the totalized
zero-denominator case `G = k + m = 0`. -/
theorem staticCollapse
    (G n k m ρ χ : ℝ)
    (hG : 0 < G) (hn : 0 < n)
    (hρ : ρ = 0) (hχ : χ = 0)
    (hstatic : G / (4 * n) = k + m + (ρ + χ) * n) :
    n = G / (4 * (k + m)) := by
  rw [hρ, hχ] at hstatic
  norm_num at hstatic
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hleft : 0 < G / (4 * n) :=
    div_pos hG (mul_pos (by norm_num) hn)
  have hkmpos : 0 < k + m := by
    nlinarith [hstatic]
  have hden : 4 * (k + m) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hkmpos)
  apply (eq_div_iff hden).2
  have hkm : k + m = G / (4 * n) := by
    nlinarith [hstatic]
  rw [hkm]
  field_simp [hn0]

/-! ## W7 / A8 — peace-trigger threshold -/

/-- **W7 / A8 peace-trigger threshold (T5B core).** The peace payoff dominates
the conflict-plus-continuation payoff exactly when `δ ≥ 2/3`. -/
theorem peaceTriggerThreshold
    (G δ : ℝ) (hG : 0 < G) (_hδ0 : 0 < δ) (hδ1 : δ < 1) :
    G / (2 * (1 - δ)) ≥
        G + δ * G / (4 * (1 - δ)) ↔
      δ ≥ 2 / 3 := by
  have ht : 0 < 1 - δ := by linarith
  have hscale : 0 < 4 * (1 - δ) / G :=
    div_pos (mul_pos (by norm_num) ht) hG
  have hidentity :
      (4 * (1 - δ) / G) *
          (G / (2 * (1 - δ)) -
            (G + δ * G / (4 * (1 - δ)))) =
        3 * δ - 2 := by
    field_simp [ne_of_gt hG, ne_of_gt ht]
    ring
  constructor
  · intro h
    have hdiff :
        0 ≤
          G / (2 * (1 - δ)) -
            (G + δ * G / (4 * (1 - δ))) :=
      sub_nonneg.mpr h
    have hproduct :
        0 ≤
          (4 * (1 - δ) / G) *
            (G / (2 * (1 - δ)) -
              (G + δ * G / (4 * (1 - δ)))) :=
      mul_nonneg hscale.le hdiff
    rw [hidentity] at hproduct
    linarith
  · intro h
    have hrhs : 0 ≤ 3 * δ - 2 := by
      linarith
    have hproduct :
        0 ≤
          (4 * (1 - δ) / G) *
            (G / (2 * (1 - δ)) -
              (G + δ * G / (4 * (1 - δ)))) := by
      rw [hidentity]
      exact hrhs
    have hdiff :
        0 ≤
          G / (2 * (1 - δ)) -
            (G + δ * G / (4 * (1 - δ))) := by
      by_contra hnot
      have hneg :
          G / (2 * (1 - δ)) -
              (G + δ * G / (4 * (1 - δ))) < 0 :=
        lt_of_not_ge hnot
      have hmulneg := mul_neg_of_pos_of_neg hscale hneg
      linarith
    exact sub_nonneg.mp hdiff

/-! ## W8 — dissipation bound -/

/-- **W8 / T6 dissipation-gap identity.** The user-cost gap factors into the
three nonnegative terms that drive the weak and strict dissipation bounds. -/
theorem dissipation_gap_identity
    (k d m δ a c_u : ℝ)
    (ha : a = 1 - d)
    (hcu : c_u = k * (1 - δ * a) + m) :
    c_u - (k * d + m) = k * (1 - d) * (1 - δ) := by
  rw [hcu, ha]
  ring

/-- **W8 / T6 dissipation bound.** Under the paper's nonnegativity and
discount hypotheses, dissipation is at most `G/2`. -/
theorem dissipation_bound
    (k d m δ a c_u G : ℝ)
    (hk : 0 ≤ k) (_hd : 0 ≤ d) (_hm : 0 ≤ m)
    (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha0 : 0 ≤ a) (ha : a = 1 - d)
    (hcu : c_u = k * (1 - δ * a) + m) (hcupos : 0 < c_u)
    (hG : 0 < G) :
    (G / 2) * ((k * d + m) / c_u) ≤ G / 2 := by
  have hgap :
      c_u - (k * d + m) = k * (1 - d) * (1 - δ) :=
    dissipation_gap_identity k d m δ a c_u ha hcu
  have hgapNonneg : 0 ≤ k * (1 - d) * (1 - δ) :=
    mul_nonneg (mul_nonneg hk (by simpa [ha] using ha0))
      (sub_nonneg.mpr hδ1)
  have hcost : k * d + m ≤ c_u := by
    nlinarith [hgap]
  have hratio : (k * d + m) / c_u ≤ 1 :=
    (div_le_one hcupos).2 hcost
  have hGhalf : 0 ≤ G / 2 := by positivity
  simpa using mul_le_mul_of_nonneg_left hratio hGhalf

/-- **W8 / T6 strict dissipation bound.** If `d < 1`, `δ < 1`, and `k > 0`,
the factored gap is positive and dissipation is strictly below `G/2`. -/
theorem dissipation_bound_strict
    (k d m δ a c_u G : ℝ)
    (hk : 0 < k) (_hd : 0 ≤ d) (_hm : 0 ≤ m)
    (hd1 : d < 1) (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (_ha0 : 0 ≤ a) (ha : a = 1 - d)
    (hcu : c_u = k * (1 - δ * a) + m) (hcupos : 0 < c_u)
    (hG : 0 < G) :
    (G / 2) * ((k * d + m) / c_u) < G / 2 := by
  have hgap :
      c_u - (k * d + m) = k * (1 - d) * (1 - δ) :=
    dissipation_gap_identity k d m δ a c_u ha hcu
  have hgapPos : 0 < k * (1 - d) * (1 - δ) :=
    mul_pos (mul_pos hk (sub_pos.mpr hd1)) (sub_pos.mpr hδ1)
  have hcost : k * d + m < c_u := by
    nlinarith [hgap]
  have hratio : (k * d + m) / c_u < 1 :=
    (div_lt_one hcupos).2 hcost
  have hGhalf : 0 < G / 2 := by positivity
  simpa using mul_lt_mul_of_pos_left hratio hGhalf

end

end SpawnConflict
end SEKernel
