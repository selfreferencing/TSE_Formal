/-
SEKernel / SpectralBridge.lean
AQ-10 repair: correct spectral bounds for the gain-matrix calculus, proved
to Mathlib's current reach — arXiv:2512.07901 Cor C.2/C.3, Lemma 11.3,
Theorem 11.7(d).

The paper's Lemma 11.3 display `ρ(Γ̃) ≤ ρ(Γ) + √(‖b‖·‖c‖)` and the
Theorem 11.7(d) "Gershgorin" display are not correct as printed (STATEMENTS
AQ-10).  This file supplies the machine-checked spectral statements that
deliver the intended conclusions:

* `eigenvalue_le_rowSum` — Gershgorin-type bound (paper Cor C.2's use):
  every complex eigenvalue is bounded in modulus by any uniform row-sum
  bound.  Proof: the spectrum of a unital Banach algebra lies in the closed
  ball of the norm (`spectrum.norm_le_norm_of_mem`), applied to the L∞
  operator norm on matrices (max absolute row sum).
* `gain_eigenvalue_bound` — spectral Cor C.3 for a nonnegative real gain
  matrix: row sums ≤ 1 − m ⟹ every eigenvalue (of the complexification —
  the correct reading of "eigenvalue of a real matrix") has modulus ≤ 1 − m.
* `extension_eigenvalue_bound` — the **corrected Lemma 11.3 / 11.7(d)
  display**: for the block extension Γ̃ = [[Γ, b],[cᵀ, 0]], if each old row
  sum plus its new coupling is ≤ 1 − m′ and the new row sum is ≤ 1 − m′,
  then every eigenvalue of Γ̃ has modulus ≤ 1 − m′ — quantified slack
  retention with an explicit, correct bound.

Together with `Law4.extension_cert` (the exact certificate-form extension)
these replace the flagged displays.  The remaining classical piece — the
Perron–Frobenius equivalence between the certificate and ρ(Γ) < 1 for
nonnegative matrices (paper Thm C.5(2)⟺(3)) — is not yet in Mathlib and
stays a recorded interface (AQ-9/AQ-11).

Zero custom axioms.
-/
import Mathlib
import SEKernel.Law3_Stability
import SEKernel.Law4_ClosureG

namespace SEKernel
namespace SpectralBridge

open Finset

section LinftyOp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]

/-- **Gershgorin-type eigenvalue bound (paper Cor C.2, corrected use):**
every element of the spectrum of a complex matrix is bounded in modulus by
any uniform bound on the absolute row sums. -/
theorem eigenvalue_le_rowSum (A : Matrix L L ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ c) :
    ∀ z ∈ spectrum ℂ A, ‖z‖ ≤ c := by
  intro z hz
  have hAle : ‖A‖ ≤ c := by
    rw [Matrix.linfty_opNorm_def]
    have hsup : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ c.toNNReal := by
      refine Finset.sup_le fun i _ => ?_
      rw [← NNReal.coe_le_coe, NNReal.coe_sum, Real.coe_toNNReal c hc]
      simpa [coe_nnnorm] using hrow i
    calc ((Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) : ℝ)
        ≤ (c.toNNReal : ℝ) := NNReal.coe_le_coe.mpr hsup
      _ = c := Real.coe_toNNReal c hc
  exact le_trans (spectrum.norm_le_norm_of_mem hz) hAle

/-- **Spectral Corollary C.3 (corrected orientation):** a nonnegative real
gain matrix with row sums ≤ 1 − m has all (complex) eigenvalues of modulus
≤ 1 − m; in particular row sums strictly inside 1 give spectral radius
< 1. -/
theorem gain_eigenvalue_bound (Γ : L → L → ℝ) (hΓ : ∀ i j, 0 ≤ Γ i j)
    {m : ℝ} (hm : 0 ≤ 1 - m)
    (hrow : ∀ i, ∑ j, Γ i j ≤ 1 - m) :
    ∀ z ∈ spectrum ℂ (Matrix.of fun i j => (Γ i j : ℂ)), ‖z‖ ≤ 1 - m := by
  apply eigenvalue_le_rowSum _ hm
  intro i
  have hnorm : ∀ j, ‖(Matrix.of fun i j => (Γ i j : ℂ)) i j‖ = Γ i j := by
    intro j
    simp only [Matrix.of_apply, Complex.norm_real]
    exact abs_of_nonneg (hΓ i j)
  calc ∑ j, ‖(Matrix.of fun i j => (Γ i j : ℂ)) i j‖
      = ∑ j, Γ i j := Finset.sum_congr rfl fun j _ => hnorm j
    _ ≤ 1 - m := hrow i

end LinftyOp

section Extension

open SmallGain

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- **Corrected Lemma 11.3 / Theorem 11.7(d) spectral display.**  For the
block extension `Γ̃ = [[Γ, b],[cᵀ, 0]]` of a nonnegative gain matrix by
nonnegative couplings: if every old row's sum plus its new coupling is at
most `1 − m′`, and the new row's sum is at most `1 − m′`, then **every
complex eigenvalue of Γ̃ has modulus at most `1 − m′`** — the extension
retains quantified spectral slack.  (This replaces the paper's
`ρ(Γ̃) ≤ ρ(Γ) + √(‖b‖·‖c‖)` and "Gershgorin" displays, which are incorrect
as printed; the exact certificate-form counterpart is
`SmallGain.extension_cert`.) -/
theorem extension_eigenvalue_bound
    (Γ : L → L → ℝ) (b c : L → ℝ)
    (hΓ : ∀ i j, 0 ≤ Γ i j) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    {m' : ℝ} (hm : 0 ≤ 1 - m')
    (hrowOld : ∀ ℓ, (∑ ℓ', Γ ℓ ℓ') + b ℓ ≤ 1 - m')
    (hrowNew : ∑ ℓ', c ℓ' ≤ 1 - m') :
    ∀ z ∈ spectrum ℂ
      (Matrix.of fun k k' => ((extendGain Γ b c k k' : ℝ) : ℂ)),
      ‖z‖ ≤ 1 - m' := by
  have hnn : ∀ k k', 0 ≤ extendGain Γ b c k k' := by
    intro k k'
    cases k with
    | some ℓ =>
      cases k' with
      | some ℓ' => exact hΓ ℓ ℓ'
      | none => exact hb ℓ
    | none =>
      cases k' with
      | some ℓ' => exact hc ℓ'
      | none => exact le_refl 0
  have hrows : ∀ k, ∑ k', extendGain Γ b c k k' ≤ 1 - m' := by
    intro k
    cases k with
    | some ℓ =>
      rw [Fintype.sum_option]
      simp only [extendGain]
      linarith [hrowOld ℓ]
    | none =>
      rw [Fintype.sum_option]
      simp only [extendGain]
      linarith [hrowNew]
  exact gain_eigenvalue_bound _ hnn hm hrows

end Extension

end SpectralBridge
end SEKernel
