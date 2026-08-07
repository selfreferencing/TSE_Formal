/-
SEKernel / Law3_SpectralClosure.lean
Law 3 (H-γ Stability) — closure of the AQ-9 spectral interface (2026-08-07).

The kernel's Law 3 proves the G1 Lyapunov chain from the M-matrix
certificate `SmallGainCert Γ v m` (paper Thm C.5(3)).  The audit of
2026-08-07 flagged that the paper's Law 3 is stated spectrally ("stable iff
ρ(Γ) < 1") and that the certificate ⟺ spectral-radius bridge was deferred,
so neither direction of the spectral phrasing was machine-checked.

This module closes the interface.  Both directions are proved outright,
with zero custom axioms:

* `spectral_bound_of_cert` — a certificate with positive margin forces
  every complex eigenvalue of Γ inside a disc of radius `1 − m/vmax < 1`
  (diagonal similarity + the Gershgorin-type bound of `SpectralBridge`).
* `cert_of_spectral` — if every complex eigenvalue of Γ has modulus < 1,
  a certificate with positive margin exists.  Proof: Gelfand's formula
  gives `‖(Γᵀ)^N‖ < 1` for some `N`; the finite Neumann sum
  `v = Σ_{k<N} (Γᵀ)^k 𝟙` is then a positive weight vector with margin
  `1 − ‖(Γᵀ)^N‖`.  (No Perron–Frobenius input needed.)
* `cert_iff_spectral` — the equivalence, i.e. paper Thm C.5 (2) ⟺ (3)
  for nonnegative gain matrices.
* `G1_weighted_lyapunov_of_spectral` — Law 3 in its own spectral phrasing:
  every eigenvalue of the normalised gain matrix inside the unit disc
  implies the G1 weighted Lyapunov inequality.  This is the statement the
  paper's Law 3 names.

Zero custom axioms.
-/
import Mathlib
import SEKernel.Law3_Stability
import SEKernel.SpectralBridge

namespace SEKernel
namespace SmallGain

open Finset
open scoped Matrix

section Spectral

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]

/-- Complexification of a real square matrix, entrywise. -/
private def cx (M : Matrix L L ℝ) : Matrix L L ℂ :=
  Matrix.of fun i j => (M i j : ℂ)

private lemma cx_apply (M : Matrix L L ℝ) (i j : L) : cx M i j = (M i j : ℂ) := rfl

/-- `cx` is multiplicative (entrywise coercion is a ring hom). -/
private lemma cx_mul (M N : Matrix L L ℝ) : cx (M * N) = cx M * cx N := by
  ext i j
  simp only [cx, Matrix.of_apply, Matrix.mul_apply]
  push_cast
  rfl

private lemma cx_one : cx (1 : Matrix L L ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [cx, Matrix.one_apply, h]

private lemma cx_pow (M : Matrix L L ℝ) (n : ℕ) : cx (M ^ n) = cx M ^ n := by
  induction n with
  | zero => simpa using cx_one
  | succ k ih => rw [pow_succ, pow_succ, cx_mul, ih]

/-- Spectrum is invariant under transposition (over ℂ; determinant argument). -/
theorem spectrum_transpose (A : Matrix L L ℂ) :
    spectrum ℂ (Aᵀ) = spectrum ℂ A := by
  ext z
  simp only [spectrum.mem_iff]
  have hT : algebraMap ℂ (Matrix L L ℂ) z - Aᵀ
      = (algebraMap ℂ (Matrix L L ℂ) z - A)ᵀ := by
    rw [Matrix.transpose_sub]
    congr 1
    simp [Matrix.algebraMap_eq_diagonal]
  rw [hT, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose,
    ← Matrix.isUnit_iff_isUnit_det]

/-- **Certificate ⟹ spectral bound.**  A small-gain certificate with margin
`m > 0` confines every complex eigenvalue of Γ to the closed disc of radius
`1 − m/vmax`, where `vmax` is the largest weight; in particular ρ(Γ) < 1.
(Diagonal similarity `D⁻¹ Γᵀ D` with `D = diag v` turns the certificate's
column margins into row-sum slack, and the Gershgorin-type bound of
`SpectralBridge` applies.) -/
theorem spectral_bound_of_cert {Γ : L → L → ℝ} {v : L → ℝ} {m : ℝ}
    (hΓ : ∀ i j, 0 ≤ Γ i j) (hcert : SmallGainCert Γ v m) (hm : 0 < m) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ z ∈ spectrum ℂ (Matrix.of fun i j => (Γ i j : ℂ)), ‖z‖ ≤ r := by
  classical
  -- the largest weight
  set vmax : ℝ := univ.sup' univ_nonempty v with hvmax
  have hv_le : ∀ ℓ, v ℓ ≤ vmax := fun ℓ => le_sup' v (mem_univ ℓ)
  have ℓ₀ : L := Classical.arbitrary L
  have hvmax_pos : 0 < vmax := lt_of_lt_of_le (hcert.pos ℓ₀) (hv_le ℓ₀)
  -- the margin forces m ≤ v ℓ for every ℓ
  have hm_le : ∀ ℓ, m ≤ v ℓ := by
    intro ℓ
    have h := hcert.margin ℓ
    have hsum : 0 ≤ ∑ ℓ', Γ ℓ' ℓ * v ℓ' :=
      Finset.sum_nonneg fun ℓ' _ =>
        mul_nonneg (hΓ ℓ' ℓ) (le_of_lt (hcert.pos ℓ'))
    linarith
  have hmvmax : m / vmax ≤ 1 := by
    rw [div_le_one hvmax_pos]
    exact le_trans (hm_le ℓ₀) (hv_le ℓ₀)
  refine ⟨1 - m / vmax, by linarith, ?_, ?_⟩
  · have : 0 < m / vmax := div_pos hm hvmax_pos
    linarith
  -- the similarity: M = D⁻¹ (cx Γᵀ) D with D = diag (v·)
  intro z hz
  set B : Matrix L L ℝ := (Matrix.of Γ)ᵀ with hB
  set D : Matrix L L ℂ := Matrix.diagonal fun ℓ => (v ℓ : ℂ) with hD
  set Dinv : Matrix L L ℂ := Matrix.diagonal fun ℓ => ((v ℓ : ℂ))⁻¹ with hDinv
  have hv_ne : ∀ ℓ, ((v ℓ : ℂ)) ≠ 0 := fun ℓ => by
    exact_mod_cast ne_of_gt (hcert.pos ℓ)
  have hDD : D * Dinv = 1 := by
    rw [hD, hDinv, Matrix.diagonal_mul_diagonal]
    have : (fun ℓ => (v ℓ : ℂ) * ((v ℓ : ℂ))⁻¹) = fun _ => (1 : ℂ) :=
      funext fun ℓ => mul_inv_cancel₀ (hv_ne ℓ)
    rw [this, Matrix.diagonal_one]
  have hDD' : Dinv * D = 1 := by
    rw [hD, hDinv, Matrix.diagonal_mul_diagonal]
    have : (fun ℓ => ((v ℓ : ℂ))⁻¹ * (v ℓ : ℂ)) = fun _ => (1 : ℂ) :=
      funext fun ℓ => inv_mul_cancel₀ (hv_ne ℓ)
    rw [this, Matrix.diagonal_one]
  -- the unit and the conjugated matrix
  have hσ : spectrum ℂ (Dinv * cx B * D) = spectrum ℂ (cx B) := by
    have h := spectrum.units_conjugate' (R := ℂ) (a := cx B)
      (u := ⟨D, Dinv, hDD, hDD'⟩)
    exact h
  -- z lies in the spectrum of the conjugated matrix
  have hzB : z ∈ spectrum ℂ (Dinv * cx B * D) := by
    have hcxT : cx B = (cx (Matrix.of Γ))ᵀ := by
      ext i j; simp [cx, hB, Matrix.transpose_apply]
    have hz' : z ∈ spectrum ℂ (cx B) := by
      rw [hcxT, spectrum_transpose]
      exact hz
    rw [hσ]
    exact hz'
  -- row sums of the conjugated matrix are ≤ 1 − m/vmax
  refine SpectralBridge.eigenvalue_le_rowSum (Dinv * cx B * D) ?_ ?_ z hzB
  · have : 0 < m / vmax := div_pos hm hvmax_pos
    linarith
  · intro i
    have hentry : ∀ j, (Dinv * cx B * D) i j
        = ((v i : ℂ))⁻¹ * (Γ j i : ℂ) * (v j : ℂ) := by
      intro j
      rw [hDinv, hD]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp [cx, hB, Matrix.transpose_apply]
    have hnorm : ∀ j, ‖(Dinv * cx B * D) i j‖ = (v i)⁻¹ * Γ j i * v j := by
      intro j
      rw [hentry j, norm_mul, norm_mul, norm_inv]
      have h1 : ‖((v i : ℝ) : ℂ)‖ = v i := by
        rw [Complex.norm_real]; exact abs_of_pos (hcert.pos i)
      have h2 : ‖((Γ j i : ℝ) : ℂ)‖ = Γ j i := by
        rw [Complex.norm_real]; exact abs_of_nonneg (hΓ j i)
      have h3 : ‖((v j : ℝ) : ℂ)‖ = v j := by
        rw [Complex.norm_real]; exact abs_of_pos (hcert.pos j)
      rw [h1, h2, h3]
    calc ∑ j, ‖(Dinv * cx B * D) i j‖
        = (v i)⁻¹ * ∑ j, Γ j i * v j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [hnorm j]; ring
      _ ≤ (v i)⁻¹ * (v i - m) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt (hcert.pos i)))
          have := hcert.margin i
          linarith
      _ = 1 - m / v i := by
          have hne : v i ≠ 0 := ne_of_gt (hcert.pos i)
          field_simp
      _ ≤ 1 - m / vmax := by
          have h1 : m / vmax ≤ m / v i :=
            div_le_div_of_nonneg_left (le_of_lt hm) (hcert.pos i) (hv_le i)
          linarith

/-- Entries of powers of an entrywise-nonnegative matrix are nonnegative. -/
private lemma pow_nonneg_entries {B : Matrix L L ℝ} (hB : ∀ i j, 0 ≤ B i j) :
    ∀ (n : ℕ) (i j : L), 0 ≤ (B ^ n) i j := by
  intro n
  induction n with
  | zero =>
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun ℓ _ => mul_nonneg (ih i ℓ) (hB ℓ j)

/-- **Spectral bound ⟹ certificate.**  If every complex eigenvalue of the
nonnegative gain matrix Γ has modulus < 1, then a small-gain certificate
with strictly positive margin exists: Gelfand's formula produces `N` with
`‖(Γᵀ)^N‖ < 1` in the L∞ operator norm, and the finite Neumann sum
`v ℓ = Σ_{k<N} ((Γᵀ)^k 𝟙) ℓ` is a positive weight vector whose margin is
`1 − ‖(Γᵀ)^N‖ > 0`.  No Perron–Frobenius theory is used. -/
theorem cert_of_spectral {Γ : L → L → ℝ}
    (hΓ : ∀ i j, 0 ≤ Γ i j)
    (hspec : ∀ z ∈ spectrum ℂ (Matrix.of fun i j => (Γ i j : ℂ)), ‖z‖ < 1) :
    ∃ (v : L → ℝ) (m : ℝ), 0 < m ∧ SmallGainCert Γ v m := by
  classical
  set B : Matrix L L ℝ := (Matrix.of Γ)ᵀ with hB
  have hBnn : ∀ i j, 0 ≤ B i j := fun i j => hΓ j i
  have hBapp : ∀ a b : L, B a b = Γ b a := fun a b => rfl
  -- transfer the spectral hypothesis to the complexified transpose
  have hspecB : ∀ z ∈ spectrum ℂ (cx B), ‖z‖ < 1 := by
    intro z hz
    apply hspec
    have hcxT : cx B = (cx (Matrix.of Γ))ᵀ := by
      ext i j; simp [cx, hB, Matrix.transpose_apply]
    rwa [hcxT, spectrum_transpose] at hz
  -- spectral radius < 1
  have hρ : spectralRadius ℂ (cx B) < 1 := by
    have h := spectrum.spectralRadius_lt_of_forall_lt (cx B)
      (r := 1) (fun k hk => by exact_mod_cast hspecB k hk)
    simpa using h
  -- Gelfand: some power has norm < 1
  have htend := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (cx B)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (‖cx B ^ n‖₊ : ENNReal) ^ (1 / (n : ℝ)) < 1 :=
    htend.eventually_lt_const hρ
  obtain ⟨N, hN1, hNlt⟩ :
      ∃ N : ℕ, 1 ≤ N ∧ (‖cx B ^ N‖₊ : ENNReal) ^ (1 / (N : ℝ)) < 1 := by
    obtain ⟨N, hN⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
    exact ⟨N, hN.2, hN.1⟩
  -- extract ‖B^N‖ < 1 (real norm)
  have hpowlt : ‖cx B ^ N‖₊ < 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (1 : ENNReal) ≤ (‖cx B ^ N‖₊ : ENNReal) := by exact_mod_cast hcon
    have h2 : (1 : ENNReal) ^ (1 / (N : ℝ)) ≤
        (‖cx B ^ N‖₊ : ENNReal) ^ (1 / (N : ℝ)) :=
      ENNReal.rpow_le_rpow h1 (by positivity)
    rw [ENNReal.one_rpow] at h2
    exact absurd (lt_of_le_of_lt h2 hNlt) (lt_irrefl 1)
  have hnormlt : ‖cx B ^ N‖ < 1 := by
    calc ‖cx B ^ N‖ = ((‖cx B ^ N‖₊ : NNReal) : ℝ) := (coe_nnnorm _).symm
      _ < ((1 : NNReal) : ℝ) := NNReal.coe_lt_coe.mpr hpowlt
      _ = 1 := NNReal.coe_one
  -- row sums of B^N are bounded by ‖(cx B)^N‖
  have hrowN : ∀ i, ∑ j, (B ^ N) i j ≤ ‖cx B ^ N‖ := by
    intro i
    have hle : (∑ j, ‖(cx B ^ N) i j‖₊) ≤ ‖cx B ^ N‖₊ := by
      rw [Matrix.linfty_opNNNorm_def]
      exact Finset.le_sup (f := fun i => ∑ j, ‖(cx B ^ N) i j‖₊) (mem_univ i)
    have hcast : ((∑ j, ‖(cx B ^ N) i j‖₊ : NNReal) : ℝ) = ∑ j, (B ^ N) i j := by
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← cx_pow, cx_apply, Complex.norm_real]
      exact abs_of_nonneg (pow_nonneg_entries hBnn N i j)
    calc ∑ j, (B ^ N) i j
        = ((∑ j, ‖(cx B ^ N) i j‖₊ : NNReal) : ℝ) := hcast.symm
      _ ≤ ((‖cx B ^ N‖₊ : NNReal) : ℝ) := by exact_mod_cast hle
      _ = ‖cx B ^ N‖ := coe_nnnorm _
  -- the finite Neumann weights
  set v : L → ℝ := fun ℓ => ∑ k ∈ Finset.range N, ∑ ℓ', (B ^ k) ℓ ℓ' with hv
  set t : ℝ := ‖cx B ^ N‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hrs0 : ∀ ℓ : L, ∑ ℓ', ((B : Matrix L L ℝ) ^ 0) ℓ ℓ' = 1 := by
    intro ℓ
    simp [Matrix.one_apply]
  refine ⟨v, 1 - t, by linarith, ?_, ?_⟩
  -- positivity: the k = 0 term contributes the row sum of 𝟙, namely 1
  · intro ℓ
    have h0mem : 0 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hge : (1 : ℝ) ≤ v ℓ := by
      rw [hv]
      dsimp only
      calc (1 : ℝ) = ∑ ℓ', ((B : Matrix L L ℝ) ^ 0) ℓ ℓ' := (hrs0 ℓ).symm
        _ ≤ ∑ k ∈ Finset.range N, ∑ ℓ', (B ^ k) ℓ ℓ' :=
            Finset.single_le_sum
              (f := fun k => ∑ ℓ', ((B : Matrix L L ℝ) ^ k) ℓ ℓ')
              (fun k _ => Finset.sum_nonneg fun ℓ' _ =>
                pow_nonneg_entries hBnn k ℓ ℓ') h0mem
    linarith
  -- margin: v ℓ − (Γᵀ v) ℓ telescopes to 1 − rowSum(B^N) ℓ ≥ 1 − t
  · intro ℓ
    have hkey : ∑ ℓ', Γ ℓ' ℓ * v ℓ'
        = ∑ k ∈ Finset.range N, ∑ ℓ'', (B ^ (k + 1)) ℓ ℓ'' := by
      have h1 : ∀ ℓ' : L, Γ ℓ' ℓ * v ℓ'
          = ∑ k ∈ Finset.range N, B ℓ ℓ' * ∑ ℓ'', (B ^ k) ℓ' ℓ'' := by
        intro ℓ'
        rw [hv]
        dsimp only
        rw [Finset.mul_sum, hBapp]
      rw [Finset.sum_congr rfl fun ℓ' _ => h1 ℓ']
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hpow : ∀ ℓ'' : L, (B ^ (k + 1)) ℓ ℓ'' = ∑ ℓ', B ℓ ℓ' * (B ^ k) ℓ' ℓ'' := by
        intro ℓ''
        rw [pow_succ', Matrix.mul_apply]
      rw [Finset.sum_congr rfl fun ℓ'' _ => hpow ℓ'']
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ℓ' _ => by rw [Finset.mul_sum]
    have htel : v ℓ - ∑ ℓ', Γ ℓ' ℓ * v ℓ'
        = 1 - ∑ ℓ'', (B ^ N) ℓ ℓ'' := by
      rw [hkey, hv]
      dsimp only
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_range_sub' (f := fun k => ∑ ℓ'', ((B : Matrix L L ℝ) ^ k) ℓ ℓ'') N]
      rw [hrs0 ℓ]
    have hfin := hrowN ℓ
    linarith [htel, hfin]

/-- **AQ-9 closed: certificate ⟺ spectral radius (paper Thm C.5, (2) ⟺ (3),
for nonnegative gain matrices).**  A positive-margin M-matrix certificate
exists exactly when every complex eigenvalue of Γ lies strictly inside the
unit disc. -/
theorem cert_iff_spectral {Γ : L → L → ℝ} (hΓ : ∀ i j, 0 ≤ Γ i j) :
    (∃ (v : L → ℝ) (m : ℝ), 0 < m ∧ SmallGainCert Γ v m) ↔
      ∀ z ∈ spectrum ℂ (Matrix.of fun i j => (Γ i j : ℂ)), ‖z‖ < 1 := by
  constructor
  · rintro ⟨v, m, hm, hcert⟩ z hz
    obtain ⟨r, -, hr1, hbound⟩ := spectral_bound_of_cert hΓ hcert hm
    exact lt_of_le_of_lt (hbound z hz) hr1
  · exact cert_of_spectral hΓ

end Spectral

section Law3Spectral

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
variable {γ : L → ℝ} {β : L → L → ℝ} {Var E : L → ℝ}

/-- **Law 3 in its own spectral phrasing (Theorem 8.2 as the paper states
it).**  If every complex eigenvalue of the normalised gain matrix
(Definition 7.5) has modulus < 1 — the ρ(Γ) < 1 condition — then positive
weights and a positive margin exist for which the α-weighted total of
per-level Price increments dominates the total variance: the G1 Lyapunov
inequality.  Chains `cert_of_spectral` with `G1_weighted_lyapunov`; the
previously deferred spectral interface (AQ-9) no longer appears. -/
theorem G1_weighted_lyapunov_of_spectral
    (hVar : ∀ ℓ, 0 ≤ Var ℓ) (hγ : ∀ ℓ, γ ℓ < 1)
    (hβ : ∀ ℓ ℓ', 0 ≤ β ℓ ℓ') (hβdiag : ∀ ℓ, β ℓ ℓ = 0)
    (hHNL : ∀ ℓ, -(γ ℓ * Var ℓ) - ∑ ℓ' ∈ {ℓ}ᶜ, β ℓ ℓ' * Var ℓ' ≤ E ℓ)
    (hspec : ∀ z ∈ spectrum ℂ
      (Matrix.of fun ℓ ℓ' => (gainMatrix γ β ℓ ℓ' : ℂ)), ‖z‖ < 1) :
    ∃ (v : L → ℝ) (m : ℝ), 0 < m ∧
      m * ∑ ℓ, Var ℓ ≤ ∑ ℓ, (v ℓ / (1 - γ ℓ)) * (Var ℓ + E ℓ) := by
  have hnn : ∀ ℓ ℓ', 0 ≤ gainMatrix γ β ℓ ℓ' := by
    intro ℓ ℓ'
    unfold gainMatrix
    split_ifs
    · exact le_refl 0
    · exact div_nonneg (hβ ℓ ℓ') (by linarith [hγ ℓ])
  obtain ⟨v, m, hm, hcert⟩ := cert_of_spectral hnn hspec
  exact ⟨v, m, hm, G1_weighted_lyapunov hVar hγ hβdiag hHNL hcert⟩

end Law3Spectral

end SmallGain
end SEKernel
