/-
SEKernel / Law3_Stability.lean
Law 3 (H-γ Stability), certificate form — arXiv:2512.07901 §§7–8, Appendix C.

Small-gain theory for the N-level Poiesis stack.  Per the paper's own
Theorem C.5 (M-matrix characterisation, item 3), the working small-gain
hypothesis is a positive weight vector `v` with `(I − Γᵀ) v ≥ m·𝟙`
componentwise (`SmallGainCert Γ v m`).  For nonnegative Γ this is
equivalent to ρ(Γ) < 1; the kernel proves everything from the
certificate, proves the column-sum sufficient condition (paper Cor C.3,
in the transposed orientation that G1 actually consumes) outright, and
leaves the spectral-radius bridge as the recorded Tier-2 interface
(STATEMENTS.md, AQ-9).

Main results:
* `SmallGainCert.of_colSums`  — column sums ≤ 1 − m give the certificate
  v = 𝟙 (paper Cor C.3, transposed orientation).
* `G1_weight_pos`             — Lemma 8.1 weights α_ℓ = v_ℓ/(1−γ_ℓ) > 0.
* `G1_weighted_lyapunov`      — Theorem 8.2 (G1), algebraic heart: under
  the H-NL bounds and a certificate, the α-weighted total of per-level
  Price increments dominates m·Σ Var.  Exactly the paper's displayed
  chain in the proof of Theorem 8.2.
* `G1_weighted_lyapunov_nonneg` — the `d/dt Ψ_N ≥ 0` packaging.

Finding recorded during formalization: the G1 inequality does not need
β ≥ 0 (Assumption 7.3 posits it); the H-NL inequality itself carries all
the sign information used.

Zero custom axioms; everything is finite Finset algebra over ℝ.
-/
import Mathlib

namespace SEKernel
namespace SmallGain

variable {L : Type*} [Fintype L]

/-- Small-gain certificate (paper Thm C.5(3), for `Γᵀ`): positive weights `v`
with margin `m` in every column: `v ℓ − Σ_{ℓ'} Γ ℓ' ℓ * v ℓ' ≥ m`. -/
structure SmallGainCert (Γ : L → L → ℝ) (v : L → ℝ) (m : ℝ) : Prop where
  pos : ∀ ℓ, 0 < v ℓ
  margin : ∀ ℓ, m ≤ v ℓ - ∑ ℓ', Γ ℓ' ℓ * v ℓ'

/-- Paper Corollary C.3 (transposed orientation): if all column sums of the
gain matrix are at most `1 − m`, the all-ones vector is a small-gain
certificate with margin `m`. -/
theorem SmallGainCert.of_colSums {Γ : L → L → ℝ} {m : ℝ}
    (h : ∀ ℓ, ∑ ℓ', Γ ℓ' ℓ ≤ 1 - m) :
    SmallGainCert Γ (fun _ => 1) m := by
  refine ⟨fun _ => one_pos, fun ℓ => ?_⟩
  have h' := h ℓ
  simp only [mul_one]
  linarith

variable [DecidableEq L]

/-- The normalised gain matrix of Definition 7.5: `Γ ℓ ℓ' = β ℓ ℓ' / (1 − γ ℓ)`
off the diagonal, `0` on it. -/
noncomputable def gainMatrix (γ : L → ℝ) (β : L → L → ℝ) : L → L → ℝ :=
  fun ℓ ℓ' => if ℓ' = ℓ then 0 else β ℓ ℓ' / (1 - γ ℓ)

variable {γ : L → ℝ} {β : L → L → ℝ} {Var E v : L → ℝ} {m : ℝ}

/-- Lemma 8.1 (positivity of the G1 weights): `α_ℓ = v_ℓ/(1−γ_ℓ) > 0`. -/
theorem G1_weight_pos (hγ : ∀ ℓ, γ ℓ < 1) (hv : ∀ ℓ, 0 < v ℓ) (ℓ : L) :
    0 < v ℓ / (1 - γ ℓ) :=
  div_pos (hv ℓ) (by linarith [hγ ℓ])

/-- **Theorem 8.2 (G1: N-Level Lyapunov), algebraic heart.**
`Var ℓ ≥ 0` are the per-level variances and `E ℓ` the externality terms of the
per-level Price decompositions (`d/dt f̄⁽ℓ⁾ = Var ℓ + E ℓ`, taken as input —
discrete-step or given-derivative form).  Under the H-NL bounds
(Assumption 7.3) and a small-gain certificate `v` with margin `m` for the
normalised gain matrix, the weights `α ℓ = v ℓ / (1 − γ ℓ)` satisfy

  `Σ_ℓ α ℓ (Var ℓ + E ℓ)  ≥  m · Σ_ℓ Var ℓ`.

With `m = 1` (the paper's normalisation `(I−Γᵀ)v = 𝟙`) this is exactly the
final display of the paper's proof, `d/dt Ψ_N ≥ Σ_ℓ Var⁽ℓ⁾`. -/
theorem G1_weighted_lyapunov
    (hVar : ∀ ℓ, 0 ≤ Var ℓ)
    (hγ : ∀ ℓ, γ ℓ < 1)
    (hβdiag : ∀ ℓ, β ℓ ℓ = 0)
    (hHNL : ∀ ℓ, -(γ ℓ * Var ℓ) - ∑ ℓ' ∈ {ℓ}ᶜ, β ℓ ℓ' * Var ℓ' ≤ E ℓ)
    (hcert : SmallGainCert (gainMatrix γ β) v m) :
    m * ∑ ℓ, Var ℓ ≤ ∑ ℓ, (v ℓ / (1 - γ ℓ)) * (Var ℓ + E ℓ) := by
  have hγpos : ∀ ℓ, 0 < 1 - γ ℓ := fun ℓ => by linarith [hγ ℓ]
  set α : L → ℝ := fun ℓ => v ℓ / (1 - γ ℓ) with hα
  have hαpos : ∀ ℓ, 0 < α ℓ := fun ℓ => div_pos (hcert.pos ℓ) (hγpos ℓ)
  -- Step 1: pointwise lower bound from H-NL, weighted by α ℓ > 0.
  have step1 : ∀ ℓ, α ℓ * ((1 - γ ℓ) * Var ℓ - ∑ ℓ' ∈ {ℓ}ᶜ, β ℓ ℓ' * Var ℓ')
      ≤ α ℓ * (Var ℓ + E ℓ) := by
    intro ℓ
    have h := hHNL ℓ
    have hineq : (1 - γ ℓ) * Var ℓ - ∑ ℓ' ∈ {ℓ}ᶜ, β ℓ ℓ' * Var ℓ'
        ≤ Var ℓ + E ℓ := by nlinarith [h]
    exact mul_le_mul_of_nonneg_left hineq (le_of_lt (hαpos ℓ))
  -- Step 2: rearrange the α-weighted left side into certificate columns.
  have key : ∑ ℓ, α ℓ * ((1 - γ ℓ) * Var ℓ - ∑ ℓ' ∈ {ℓ}ᶜ, β ℓ ℓ' * Var ℓ')
      = ∑ ℓ, (v ℓ - ∑ ℓ', gainMatrix γ β ℓ' ℓ * v ℓ') * Var ℓ := by
    have hαγ : ∀ ℓ, α ℓ * (1 - γ ℓ) = v ℓ := fun ℓ =>
      div_mul_cancel₀ (v ℓ) (ne_of_gt (hγpos ℓ))
    -- complete the restricted inner sums (diagonal terms vanish)
    have hdiag0 : ∀ ℓ, ∑ ℓ' ∈ ({ℓ}ᶜ : Finset L), α ℓ * β ℓ ℓ' * Var ℓ'
        = ∑ ℓ', α ℓ * β ℓ ℓ' * Var ℓ' := by
      intro ℓ
      have hsplit := Finset.sum_compl_add_sum {ℓ}
        (fun ℓ' => α ℓ * β ℓ ℓ' * Var ℓ')
      have hsing : ∑ ℓ' ∈ ({ℓ} : Finset L), α ℓ * β ℓ ℓ' * Var ℓ' = 0 := by
        simp [hβdiag ℓ]
      linarith
    have hterm : ∀ ℓ ℓ', gainMatrix γ β ℓ' ℓ * v ℓ' * Var ℓ
        = α ℓ' * β ℓ' ℓ * Var ℓ := by
      intro ℓ ℓ'
      by_cases h : ℓ = ℓ'
      · subst h; simp [gainMatrix, hβdiag]
      · simp only [gainMatrix, if_neg h, hα]
        ring
    calc ∑ ℓ, α ℓ * ((1 - γ ℓ) * Var ℓ - ∑ ℓ' ∈ {ℓ}ᶜ, β ℓ ℓ' * Var ℓ')
        = ∑ ℓ, (v ℓ * Var ℓ - ∑ ℓ', α ℓ * β ℓ ℓ' * Var ℓ') := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [mul_sub, ← mul_assoc, hαγ ℓ, Finset.mul_sum]
          simp only [← mul_assoc]
          rw [hdiag0 ℓ]
      _ = ∑ ℓ, v ℓ * Var ℓ - ∑ ℓ, ∑ ℓ', α ℓ * β ℓ ℓ' * Var ℓ' := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ ℓ, v ℓ * Var ℓ - ∑ ℓ, ∑ ℓ', α ℓ' * β ℓ' ℓ * Var ℓ := by
          rw [Finset.sum_comm (f := fun ℓ ℓ' => α ℓ * β ℓ ℓ' * Var ℓ')]
      _ = ∑ ℓ, (v ℓ * Var ℓ - ∑ ℓ', α ℓ' * β ℓ' ℓ * Var ℓ) := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ ℓ, (v ℓ - ∑ ℓ', gainMatrix γ β ℓ' ℓ * v ℓ') * Var ℓ := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [sub_mul, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun ℓ' _ => (hterm ℓ ℓ').symm
  -- Step 3: apply the certificate margins and chain.
  calc m * ∑ ℓ, Var ℓ = ∑ ℓ, m * Var ℓ := by rw [Finset.mul_sum]
    _ ≤ ∑ ℓ, (v ℓ - ∑ ℓ', gainMatrix γ β ℓ' ℓ * v ℓ') * Var ℓ :=
        Finset.sum_le_sum fun ℓ _ =>
          mul_le_mul_of_nonneg_right (hcert.margin ℓ) (hVar ℓ)
    _ = ∑ ℓ, α ℓ * ((1 - γ ℓ) * Var ℓ - ∑ ℓ' ∈ {ℓ}ᶜ, β ℓ ℓ' * Var ℓ') := key.symm
    _ ≤ ∑ ℓ, α ℓ * (Var ℓ + E ℓ) := Finset.sum_le_sum fun ℓ _ => step1 ℓ

/-- G1 packaging: with nonnegative margin, the weighted Lyapunov increment is
nonnegative (`d/dt Ψ_N ≥ m·Σ Var⁽ℓ⁾ ≥ 0` in the paper's phrasing). -/
theorem G1_weighted_lyapunov_nonneg
    (hVar : ∀ ℓ, 0 ≤ Var ℓ)
    (hγ : ∀ ℓ, γ ℓ < 1)
    (hβdiag : ∀ ℓ, β ℓ ℓ = 0)
    (hHNL : ∀ ℓ, -(γ ℓ * Var ℓ) - ∑ ℓ' ∈ {ℓ}ᶜ, β ℓ ℓ' * Var ℓ' ≤ E ℓ)
    (hcert : SmallGainCert (gainMatrix γ β) v m) (hm : 0 ≤ m) :
    0 ≤ ∑ ℓ, (v ℓ / (1 - γ ℓ)) * (Var ℓ + E ℓ) := by
  have h := G1_weighted_lyapunov hVar hγ hβdiag hHNL hcert
  have h0 : 0 ≤ m * ∑ ℓ, Var ℓ :=
    mul_nonneg hm (Finset.sum_nonneg fun ℓ _ => hVar ℓ)
  linarith

end SmallGain
end SEKernel
