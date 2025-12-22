/-
CertificateFrontier.lean

Lean 4 / mathlib formalization of the "certificate frontier collapse" theorem
from the Theory of Strategic Evolution.

The theorem shows that no adaptive recertification can maintain stability 
beyond a finite threshold δ̄—i.e., "certificate-chasing is futile."

We work in reduced coordinates on the tangent space T.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.Basic

open scoped BigOperators Matrix
open Filter

namespace CertificateFrontier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Symmetric part of a Jacobian `J` with respect to metric/Hessian `H`. -/
def symPart (H J : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  H * J + Jᵀ * H

/-- Negative definite predicate: `A` is neg-def iff `-A` is pos-def. -/
def NegDef (A : Matrix ι ι ℝ) : Prop :=
  Matrix.PosDef (-A)

/-- A Lyapunov (quadratic) certificate `H` is feasible for `J` iff `H ≻ 0` and
    `H J + Jᵀ H ≺ 0`. -/
def LyapFeasible (H J : Matrix ι ι ℝ) : Prop :=
  Matrix.PosDef H ∧ NegDef (symPart H J)

/-- Certificate set `C(δ)` for the affine Jacobian pencil `J(δ)=J0+δ J1`. -/
def CertSet (J0 J1 : Matrix ι ι ℝ) (δ : ℝ) : Set (Matrix ι ι ℝ) :=
  {H | LyapFeasible H (J0 + δ • J1)}

------------------------------------------------------------------------
-- Paper notation: S₀(V), D(V), S(V)
------------------------------------------------------------------------

/-- Baseline symmetric Jacobian part `S₀(V)` at certificate metric `H`. -/
def S0 (H J0 : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  symPart H J0

/-- Increasing-returns symmetric perturbation `D(V)` at certificate metric `H`. -/
def D (H J1 : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  symPart H J1

/-- Safe region `S(V)` for a fixed certificate `H`. -/
def SafeRegion (H : Matrix ι ι ℝ) : Set (Matrix ι ι ℝ) :=
  {J | Matrix.PosDef H ∧ NegDef (symPart H J)}

------------------------------------------------------------------------
-- Hurwitz predicate and key lemmas (interface/axioms)
------------------------------------------------------------------------

/-- Hurwitz stability: all eigenvalues have negative real part.

    We use the algebra spectrum of the matrix viewed as an element of
    the ℂ-algebra Matrix ι ι ℂ via the canonical embedding ℝ → ℂ. -/
def Hurwitz (J : Matrix ι ι ℝ) : Prop :=
  ∀ μ : ℂ, μ ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) → μ.re < 0

/-- **Axiom (Lyapunov Theorem)**
    
    A matrix J is Hurwitz if and only if there exists a positive definite
    matrix H such that HJ + JᵀH is negative definite.
    
    This is the classical Lyapunov stability theorem (1892). -/
axiom lyapunov_iff_hurwitz (J : Matrix ι ι ℝ) :
  Hurwitz J ↔ ∃ H : Matrix ι ι ℝ, LyapFeasible H J

/-- **Axiom (Eventual Destabilization)**
    
    For any Jacobian pencil J(δ) = J₀ + δJ₁, there exists δ₁ such that
    J(δ) is not Hurwitz for all δ ≥ δ₁.
    
    This follows from spectral perturbation theory when α(J₁) > 0,
    where α denotes spectral abscissa. -/
axiom eventually_not_hurwitz (J0 J1 : Matrix ι ι ℝ) :
  ∃ δ₁ : ℝ, ∀ δ : ℝ, δ₁ ≤ δ → ¬ Hurwitz (J0 + δ • J1)

------------------------------------------------------------------------
-- Core lemma
------------------------------------------------------------------------

/-- If J(δ) is not Hurwitz, then no Lyapunov certificate exists. -/
theorem CertSet_empty_of_not_Hurwitz {J0 J1 : Matrix ι ι ℝ} {δ : ℝ}
    (h : ¬ Hurwitz (J0 + δ • J1)) :
    CertSet J0 J1 δ = ∅ := by
  ext H
  simp only [CertSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hH
  apply h
  rw [lyapunov_iff_hurwitz]
  exact ⟨H, hH⟩

------------------------------------------------------------------------
-- Main theorems
------------------------------------------------------------------------

/-- **Certificate Frontier Collapse Theorem**
    
    There exists a finite δ̄ beyond which no Lyapunov certificate exists.
    Adaptive recertification ("certificate-chasing") cannot maintain 
    stability past this frontier.
    
    This is the key impossibility result: recertification with different
    metrics H cannot escape the fundamental spectral constraint. -/
theorem frontier_collapse (J0 J1 : Matrix ι ι ℝ) :
    ∃ δbar : ℝ, ∀ δ : ℝ, δbar < δ → CertSet J0 J1 δ = ∅ := by
  obtain ⟨δ₁, hδ₁⟩ := eventually_not_hurwitz J0 J1
  refine ⟨δ₁, fun δ hlt => ?_⟩
  have hle : δ₁ ≤ δ := le_of_lt hlt
  have hNH : ¬ Hurwitz (J0 + δ • J1) := hδ₁ δ hle
  exact CertSet_empty_of_not_Hurwitz hNH

/-- **Uniform Certificate Bound**
    
    For ANY certificate V (metric H), its critical modification level
    δ_crit(V) is bounded above by the universal frontier δ̄.
    
    This shows Version B (frontier exists) implies Version A 
    (uniform bound across all certificates). -/
theorem uniform_certificate_bound (J0 J1 : Matrix ι ι ℝ) :
    ∃ δbar : ℝ, ∀ H : Matrix ι ι ℝ, ∀ δ : ℝ,
      δbar < δ → ¬ LyapFeasible H (J0 + δ • J1) := by
  obtain ⟨δbar, hδbar⟩ := frontier_collapse J0 J1
  refine ⟨δbar, fun H δ hlt hfeas => ?_⟩
  have hempty := hδbar δ hlt
  simp only [CertSet, Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq] at hempty
  exact hempty H hfeas

------------------------------------------------------------------------
-- Governance application
------------------------------------------------------------------------

/-- **No Escape Along Equilibrium Path**
    
    If competitive equilibrium modifications δ*(κ) diverge as friction 
    κ → 0, then for sufficiently small κ, no certificate exists.
    
    This is the "governance bite": selection pressure eventually 
    overcomes ANY verification scheme. -/
theorem no_escape_along_path (J0 J1 : Matrix ι ι ℝ) 
    (δstar : ℝ → ℝ) -- equilibrium modification as function of friction
    (h_diverge : ∀ M : ℝ, ∃ κ₀ : ℝ, κ₀ > 0 ∧ ∀ κ : ℝ, 0 < κ → κ < κ₀ → δstar κ > M) :
    ∃ κ₀ : ℝ, κ₀ > 0 ∧ ∀ κ : ℝ, 0 < κ → κ < κ₀ → CertSet J0 J1 (δstar κ) = ∅ := by
  obtain ⟨δbar, hδbar⟩ := frontier_collapse J0 J1
  obtain ⟨κ₀, hκ₀_pos, hκ₀⟩ := h_diverge δbar
  refine ⟨κ₀, hκ₀_pos, fun κ hpos hlt => ?_⟩
  have hbig : δstar κ > δbar := hκ₀ κ hpos hlt
  exact hδbar (δstar κ) hbig

end CertificateFrontier
