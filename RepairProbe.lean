/-
RepairProbe.lean — anti-vacuity certificates for the repaired Law 7
interface (2026-08-07).

The 2026-08-07 audit refuted the OLD `ClassicalHopfStatement` with two
instantiations: the identically-zero field (free `α, ω` satisfied every
hypothesis) and, against any α/ω-tied variant, linear fields (free `ℓ₁`
ignored the nonlinearity).  This file machine-checks that BOTH attacks fail
the hypotheses of the REPAIRED statement:

* `zero_field_fails_rotation` — a family whose field vanishes identically is
  forced (by `hasJac` and uniqueness of the Fréchet derivative) to have zero
  Jacobian, which can never equal `rotation ω₀` for `ω₀ > 0`.
* `linear_field_ell1_zero` / `linear_field_fails_ell1` — a linear field has
  first Lyapunov number exactly 0, so the `ell1At … < 0` hypothesis fails.

Satisfiability of the repaired hypotheses is witnessed constructively by
`SEKernel.Law7.rm_supercritical_hopf` (Law7_Instantiation.lean), which
discharges every hypothesis for the replicator–mutator family.

Zero custom axioms; run `lake env lean RepairProbe.lean` to check.
-/
import SEKernel.Law7_Hopf
import SEKernel.Law7_Instantiation

namespace RepairProbe

open SEKernel.Law7

/-! ### Attack 1: the zero field cannot reach the rotation frame -/

/-- In any `HopfFamily` whose field vanishes identically, the `hasJac` field
forces the Jacobian to vanish too — the eigendata is no longer free. -/
theorem zero_field_J_zero (fam : HopfFamily)
    (hV : ∀ κ y i, fam.V κ y i = 0) (κ : ℝ) : fam.J κ = 0 := by
  have hVfun : fam.V κ = fun _ => (0 : Fin 2 → ℝ) := by
    funext y i; exact hV κ y i
  have hconst : HasFDerivAt (fam.V κ)
      (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (fam.equilibrium κ) := by
    rw [hVfun]
    exact hasFDerivAt_const _ _
  have huniq := (fam.hasJac κ).unique hconst
  ext i j
  have h1 : (LinearMap.toContinuousLinearMap
      (Matrix.mulVecLin (fam.J κ))) (Pi.single j 1) i
      = (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (Pi.single j 1) i := by
    rw [huniq]
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply, Finset.sum_ite_eq'] using h1

/-- **The zero-field attack fails the repaired hypotheses:** the zero field's
(forced) Jacobian can never be the rotation frame with positive frequency. -/
theorem zero_field_fails_rotation (fam : HopfFamily)
    (hV : ∀ κ y i, fam.V κ y i = 0) (κc ω₀ : ℝ) (hω : 0 < ω₀) :
    fam.J κc ≠ SEKernel.Law7.rotation ω₀ := by
  rw [zero_field_J_zero fam hV κc]
  intro h
  have h10 : (0 : Matrix (Fin 2) (Fin 2) ℝ) 1 0
      = SEKernel.Law7.rotation ω₀ 1 0 := by rw [h]
  simp [SEKernel.Law7.rotation] at h10
  linarith

/-! ### Attack 2: linear fields have first Lyapunov number 0 -/

private theorem deriv_affine (a b p : ℝ) :
    deriv (fun s => a * s + b) p = a := by
  simpa using (((hasDerivAt_id p).const_mul a).add_const b).deriv

private theorem p1_const (c : ℝ) (x : Fin 2 → ℝ) :
    p1 (fun _ => c) x = 0 := by
  show deriv (fun _ => c) (x 0) = 0
  exact deriv_const _ _

private theorem p2_const (c : ℝ) (x : Fin 2 → ℝ) :
    p2 (fun _ => c) x = 0 := by
  show deriv (fun _ => c) (x 1) = 0
  exact deriv_const _ _

private theorem lin_p1 (A : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2)
    (x : Fin 2 → ℝ) :
    p1 (fun z => A.mulVec z i) x = A i 0 := by
  show deriv (fun s => A.mulVec ![s, x 1] i) (x 0) = A i 0
  have hfun : (fun s => A.mulVec ![s, x 1] i)
      = fun s => A i 0 * s + A i 1 * x 1 := by
    funext s
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hfun, deriv_affine]

private theorem lin_p2 (A : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2)
    (x : Fin 2 → ℝ) :
    p2 (fun z => A.mulVec z i) x = A i 1 := by
  show deriv (fun s => A.mulVec ![x 0, s] i) (x 1) = A i 1
  have hfun : (fun s => A.mulVec ![x 0, s] i)
      = fun s => A i 1 * s + A i 0 * x 0 := by
    funext s
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hfun, deriv_affine]

private theorem lin_p1_fun (A : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    p1 (fun z => A.mulVec z i) = fun _ => A i 0 := by
  funext x; exact lin_p1 A i x

private theorem lin_p2_fun (A : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    p2 (fun z => A.mulVec z i) = fun _ => A i 1 := by
  funext x; exact lin_p2 A i x

private theorem p1_const_fun (c : ℝ) : p1 (fun _ => c) = fun _ => 0 := by
  funext x; exact p1_const c x

private theorem p2_const_fun (c : ℝ) : p2 (fun _ => c) = fun _ => 0 := by
  funext x; exact p2_const c x

/-- **The linear-field attack fails the repaired hypotheses:** the first
Lyapunov number of any linear planar field is exactly zero — the second- and
third-order jets vanish, so `ell1At … < 0` is unsatisfiable. -/
theorem linear_field_ell1_zero (A : Matrix (Fin 2) (Fin 2) ℝ) (ω : ℝ) :
    ell1At (fun z => A.mulVec z) ω = 0 := by
  simp only [ell1At]
  rw [lin_p1_fun A 0, lin_p2_fun A 0, lin_p1_fun A 1, lin_p2_fun A 1]
  simp only [p1_const_fun, p2_const_fun, p1_const, p2_const]
  ring

theorem linear_field_fails_ell1 (A : Matrix (Fin 2) (Fin 2) ℝ) (ω : ℝ) :
    ¬ (ell1At (fun z => A.mulVec z) ω < 0) := by
  rw [linear_field_ell1_zero]
  exact lt_irrefl 0

end RepairProbe

#print axioms RepairProbe.zero_field_fails_rotation
#print axioms RepairProbe.linear_field_ell1_zero
#print axioms RepairProbe.linear_field_fails_ell1
