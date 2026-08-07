/-
SEKernel / Law7_Instantiation.lean
Law 7 (Hopf Transition) — the repaired classical interface, instantiated and
fully discharged for the canonical replicator–mutator model (2026-08-07).

This module does three things the 2026-08-07 audit asked for:

1. **It witnesses satisfiability of the repaired `ClassicalHopfStatement`
   hypotheses** on a concrete family: the planar reduction `rmPlanar κ μ` of
   the replicator–mutator field on the biased-RPS payoff, with its true
   Jacobian supplied and verified (`rmPlanar_hasJac`), joint smoothness, the
   explicit conjugation to the rotation frame, transversality, and a
   machine-DERIVED (not transcribed) first Lyapunov number.

2. **It machine-derives the first Lyapunov number.**  On the genuine
   trace-zero locus `κ = −6μ` the Jacobian factors as
   `(1 − 3μ) · J(0,0)`, one fixed matrix `P` conjugates it to the rotation
   frame with frequency `ω₀ = √3(1−3μ)/3`, and the Guckenheimer–Holmes
   number evaluates to

       `ell1At = μ·(−t⁴ − 2t² − 9)/4`   (t = √3, an exact identity)

   which is strictly negative for every `μ > 0` — supercriticality, derived
   from the dynamics themselves.  (The quadratic G–H terms cancel pairwise;
   the value reduces to `−6μ` after `t² = 3`.)

3. **It corrects the AQ-20 narrative.**  At `κ = 0, μ = 0` the eigenvalue
   pair does cross (kernel `rm_true_hopf`), but the first Lyapunov number is
   ZERO there — the pure-RPS replicator has the conserved quantity
   `x₀x₁x₂`, so `κ = 0, μ = 0` is a degenerate Hopf (a center), not a
   generic supercritical one (`ell1_pureRPS_zero`).  The genuine
   supercritical Hopf of the canonical model lives on the locus `κ = −6μ`,
   `μ ∈ (0, 1/3)`, and `rm_supercritical_hopf` delivers Law 7's conclusion
   there — nonconstant periodic orbits just past the threshold — conditional
   ONLY on the (true, tied) classical Hopf statement.

Zero custom axioms.
-/
import Mathlib
import SEKernel.Law7_Hopf

namespace SEKernel
namespace Law7

open Matrix

/-! ### The planar replicator–mutator family -/

/-- Planar reduction of the replicator–mutator field: coordinates
`(x₀, x₁)` on the simplex, `x₂ = 1 − x₀ − x₁`. -/
noncomputable def rmPlanar (κ μ : ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![rmField κ μ ![y 0, y 1, 1 - y 0 - y 1] 0,
    rmField κ μ ![y 0, y 1, 1 - y 0 - y 1] 1]

/-- The barycentre `(1/3, 1/3)` in planar coordinates. -/
noncomputable def bary : Fin 2 → ℝ := ![1/3, 1/3]

/-- The Jacobian of `rmPlanar κ μ` at the barycentre (the kernel's four
partials `rm_diag0/rm_diag1/rm_offdiag01/rm_offdiag10`, assembled). -/
noncomputable def rmJ (κ μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-κ/3 - μ - 1/3, -κ/3 - 2/3; κ/3 + 2/3, 1/3 - μ]

/-- Component 0 of the planar field, as an explicit polynomial. -/
theorem rmPlanar_comp0 (κ μ : ℝ) (y : Fin 2 → ℝ) :
    rmPlanar κ μ y 0
      = κ*(y 0)^3 + κ*(y 0)^2*(y 1) + (-2*κ - 1)*(y 0)^2 + κ*(y 0)*(y 1)^2
        + (-2*κ - 2)*(y 0)*(y 1) + (κ - μ + 1)*(y 0) + μ/3 := by
  simp only [rmPlanar, rmField, fitness, meanFit, biasedRPS, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- Component 1 of the planar field, as an explicit polynomial. -/
theorem rmPlanar_comp1 (κ μ : ℝ) (y : Fin 2 → ℝ) :
    rmPlanar κ μ y 1
      = κ*(y 0)^2*(y 1) + κ*(y 0)*(y 1)^2 + 2*(y 0)*(y 1) + κ*(y 1)^3
        + (1 - κ)*(y 1)^2 + (-μ - 1)*(y 1) + μ/3 := by
  simp only [rmPlanar, rmField, fitness, meanFit, biasedRPS, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The barycentre is an equilibrium of the planar field for every `(κ, μ)`. -/
theorem rmPlanar_bary (κ μ : ℝ) : rmPlanar κ μ bary = 0 := by
  funext i
  fin_cases i
  · show rmPlanar κ μ bary 0 = 0
    rw [rmPlanar_comp0]
    simp only [bary, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  · show rmPlanar κ μ bary 1 = 0
    rw [rmPlanar_comp1]
    simp only [bary, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring

/-! ### The Jacobian is the Fréchet derivative (the `hasJac` obligation) -/

private theorem proj_hasFDerivAt (i : Fin 2) (x : Fin 2 → ℝ) :
    HasFDerivAt (fun y : Fin 2 → ℝ => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) x :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).hasFDerivAt

/-- `rmJ κ μ` IS the Fréchet derivative of `rmPlanar κ μ` at the barycentre —
the tie the repaired `HopfFamily` demands. -/
theorem rmPlanar_hasJac (κ μ : ℝ) :
    HasFDerivAt (rmPlanar κ μ)
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (rmJ κ μ))) bary := by
  rw [hasFDerivAt_pi']
  intro i
  have h0 := proj_hasFDerivAt 0 bary
  have h1 := proj_hasFDerivAt 1 bary
  have hb0 : bary 0 = 1/3 := by simp [bary]
  have hb1 : bary 1 = 1/3 := by simp [bary]
  fin_cases i
  · -- component 0
    show HasFDerivAt (fun y : Fin 2 → ℝ => rmPlanar κ μ y 0)
      ((ContinuousLinearMap.proj 0).comp
        (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (rmJ κ μ)))) bary
    have hfun : (fun y : Fin 2 → ℝ => rmPlanar κ μ y 0)
        = fun y => κ*(y 0)^3 + κ*(y 0)^2*(y 1) + (-2*κ - 1)*(y 0)^2
          + κ*(y 0)*(y 1)^2 + (-2*κ - 2)*(y 0)*(y 1) + (κ - μ + 1)*(y 0) + μ/3 := by
      funext y; exact rmPlanar_comp0 κ μ y
    rw [hfun]
    have H1 := (h0.pow 3).const_mul κ
    have H2 := ((h0.pow 2).mul h1).const_mul κ
    have H3 := (h0.pow 2).const_mul (-2*κ - 1)
    have H4 := (h0.mul (h1.pow 2)).const_mul κ
    have H5 := (h0.mul h1).const_mul (-2*κ - 2)
    have H6 := h0.const_mul (κ - μ + 1)
    have H := (((((H1.add H2).add H3).add H4).add H5).add H6).add_const (μ/3)
    convert H using 1
    all_goals first
      | (funext y
         simp only [Pi.mul_apply, Pi.add_apply]
         ring)
      | (ext v
         simp [ContinuousLinearMap.comp_apply, Matrix.mulVecLin_apply,
           Matrix.mulVec, dotProduct, Fin.sum_univ_two, rmJ, hb0, hb1,
           Pi.mul_apply]
         push_cast
         ring)
  · -- component 1
    show HasFDerivAt (fun y : Fin 2 → ℝ => rmPlanar κ μ y 1)
      ((ContinuousLinearMap.proj 1).comp
        (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (rmJ κ μ)))) bary
    have hfun : (fun y : Fin 2 → ℝ => rmPlanar κ μ y 1)
        = fun y => κ*(y 0)^2*(y 1) + κ*(y 0)*(y 1)^2 + 2*((y 0)*(y 1))
          + κ*(y 1)^3 + (1 - κ)*(y 1)^2 + (-μ - 1)*(y 1) + μ/3 := by
      funext y; rw [rmPlanar_comp1]; ring
    rw [hfun]
    have H1 := ((h0.pow 2).mul h1).const_mul κ
    have H2 := (h0.mul (h1.pow 2)).const_mul κ
    have H3 := (h0.mul h1).const_mul (2 : ℝ)
    have H4 := (h1.pow 3).const_mul κ
    have H5 := (h1.pow 2).const_mul (1 - κ)
    have H6 := h1.const_mul (-μ - 1)
    have H := (((((H1.add H2).add H3).add H4).add H5).add H6).add_const (μ/3)
    convert H using 1
    all_goals first
      | (funext y
         simp only [Pi.mul_apply, Pi.add_apply]
         ring)
      | (ext v
         simp [ContinuousLinearMap.comp_apply, Matrix.mulVecLin_apply,
           Matrix.mulVec, dotProduct, Fin.sum_univ_two, rmJ, hb0, hb1,
           Pi.mul_apply]
         push_cast
         ring)

/-- Joint smoothness of the (reversed-parameter) planar family. -/
theorem rmPlanar_smooth_rev (μ κc : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin 2 → ℝ) => rmPlanar (2*κc - p.1) μ p.2) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · show ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin 2 → ℝ) => rmPlanar (2*κc - p.1) μ p.2 0)
    have hfun : (fun p : ℝ × (Fin 2 → ℝ) => rmPlanar (2*κc - p.1) μ p.2 0)
        = fun p => (2*κc - p.1)*(p.2 0)^3 + (2*κc - p.1)*(p.2 0)^2*(p.2 1)
          + (-2*(2*κc - p.1) - 1)*(p.2 0)^2 + (2*κc - p.1)*(p.2 0)*(p.2 1)^2
          + (-2*(2*κc - p.1) - 2)*(p.2 0)*(p.2 1)
          + ((2*κc - p.1) - μ + 1)*(p.2 0) + μ/3 := by
      funext p; exact rmPlanar_comp0 _ μ p.2
    rw [hfun]
    fun_prop
  · show ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin 2 → ℝ) => rmPlanar (2*κc - p.1) μ p.2 1)
    have hfun : (fun p : ℝ × (Fin 2 → ℝ) => rmPlanar (2*κc - p.1) μ p.2 1)
        = fun p => (2*κc - p.1)*(p.2 0)^2*(p.2 1) + (2*κc - p.1)*(p.2 0)*(p.2 1)^2
          + 2*(p.2 0)*(p.2 1) + (2*κc - p.1)*(p.2 1)^3
          + (1 - (2*κc - p.1))*(p.2 1)^2 + (-μ - 1)*(p.2 1) + μ/3 := by
      funext p; exact rmPlanar_comp1 _ μ p.2
    rw [hfun]
    fun_prop

/-! ### The conjugation to the rotation frame

At the genuine crossing locus `κ = −6μ` the Jacobian factors:
`rmJ (−6μ) μ = (1 − 3μ) · rmJ 0 0`, so ONE fixed matrix `P` conjugates it to
the rotation frame for every `μ`, with frequency `ω₀ = √3(1 − 3μ)/3`. -/

/-- Shorthand for `√3`. -/
noncomputable def sq3 : ℝ := Real.sqrt 3

theorem sq3_sq : sq3 * sq3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem sq3_pos : 0 < sq3 := Real.sqrt_pos.mpr (by norm_num)

/-- The conjugator (columns: `e₁` and the normalised image direction). -/
noncomputable def Pmat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -sq3/3; 0, 2*sq3/3]

/-- The explicit inverse of `Pmat` (uses `√3·√3 = 3`). -/
noncomputable def Qmat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1/2; 0, sq3/2]

theorem QP_one : Qmat * Pmat = 1 := by
  have h3 := sq3_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qmat, Pmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    nlinarith [h3]

theorem PQ_one : Pmat * Qmat = 1 := by
  have h3 := sq3_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qmat, Pmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    nlinarith [h3]

/-- The conjugacy `J(κc(μ)) · P = P · rotation ω₀` at the crossing locus. -/
theorem rmJ_conj (μ : ℝ) :
    rmJ (-6*μ) μ * Pmat = Pmat * rotation (sq3 * (1 - 3*μ) / 3) := by
  have h3 := sq3_sq
  have h3μ : μ * (sq3 * sq3) = 3 * μ := by rw [h3]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rmJ, Pmat, rotation, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [h3, h3μ]

/-! ### The machine-derived first Lyapunov number

`Wc μ` is the conjugated, shifted field at the critical parameter — the field
whose jet the repaired `ClassicalHopfStatement` inspects. -/

/-- The conjugated shifted field at criticality:
`W(z) = Q · rmPlanar(−6μ, μ)(P·z + bary)`. -/
noncomputable def Wc (μ : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  Qmat.mulVec (rmPlanar (-6*μ) μ (Pmat.mulVec z + bary))

/-- The affine inner map, computed componentwise. -/
private theorem inner_eq (z : Fin 2 → ℝ) :
    Pmat.mulVec z + bary
      = ![z 0 - sq3/3 * z 1 + 1/3, 2*sq3/3 * z 1 + 1/3] := by
  funext i
  fin_cases i <;>
    simp [Pmat, bary, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.add_apply] <;>
    ring

/-- `Wc` component 0, via the polynomial forms (avoids re-unfolding the
replicator field). -/
private theorem Wc_c0 (μ : ℝ) (z : Fin 2 → ℝ) :
    Wc μ z 0
      = rmPlanar (-6*μ) μ ![z 0 - sq3/3 * z 1 + 1/3, 2*sq3/3 * z 1 + 1/3] 0
        + 1/2 * rmPlanar (-6*μ) μ
            ![z 0 - sq3/3 * z 1 + 1/3, 2*sq3/3 * z 1 + 1/3] 1 := by
  show (Qmat.mulVec (rmPlanar (-6*μ) μ (Pmat.mulVec z + bary))) 0 = _
  rw [inner_eq]
  simp [Qmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `Wc` component 1. -/
private theorem Wc_c1 (μ : ℝ) (z : Fin 2 → ℝ) :
    Wc μ z 1
      = sq3/2 * rmPlanar (-6*μ) μ
          ![z 0 - sq3/3 * z 1 + 1/3, 2*sq3/3 * z 1 + 1/3] 1 := by
  show (Qmat.mulVec (rmPlanar (-6*μ) μ (Pmat.mulVec z + bary))) 1 = _
  rw [inner_eq]
  simp [Qmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Local cubic-derivative helper (same shape as the kernel's). -/
private theorem cubic_deriv (c3 c2 c1 c0 p : ℝ) :
    HasDerivAt (fun s => c3 * s ^ 3 + c2 * s ^ 2 + c1 * s + c0)
      (3 * c3 * p ^ 2 + 2 * c2 * p + c1) p := by
  have e1 : HasDerivAt (fun s : ℝ => c3 * s ^ 3) (3 * c3 * p ^ 2) p := by
    have := (hasDerivAt_pow 3 p).const_mul c3; convert this using 1
    push_cast; ring
  have e2 : HasDerivAt (fun s : ℝ => c2 * s ^ 2) (2 * c2 * p) p := by
    have := (hasDerivAt_pow 2 p).const_mul c2; convert this using 1
    push_cast; ring
  have e3 : HasDerivAt (fun s : ℝ => c1 * s) c1 p := by
    simpa using (hasDerivAt_id p).const_mul c1
  have e4 : HasDerivAt (fun s : ℝ => c0) (0 : ℝ) p := hasDerivAt_const p c0
  have h : HasDerivAt (fun s => c3 * s ^ 3 + c2 * s ^ 2 + c1 * s + c0)
      (3 * c3 * p ^ 2 + 2 * c2 * p + c1 + 0) p := (((e1.add e2).add e3).add e4)
  simpa using h

/-- Definitional unfoldings for the slice partials, used to rewrite ONLY the
outermost occurrence. -/
private theorem p1_eval (F : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    p1 F x = deriv (fun s => F ![s, x 1]) (x 0) := rfl

private theorem p2_eval (F : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    p2 F x = deriv (fun s => F ![x 0, s]) (x 1) := rfl

/-! #### Slice polynomials of `Wc` (coefficients exact in `√3`, no
`√3² = 3` reduction — every identity below is pure `ring`) -/

private theorem Wc0_slice_x (μ u : ℝ) :
    Wc μ ![u, 0] 0 = (-6*μ)*u^3 + (3*μ - 1)*u^2 + 0*u + 0 := by
  rw [Wc_c0, rmPlanar_comp0, rmPlanar_comp1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

private theorem Wc1_slice_x (μ u : ℝ) :
    Wc μ ![u, 0] 1 = 0*u^3 + (-μ*sq3)*u^2 + (sq3/3 - μ*sq3)*u + 0 := by
  rw [Wc_c1, rmPlanar_comp1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

private theorem Wc0_slice_y (μ s w : ℝ) :
    Wc μ ![s, w] 0
      = 0*w^3 + (sq3*sq3/3 - μ*(sq3*sq3) - 2*μ*s*(sq3*sq3))*w^2
        + (μ*sq3 - sq3/3 - 2*μ*s*sq3)*w
        + ((-6*μ)*s^3 + (3*μ - 1)*s^2) := by
  rw [Wc_c0, rmPlanar_comp0, rmPlanar_comp1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

private theorem Wc1_slice_y (μ s w : ℝ) :
    Wc μ ![s, w] 1
      = (-2*μ*(sq3*sq3)*(sq3*sq3)/3)*w^3 + (μ*(sq3*sq3)*sq3/3)*w^2
        + (2*s*(sq3*sq3)/3 - 2*μ*s^2*(sq3*sq3) - 2*μ*s*(sq3*sq3))*w
        + (s*sq3/3 - μ*s^2*sq3 - μ*s*sq3) := by
  rw [Wc_c1, rmPlanar_comp1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

private theorem Wc1_slice_xu (μ u w : ℝ) :
    Wc μ ![w, u] 1
      = 0*w^3 + (-2*μ*(sq3*sq3)*u - μ*sq3)*w^2
        + (2*(sq3*sq3)*u/3 + sq3/3 - 2*μ*(sq3*sq3)*u - μ*sq3)*w
        + (-2*μ*(sq3*sq3)*(sq3*sq3)*u^3/3 + μ*(sq3*sq3)*sq3*u^2/3) := by
  rw [Wc_c1, rmPlanar_comp1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-! #### The ten partials of `Wc` at the origin, by nested slice derivatives -/

private theorem f_p1_ax (μ s : ℝ) :
    p1 (fun z => Wc μ z 0) ![s, 0] = 3*(-6*μ)*s^2 + 2*(3*μ - 1)*s := by
  rw [p1_eval]
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  have hpoly : (fun u : ℝ => Wc μ ![u, 0] 0)
      = fun u => (-6*μ)*u^3 + (3*μ - 1)*u^2 + 0*u + 0 := by
    funext u; exact Wc0_slice_x μ u
  rw [hpoly, (cubic_deriv (-6*μ) (3*μ - 1) 0 0 s).deriv]
  ring

private theorem f_xx (μ : ℝ) :
    p1 (p1 (fun z => Wc μ z 0)) 0 = 2*(3*μ - 1) := by
  rw [p1_eval]
  simp only [Pi.zero_apply]
  have hpoly : (fun s : ℝ => p1 (fun z => Wc μ z 0) ![s, 0])
      = fun s => 0*s^3 + (3*(-6*μ))*s^2 + (2*(3*μ - 1))*s + 0 := by
    funext s; rw [f_p1_ax]; ring
  rw [hpoly, (cubic_deriv 0 (3*(-6*μ)) (2*(3*μ - 1)) 0 0).deriv]
  ring

private theorem f_xxx (μ : ℝ) :
    p1 (p1 (p1 (fun z => Wc μ z 0))) 0 = -36*μ := by
  rw [p1_eval]
  simp only [Pi.zero_apply]
  have hinner : (fun s : ℝ => p1 (p1 (fun z => Wc μ z 0)) ![s, 0])
      = fun s => 0*s^3 + 0*s^2 + (6*(-6*μ))*s + (2*(3*μ - 1)) := by
    funext s
    rw [p1_eval]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    have hpoly : (fun u : ℝ => p1 (fun z => Wc μ z 0) ![u, 0])
        = fun u => 0*u^3 + (3*(-6*μ))*u^2 + (2*(3*μ - 1))*u + 0 := by
      funext u; rw [f_p1_ax]; ring
    rw [hpoly, (cubic_deriv 0 (3*(-6*μ)) (2*(3*μ - 1)) 0 s).deriv]
    ring
  rw [hinner, (cubic_deriv 0 0 (6*(-6*μ)) (2*(3*μ - 1)) 0).deriv]
  ring

private theorem f_p2_su (μ s u : ℝ) :
    p2 (fun z => Wc μ z 0) ![s, u]
      = 2*(sq3*sq3/3 - μ*(sq3*sq3) - 2*μ*s*(sq3*sq3))*u
        + (μ*sq3 - sq3/3 - 2*μ*s*sq3) := by
  rw [p2_eval]
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  have hpoly : (fun w : ℝ => Wc μ ![s, w] 0)
      = fun w => 0*w^3 + (sq3*sq3/3 - μ*(sq3*sq3) - 2*μ*s*(sq3*sq3))*w^2
        + (μ*sq3 - sq3/3 - 2*μ*s*sq3)*w + ((-6*μ)*s^3 + (3*μ - 1)*s^2) := by
    funext w; exact Wc0_slice_y μ s w
  rw [hpoly, (cubic_deriv 0 (sq3*sq3/3 - μ*(sq3*sq3) - 2*μ*s*(sq3*sq3))
    (μ*sq3 - sq3/3 - 2*μ*s*sq3) ((-6*μ)*s^3 + (3*μ - 1)*s^2) u).deriv]
  ring

private theorem f_xy (μ : ℝ) :
    p1 (p2 (fun z => Wc μ z 0)) 0 = -2*μ*sq3 := by
  rw [p1_eval]
  simp only [Pi.zero_apply]
  have hpoly : (fun s : ℝ => p2 (fun z => Wc μ z 0) ![s, 0])
      = fun s => 0*s^3 + 0*s^2 + (-2*μ*sq3)*s + (μ*sq3 - sq3/3) := by
    funext s; rw [f_p2_su]; ring
  rw [hpoly, (cubic_deriv 0 0 (-2*μ*sq3) (μ*sq3 - sq3/3) 0).deriv]
  ring

private theorem f_yy (μ : ℝ) :
    p2 (p2 (fun z => Wc μ z 0)) 0 = 2*(sq3*sq3/3 - μ*(sq3*sq3)) := by
  rw [p2_eval]
  simp only [Pi.zero_apply]
  have hpoly : (fun u : ℝ => p2 (fun z => Wc μ z 0) ![0, u])
      = fun u => 0*u^3 + 0*u^2 + (2*(sq3*sq3/3 - μ*(sq3*sq3)))*u
          + (μ*sq3 - sq3/3) := by
    funext u; rw [f_p2_su]; ring
  rw [hpoly, (cubic_deriv 0 0 (2*(sq3*sq3/3 - μ*(sq3*sq3))) (μ*sq3 - sq3/3) 0).deriv]
  ring

private theorem f_xyy (μ : ℝ) :
    p1 (p2 (p2 (fun z => Wc μ z 0))) 0 = -4*μ*(sq3*sq3) := by
  rw [p1_eval]
  simp only [Pi.zero_apply]
  have hinner : (fun s : ℝ => p2 (p2 (fun z => Wc μ z 0)) ![s, 0])
      = fun s => 0*s^3 + 0*s^2 + (-4*μ*(sq3*sq3))*s
          + (2*(sq3*sq3/3 - μ*(sq3*sq3))) := by
    funext s
    rw [p2_eval]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    have hpoly : (fun u : ℝ => p2 (fun z => Wc μ z 0) ![s, u])
        = fun u => 0*u^3 + 0*u^2
            + (2*(sq3*sq3/3 - μ*(sq3*sq3) - 2*μ*s*(sq3*sq3)))*u
            + (μ*sq3 - sq3/3 - 2*μ*s*sq3) := by
      funext u; rw [f_p2_su]; ring
    rw [hpoly, (cubic_deriv 0 0
      (2*(sq3*sq3/3 - μ*(sq3*sq3) - 2*μ*s*(sq3*sq3)))
      (μ*sq3 - sq3/3 - 2*μ*s*sq3) 0).deriv]
    ring
  rw [hinner, (cubic_deriv 0 0 (-4*μ*(sq3*sq3))
    (2*(sq3*sq3/3 - μ*(sq3*sq3))) 0).deriv]
  ring

private theorem g_p1_ax (μ s : ℝ) :
    p1 (fun z => Wc μ z 1) ![s, 0] = 2*(-μ*sq3)*s + (sq3/3 - μ*sq3) := by
  rw [p1_eval]
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  have hpoly : (fun u : ℝ => Wc μ ![u, 0] 1)
      = fun u => 0*u^3 + (-μ*sq3)*u^2 + (sq3/3 - μ*sq3)*u + 0 := by
    funext u; exact Wc1_slice_x μ u
  rw [hpoly, (cubic_deriv 0 (-μ*sq3) (sq3/3 - μ*sq3) 0 s).deriv]
  ring

private theorem g_xx (μ : ℝ) :
    p1 (p1 (fun z => Wc μ z 1)) 0 = -2*μ*sq3 := by
  rw [p1_eval]
  simp only [Pi.zero_apply]
  have hpoly : (fun s : ℝ => p1 (fun z => Wc μ z 1) ![s, 0])
      = fun s => 0*s^3 + 0*s^2 + (2*(-μ*sq3))*s + (sq3/3 - μ*sq3) := by
    funext s; rw [g_p1_ax]; ring
  rw [hpoly, (cubic_deriv 0 0 (2*(-μ*sq3)) (sq3/3 - μ*sq3) 0).deriv]
  ring

private theorem g_p1_su (μ s u : ℝ) :
    p1 (fun z => Wc μ z 1) ![s, u]
      = 2*(-2*μ*(sq3*sq3)*u - μ*sq3)*s
        + (2*(sq3*sq3)*u/3 + sq3/3 - 2*μ*(sq3*sq3)*u - μ*sq3) := by
  rw [p1_eval]
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  have hpoly : (fun w : ℝ => Wc μ ![w, u] 1)
      = fun w => 0*w^3 + (-2*μ*(sq3*sq3)*u - μ*sq3)*w^2
        + (2*(sq3*sq3)*u/3 + sq3/3 - 2*μ*(sq3*sq3)*u - μ*sq3)*w
        + (-2*μ*(sq3*sq3)*(sq3*sq3)*u^3/3 + μ*(sq3*sq3)*sq3*u^2/3) := by
    funext w; exact Wc1_slice_xu μ u w
  rw [hpoly, (cubic_deriv 0 (-2*μ*(sq3*sq3)*u - μ*sq3)
    (2*(sq3*sq3)*u/3 + sq3/3 - 2*μ*(sq3*sq3)*u - μ*sq3)
    (-2*μ*(sq3*sq3)*(sq3*sq3)*u^3/3 + μ*(sq3*sq3)*sq3*u^2/3) s).deriv]
  ring

private theorem g_xxy (μ : ℝ) :
    p2 (p1 (p1 (fun z => Wc μ z 1))) 0 = -4*μ*(sq3*sq3) := by
  rw [p2_eval]
  simp only [Pi.zero_apply]
  have hinner : (fun u : ℝ => p1 (p1 (fun z => Wc μ z 1)) ![0, u])
      = fun u => 0*u^3 + 0*u^2 + (-4*μ*(sq3*sq3))*u + (-2*μ*sq3) := by
    funext u
    rw [p1_eval]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    have hpoly : (fun s : ℝ => p1 (fun z => Wc μ z 1) ![s, u])
        = fun s => 0*s^3 + 0*s^2 + (2*(-2*μ*(sq3*sq3)*u - μ*sq3))*s
            + (2*(sq3*sq3)*u/3 + sq3/3 - 2*μ*(sq3*sq3)*u - μ*sq3) := by
      funext s; rw [g_p1_su]; ring
    rw [hpoly, (cubic_deriv 0 0 (2*(-2*μ*(sq3*sq3)*u - μ*sq3))
      (2*(sq3*sq3)*u/3 + sq3/3 - 2*μ*(sq3*sq3)*u - μ*sq3) 0).deriv]
    ring
  rw [hinner, (cubic_deriv 0 0 (-4*μ*(sq3*sq3)) (-2*μ*sq3) 0).deriv]
  ring

private theorem g_p2_su (μ s u : ℝ) :
    p2 (fun z => Wc μ z 1) ![s, u]
      = 3*(-2*μ*(sq3*sq3)*(sq3*sq3)/3)*u^2 + 2*(μ*(sq3*sq3)*sq3/3)*u
        + (2*s*(sq3*sq3)/3 - 2*μ*s^2*(sq3*sq3) - 2*μ*s*(sq3*sq3)) := by
  rw [p2_eval]
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  have hpoly : (fun w : ℝ => Wc μ ![s, w] 1)
      = fun w => (-2*μ*(sq3*sq3)*(sq3*sq3)/3)*w^3 + (μ*(sq3*sq3)*sq3/3)*w^2
        + (2*s*(sq3*sq3)/3 - 2*μ*s^2*(sq3*sq3) - 2*μ*s*(sq3*sq3))*w
        + (s*sq3/3 - μ*s^2*sq3 - μ*s*sq3) := by
    funext w; exact Wc1_slice_y μ s w
  rw [hpoly, (cubic_deriv (-2*μ*(sq3*sq3)*(sq3*sq3)/3) (μ*(sq3*sq3)*sq3/3)
    (2*s*(sq3*sq3)/3 - 2*μ*s^2*(sq3*sq3) - 2*μ*s*(sq3*sq3))
    (s*sq3/3 - μ*s^2*sq3 - μ*s*sq3) u).deriv]

private theorem g_xy (μ : ℝ) :
    p1 (p2 (fun z => Wc μ z 1)) 0 = 2*(sq3*sq3)/3 - 2*μ*(sq3*sq3) := by
  rw [p1_eval]
  simp only [Pi.zero_apply]
  have hpoly : (fun s : ℝ => p2 (fun z => Wc μ z 1) ![s, 0])
      = fun s => 0*s^3 + (-2*μ*(sq3*sq3))*s^2
          + (2*(sq3*sq3)/3 - 2*μ*(sq3*sq3))*s + 0 := by
    funext s; rw [g_p2_su]; ring
  rw [hpoly, (cubic_deriv 0 (-2*μ*(sq3*sq3))
    (2*(sq3*sq3)/3 - 2*μ*(sq3*sq3)) 0 0).deriv]
  ring

private theorem g_yy (μ : ℝ) :
    p2 (p2 (fun z => Wc μ z 1)) 0 = 2*(μ*(sq3*sq3)*sq3/3) := by
  rw [p2_eval]
  simp only [Pi.zero_apply]
  have hpoly : (fun u : ℝ => p2 (fun z => Wc μ z 1) ![0, u])
      = fun u => 0*u^3 + (3*(-2*μ*(sq3*sq3)*(sq3*sq3)/3))*u^2
          + (2*(μ*(sq3*sq3)*sq3/3))*u + 0 := by
    funext u; rw [g_p2_su]; ring
  rw [hpoly, (cubic_deriv 0 (3*(-2*μ*(sq3*sq3)*(sq3*sq3)/3))
    (2*(μ*(sq3*sq3)*sq3/3)) 0 0).deriv]
  ring

private theorem g_yyy (μ : ℝ) :
    p2 (p2 (p2 (fun z => Wc μ z 1))) 0 = -4*μ*(sq3*sq3)*(sq3*sq3) := by
  rw [p2_eval]
  simp only [Pi.zero_apply]
  have hinner : (fun u : ℝ => p2 (p2 (fun z => Wc μ z 1)) ![0, u])
      = fun u => 0*u^3 + 0*u^2 + (-4*μ*(sq3*sq3)*(sq3*sq3))*u
          + (2*(μ*(sq3*sq3)*sq3/3)) := by
    funext u
    rw [p2_eval]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    have hpoly : (fun w : ℝ => p2 (fun z => Wc μ z 1) ![0, w])
        = fun w => 0*w^3 + (3*(-2*μ*(sq3*sq3)*(sq3*sq3)/3))*w^2
            + (2*(μ*(sq3*sq3)*sq3/3))*w + 0 := by
      funext w; rw [g_p2_su]; ring
    rw [hpoly, (cubic_deriv 0 (3*(-2*μ*(sq3*sq3)*(sq3*sq3)/3))
      (2*(μ*(sq3*sq3)*sq3/3)) 0 u).deriv]
    ring
  rw [hinner, (cubic_deriv 0 0 (-4*μ*(sq3*sq3)*(sq3*sq3))
    (2*(μ*(sq3*sq3)*sq3/3)) 0).deriv]
  ring

/-- **The machine-derived first Lyapunov number.**  The G–H (3.4.11) value of
the conjugated replicator–mutator field at the crossing locus is the exact
rational identity `ℓ₁ = μ·(−t⁴ − 2t² − 9)/4` with `t = √3` — no `t² = 3`
reduction is even needed for the identity; reducing gives `ℓ₁ = −6μ`. -/
theorem ell1_Wc (μ : ℝ) (h13 : μ < 1/3) :
    ell1At (Wc μ) (sq3 * (1 - 3*μ) / 3)
      = μ * (-(sq3*sq3)*(sq3*sq3) - 2*(sq3*sq3) - 9) / 4 := by
  have h1 : 0 < 1 - 3*μ := by linarith
  have hω : sq3 * (1 - 3*μ) / 3 ≠ 0 := by
    have := sq3_pos
    positivity
  simp only [ell1At]
  rw [f_xxx, f_xyy, g_xxy, g_yyy, f_xy, f_xx, f_yy, g_xy, g_xx, g_yy]
  field_simp
  ring

/-- **Supercriticality, machine-derived:** `ℓ₁ < 0` for every `μ ∈ (0, 1/3)`.
Unlike the transcribed `firstLyapunov_neg` (a sign fact about the paper's
printed formula), this inequality is DERIVED from the field itself. -/
theorem ell1_Wc_neg {μ : ℝ} (h0 : 0 < μ) (h13 : μ < 1/3) :
    ell1At (Wc μ) (sq3 * (1 - 3*μ) / 3) < 0 := by
  rw [ell1_Wc μ h13]
  have h1 : 0 < (sq3*sq3)*(sq3*sq3) + 2*(sq3*sq3) + 9 := by
    nlinarith [sq3_sq]
  nlinarith [h1, h0]

/-! ### The degenerate point: `κ = 0, μ = 0` is a center, not a generic Hopf

The AQ-20 narrative placed "the true Hopf" at `κ = 0` (the γ = 1 boundary).
The eigenvalue pair does cross there (`rm_true_hopf`), but the first
Lyapunov number VANISHES at `μ = 0`: the pure-RPS replicator conserves
`x₀x₁x₂` and the barycentre is a center — a degenerate Hopf.  The value
below is the `μ → 0` limit of `ell1_Wc`; the crossing at `κ = 0, μ = 0`
therefore fails the supercriticality hypothesis of the (repaired) classical
statement, and the genuine generic Hopf lives on `κ = −6μ`, `μ > 0`. -/
theorem ell1_pureRPS_zero :
    ell1At (Wc 0) (sq3 * (1 - 3*0) / 3) = 0 := by
  rw [ell1_Wc 0 (by norm_num)]
  ring

/-! ### The family, and Law 7 discharged for the canonical model -/

/-- The reversed-parameter family around `κc = −6μ` (reversal orients the
transversal crossing in the `+` direction required by the classical
statement; orbits transfer back by a parameter flip). -/
noncomputable def rmFamRev (μ : ℝ) : HopfFamily where
  V κ := rmPlanar (2*(-6*μ) - κ) μ
  equilibrium _ := bary
  isEquil κ := rmPlanar_bary _ μ
  J κ := rmJ (2*(-6*μ) - κ) μ
  hasJac κ := rmPlanar_hasJac _ μ
  smooth := rmPlanar_smooth_rev μ (-6*μ)
  eqSmooth := contDiff_const

/-- **Law 7 for the canonical replicator–mutator, conditional only on the
classical Hopf theorem.**  For every mutation rate `μ ∈ (0, 1/3)`, the
biased-RPS replicator–mutator undergoes a supercritical Hopf bifurcation at
the bias threshold `κ = −6μ`: nonconstant periodic orbits exist for every
bias just below threshold.  Every side condition — equilibrium branch, true
Jacobian, joint smoothness, rotation-frame conjugacy, transversality, and
the sign of the machine-derived first Lyapunov number — is discharged; the
ONLY remaining input is `ClassicalHopfStatement` itself. -/
theorem rm_supercritical_hopf
    (classical_hopf : ClassicalHopfStatement)
    {μ : ℝ} (h0 : 0 < μ) (h13 : μ < 1/3) :
    ∃ ε > 0, ∀ κ, -6*μ - ε < κ → κ < -6*μ →
      ∃ y T, IsPeriodicOrbit (rmPlanar κ μ) y T := by
  have hω : 0 < sq3 * (1 - 3*μ) / 3 := by
    have h1 : 0 < 1 - 3*μ := by linarith
    have := sq3_pos
    positivity
  -- rotation-frame conjugacy for the reversed family at κc = −6μ
  have hconj : (rmFamRev μ).J (-6*μ) * Pmat
      = Pmat * rotation (sq3 * (1 - 3*μ) / 3) := by
    show rmJ (2*(-6*μ) - (-6*μ)) μ * Pmat = _
    have harg : 2*(-6*μ) - (-6*μ) = -6*μ := by ring
    rw [harg]
    exact rmJ_conj μ
  -- transversal trace crossing with positive slope for the reversed family
  have htrans : ∃ a', HasDerivAt (fun κ => ((rmFamRev μ).J κ).trace) a' (-6*μ)
      ∧ 0 < a' := by
    refine ⟨1/3, ?_, by norm_num⟩
    have hfun : (fun κ => ((rmFamRev μ).J κ).trace)
        = fun κ => κ/3 + 2*μ := by
      funext κ
      show (rmJ (2*(-6*μ) - κ) μ).trace = _
      rw [rmJ, Matrix.trace_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      ring
    rw [hfun]
    simpa using ((hasDerivAt_id (-6*μ : ℝ)).div_const 3).add_const (2*μ)
  -- the ℓ₁ hypothesis for the reversed family is the derived value
  have hℓ₁ : ell1At (fun z => Qmat.mulVec
      ((rmFamRev μ).V (-6*μ) (Pmat.mulVec z + (rmFamRev μ).equilibrium (-6*μ))))
      (sq3 * (1 - 3*μ) / 3) < 0 := by
    have hV : (fun z => Qmat.mulVec
        ((rmFamRev μ).V (-6*μ) (Pmat.mulVec z + (rmFamRev μ).equilibrium (-6*μ))))
        = Wc μ := by
      funext z
      show Qmat.mulVec (rmPlanar (2*(-6*μ) - (-6*μ)) μ (Pmat.mulVec z + bary)) = _
      have harg : 2*(-6*μ) - (-6*μ) = -6*μ := by ring
      rw [harg]
      rfl
    rw [hV]
    exact ell1_Wc_neg h0 h13
  obtain ⟨ε, hε, horb⟩ := hopf_transition_conditional classical_hopf
    (rmFamRev μ) (-6*μ) (sq3 * (1 - 3*μ) / 3) hω Pmat Qmat QP_one PQ_one
    hconj htrans hℓ₁
  refine ⟨ε, hε, fun κ h1 h2 => ?_⟩
  obtain ⟨y, T, hy⟩ := horb (2*(-6*μ) - κ) (by linarith) (by linarith)
  refine ⟨y, T, ?_⟩
  have hVκ : (rmFamRev μ).V (2*(-6*μ) - κ) = rmPlanar κ μ := by
    show rmPlanar (2*(-6*μ) - (2*(-6*μ) - κ)) μ = rmPlanar κ μ
    have harg : 2*(-6*μ) - (2*(-6*μ) - κ) = κ := by ring
    rw [harg]
  rwa [hVκ] at hy

end Law7
end SEKernel
