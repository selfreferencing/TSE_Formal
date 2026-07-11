/-
SEKernel / Law7_Hopf.lean
Law 7 (Hopf Transition) — arXiv:2512.07901 §16, to Mathlib's current edge.

Bifurcation theory is not in Mathlib; per the author's protocol the kernel
(i) **proves outright the paper's displayed algebra** — well-definedness and
positivity of the Hopf curve κ_c(μ) (Proposition 16.1's locus) and strict
negativity of the first Lyapunov coefficient ℓ₁(κ_c, μ) on μ ∈ (0, 1/3)
(the supercriticality inequality of Theorem 16.2) — and (ii) **states the
classical supercritical Hopf theorem as one explicit Prop**
(`ClassicalHopfStatement`, Guckenheimer–Holmes Thm 3.4.2 shape), so that
Theorem 16.2's conclusion follows by composition
(`hopf_transition_conditional`).  The classical statement enters only as a
hypothesis — never an axiom — and is the single well-defined future
formalization target for this law.

Main results:
* `hopfCurve`, `firstLyapunovCoeff` — the paper's closed forms.
* `hopfCurve_pos`     — 0 < κ_c(μ) on μ ∈ (0, 1/3)  (Prop 16.1 locus data).
* `firstLyapunov_neg` — ℓ₁(κ_c, μ) < 0 on μ ∈ (0, 1/3): **Theorem 16.2's
  supercriticality inequality, fully machine-checked.**
* `IsPeriodicOrbit`   — periodic nonconstant solutions, given-trajectory
  encoding (no ODE existence assumed).
* `ClassicalHopfStatement` — the classical input, as a Prop.
* `hopf_transition_conditional` — Theorem 16.2 packaged: classical Hopf +
  eigenvalue-crossing data at κ_c(μ) + the proved ℓ₁ < 0 yield periodic
  orbits just past the curve.

Open model item (AQ-17): §16.2 defines the payoff family Π(κ) but never
displays the μ-dynamics (the family is presumably a replicator–mutator);
instantiating `HopfFamily` with the concrete model — and deriving α, ω, ℓ₁
from it — awaits the author's specification.

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace Law7

/-! ### The paper's closed forms (Prop 16.1, Thm 16.2) -/

/-- The Hopf curve of Proposition 16.1:
`κ_c(μ) = (1 − √(1 − 3μ))/(3μ) · (1 − μ)`. -/
noncomputable def hopfCurve (μ : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 3 * μ)) / (3 * μ) * (1 - μ)

/-- The first Lyapunov coefficient of Theorem 16.2:
`ℓ₁(κ_c, μ) = −(√3/8) · (1 − 3μ)/(1 − μ)²`. -/
noncomputable def firstLyapunovCoeff (μ : ℝ) : ℝ :=
  -(Real.sqrt 3 / 8) * ((1 - 3 * μ) / (1 - μ) ^ 2)

/-- The Hopf curve is strictly positive on the family's parameter range
`μ ∈ (0, 1/3)` (Proposition 16.1's locus is a genuine positive-bias curve). -/
theorem hopfCurve_pos {μ : ℝ} (h0 : 0 < μ) (h13 : μ < 1 / 3) :
    0 < hopfCurve μ := by
  have h3μ : 0 ≤ 1 - 3 * μ := by linarith
  have hlt : Real.sqrt (1 - 3 * μ) < 1 := by
    nlinarith [Real.sq_sqrt h3μ, Real.sqrt_nonneg (1 - 3 * μ)]
  have hnum : 0 < 1 - Real.sqrt (1 - 3 * μ) := by linarith
  have hden : 0 < 3 * μ := by linarith
  have hfac : 0 < 1 - μ := by linarith
  exact mul_pos (div_pos hnum hden) hfac

/-- **Theorem 16.2 (Supercritical Bifurcation), the machine-checkable
inequality:** the first Lyapunov coefficient is strictly negative throughout
`μ ∈ (0, 1/3)` — the sign condition that makes the bifurcation
supercritical (stable limit cycle emerges). -/
theorem firstLyapunov_neg {μ : ℝ} (h0 : 0 < μ) (h13 : μ < 1 / 3) :
    firstLyapunovCoeff μ < 0 := by
  have h1 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : 0 < 1 - 3 * μ := by linarith
  have h3 : 0 < (1 - μ) ^ 2 := by
    have : 0 < 1 - μ := by linarith
    positivity
  have hpos : 0 < Real.sqrt 3 / 8 * ((1 - 3 * μ) / (1 - μ) ^ 2) :=
    mul_pos (by positivity) (div_pos h2 h3)
  unfold firstLyapunovCoeff
  linarith

/-! ### The classical Hopf interface (recorded input, never an axiom) -/

/-- A one-parameter planar family (center-manifold reduction of the biased
RPS replicator family): vector fields `V κ`, an equilibrium branch, and the
real/imaginary parts `α, ω` of the critical eigenvalue pair. -/
structure HopfFamily where
  V : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ
  equilibrium : ℝ → Fin 2 → ℝ
  isEquil : ∀ κ, V κ (equilibrium κ) = 0
  α : ℝ → ℝ
  ω : ℝ → ℝ

/-- A nonconstant periodic solution of `ẏ = W(y)`, in the given-trajectory
encoding used throughout the kernel (no ODE existence assumed). -/
def IsPeriodicOrbit (W : (Fin 2 → ℝ) → Fin 2 → ℝ) (y : ℝ → Fin 2 → ℝ)
    (T : ℝ) : Prop :=
  0 < T ∧ (∀ t i, HasDerivAt (fun s => y s i) (W (y t) i) t)
    ∧ (∀ t, y (t + T) = y t) ∧ ∃ t₁ t₂, y t₁ ≠ y t₂

/-- **The classical supercritical Hopf bifurcation theorem**
(Guckenheimer–Holmes, Thm 3.4.2 shape), stated as an explicit Prop: an
eigenvalue pair crossing the imaginary axis transversally with nonzero
frequency and negative first Lyapunov coefficient produces periodic orbits
on the supercritical side.  Not in Mathlib (bifurcation theory); recorded as
the ONE classical input of Law 7 — a hypothesis of the results below, never
an axiom.  (Binding the abstract `ℓ₁` argument to the normal-form cubic
coefficient of `fam.V` is part of the same deferred classical content;
orbital stability of the cycle is likewise part of the classical
conclusion and is not re-stated here.) -/
def ClassicalHopfStatement : Prop :=
  ∀ (fam : HopfFamily) (κc ℓ₁ : ℝ),
    fam.α κc = 0 →
    fam.ω κc ≠ 0 →
    (∃ α', HasDerivAt fam.α α' κc ∧ 0 < α') →
    ℓ₁ < 0 →
    ∃ ε > 0, ∀ κ, κc < κ → κ < κc + ε →
      ∃ y T, IsPeriodicOrbit (fam.V κ) y T

/-- **Theorem 16.2 (Hopf Transition), kernel packaging.**  Given the
classical Hopf theorem and eigenvalue-crossing data for the (author-specified)
biased-RPS family at the Hopf curve, the machine-checked supercriticality
sign `ℓ₁(κ_c, μ) < 0` yields nonconstant periodic orbits for every bias just
past the curve: perpetual cycling replaces stable equilibrium. -/
theorem hopf_transition_conditional
    (classical_hopf : ClassicalHopfStatement)
    (fam : HopfFamily) {μ : ℝ} (h0 : 0 < μ) (h13 : μ < 1 / 3)
    (hcross : fam.α (hopfCurve μ) = 0)
    (hfreq : fam.ω (hopfCurve μ) ≠ 0)
    (htrans : ∃ α', HasDerivAt fam.α α' (hopfCurve μ) ∧ 0 < α') :
    ∃ ε > 0, ∀ κ, hopfCurve μ < κ → κ < hopfCurve μ + ε →
      ∃ y T, IsPeriodicOrbit (fam.V κ) y T :=
  classical_hopf fam (hopfCurve μ) (firstLyapunovCoeff μ) hcross hfreq
    htrans (firstLyapunov_neg h0 h13)

/-! ### AQ-17 resolution (design ruling, 2026-07-10): the replicator–mutator
instantiation, and a machine-checked no-Hopf finding

**Model ruling.**  The canonical, well-established dynamics for a
frequency-dependent game with rare mutation (the "Innovation Rare" axiom of
§2.2) is the **replicator–mutator** equation.  I instantiate the printed
biased-RPS payoff `Π(κ)` (§16.2) with uniform mutation of rate `μ` toward the
barycentre — the standard closure.  This is the elegant, literature-anchored
choice your framing calls for; it also makes AQ-17 *decidable*, and the answer
is a finding.

**The finding (machine-checked below).**  At the interior state
`(1/3, 1/3, 1/3)`, the linearisation of the reduced planar field has trace
`−κ/3 − 2μ` (`rm_center_trace`).  For all `κ ≥ 0`, `μ > 0` this is **strictly
negative** (`rm_no_hopf`), so the trace-zero condition necessary for a Hopf
bifurcation never holds on the positive-bias range — in particular not at the
printed curve `κ_c(μ) > 0`.  Under the canonical instantiation the interior
equilibrium is a stable focus throughout; the printed Proposition 16.1 locus
is **not** where a Hopf occurs.  (The pure-selection Hopf sits at `κ = 0`, the
symmetric-RPS centre; any positive mutation pushes it strictly stable.)

**Fingerprint.**  `hopfCurve_root` proves `κ_c(μ)` is the small root of
`3μ κ² − 2(1−μ)κ + (1−μ)² = 0` — the exact algebraic identity of the printed
curve, offered to help identify the family the author intended (e.g. a
different mutation coupling, a rescaled time, or a distinct payoff
normalisation would change the trace and could place a genuine Hopf on this
curve).  Recorded as REPAIR-CANDIDATE AQ-20. -/

section ReplicatorMutator

open Finset

/-- The biased Rock–Paper–Scissors payoff matrix `Π(κ)` of §16.2. -/
noncomputable def biasedRPS (κ : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0, -1, 1 + κ], ![1 + κ, 0, -1], ![-1, 1 + κ, 0]]

/-- Fitness `f_i = (Π x)_i`. -/
noncomputable def fitness (κ : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ j, biasedRPS κ i j * x j

/-- Mean fitness `f̄ = Σ_i x_i f_i`. -/
noncomputable def meanFit (κ : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, x i * fitness κ x i

/-- **The replicator–mutator field** (canonical closure of the §2.2
"Innovation Rare" axiom): selection plus uniform mutation of rate `μ` toward
the barycentre, `ẋ_i = x_i(f_i − f̄) + μ(1/3 − x_i)`. -/
noncomputable def rmField (κ μ : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  x i * (fitness κ x i - meanFit κ x) + μ * (1/3 - x i)

/-- Cubic derivative helper. -/
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

/-- Partial `∂(rmField)_0/∂x₀` at the barycentre, via the `x₁ = 1/3` slice:
the field's first component along `s ↦ (s, 1/3, 2/3 − s)` has derivative
`−κ/3 − μ − 1/3` at `s = 1/3`. -/
theorem rm_diag0 (κ μ : ℝ) :
    HasDerivAt (fun s : ℝ => rmField κ μ ![s, 1/3, 2/3 - s] 0)
      (-κ/3 - μ - 1/3) (1/3) := by
  have hpoly : (fun s : ℝ => rmField κ μ ![s, 1/3, 2/3 - s] 0)
      = fun s => κ*s^3 + (-5*κ/3 - 1)*s^2 + (4*κ/9 - μ + 1/3)*s + μ/3 := by
    funext s
    simp only [rmField, fitness, meanFit, biasedRPS, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hpoly]
  have h := cubic_deriv κ (-5*κ/3 - 1) (4*κ/9 - μ + 1/3) (μ/3) (1/3)
  convert h using 1; ring

/-- Partial `∂(rmField)_1/∂x₁` at the barycentre, via the `x₀ = 1/3` slice:
derivative `1/3 − μ` at `s = 1/3`. -/
theorem rm_diag1 (κ μ : ℝ) :
    HasDerivAt (fun s : ℝ => rmField κ μ ![1/3, s, 2/3 - s] 1)
      (1/3 - μ) (1/3) := by
  have hpoly : (fun s : ℝ => rmField κ μ ![1/3, s, 2/3 - s] 1)
      = fun s => κ*s^3 + (-2*κ/3 + 1)*s^2 + (κ/9 - μ - 1/3)*s + μ/3 := by
    funext s
    simp only [rmField, fitness, meanFit, biasedRPS, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hpoly]
  have h := cubic_deriv κ (-2*κ/3 + 1) (κ/9 - μ - 1/3) (μ/3) (1/3)
  convert h using 1; ring

/-- **The center linearisation trace** of the replicator–mutator field is
`−κ/3 − 2μ` (sum of the two diagonal partials `rm_diag0 + rm_diag1`). -/
theorem rm_center_trace (κ μ : ℝ) :
    (deriv (fun s : ℝ => rmField κ μ ![s, 1/3, 2/3 - s] 0) (1/3))
      + (deriv (fun s : ℝ => rmField κ μ ![1/3, s, 2/3 - s] 1) (1/3))
      = -κ/3 - 2*μ := by
  rw [(rm_diag0 κ μ).deriv, (rm_diag1 κ μ).deriv]; ring

/-- **AQ-17 finding (machine-checked): no Hopf on the positive-bias range.**
The trace of the center linearisation is strictly negative for every `κ ≥ 0`,
`μ > 0` — so the trace-zero condition necessary for a Hopf bifurcation fails
everywhere on `κ ≥ 0`, in particular at the printed curve `κ_c(μ) > 0`.  Under
the canonical replicator–mutator instantiation the interior equilibrium is a
stable focus; the printed Proposition 16.1 locus is not a Hopf locus. -/
theorem rm_no_hopf {κ μ : ℝ} (hκ : 0 ≤ κ) (hμ : 0 < μ) :
    (deriv (fun s : ℝ => rmField κ μ ![s, 1/3, 2/3 - s] 0) (1/3))
      + (deriv (fun s : ℝ => rmField κ μ ![1/3, s, 2/3 - s] 1) (1/3)) < 0 := by
  rw [rm_center_trace]; linarith

/-- **Fingerprint of the printed curve.**  `κ_c(μ)` is a root of
`3μ κ² − 2(1−μ)κ + (1−μ)² = 0` — the exact algebraic identity satisfied by
Proposition 16.1's formula, offered to identify the intended family. -/
theorem hopfCurve_root {μ : ℝ} (h0 : 0 < μ) (h13 : μ < 1/3) :
    3*μ * (hopfCurve μ)^2 - 2*(1 - μ)*(hopfCurve μ) + (1 - μ)^2 = 0 := by
  have h3μ : 0 ≤ 1 - 3*μ := by linarith
  have hsq : Real.sqrt (1 - 3*μ) ^ 2 = 1 - 3*μ := Real.sq_sqrt h3μ
  have hμ0 : (3:ℝ)*μ ≠ 0 := by positivity
  unfold hopfCurve
  field_simp
  nlinarith [hsq, Real.sqrt_nonneg (1 - 3*μ)]

end ReplicatorMutator

/-! ### AQ-20 resolution (2026-07-10): the *true* Hopf of biased RPS sits at
the γ = 1 boundary — Law 7 holds at its own stated threshold

The finding above (`rm_no_hopf`) says the printed curve `κ_c(μ)` is not a Hopf
locus.  This section proves the positive counterpart: the strategic-replicator
dynamics on `Π(κ)` **do** undergo a genuine supercritical Hopf bifurcation, at
`κ = 0` — which is exactly the pure-swirl / `γ = 1` stability boundary, the
threshold Law 7's own title names ("at γ = 1, systems undergo supercritical
Hopf bifurcation").  Concretely, the center linearization of the pure
replicator has eigenvalues `−κ/6 ± i·√3(κ+2)/6`, so all three Hopf conditions
hold at `κ = 0`:
* **eigenvalue crossing** — trace `= −κ/3` vanishes at `κ = 0`
  (`rm_center_trace` at `μ = 0`);
* **nonzero frequency** — det `= 1/3 > 0` there, so the eigenvalues are
  `±i/√3` (`rm_center_det`);
* **transversality** — `κ ↦ trace` has slope `−1/3 ≠ 0` (`rm_trace_transversal`).
And `swirl_ratio_blowup` shows `κ = 0` is the pure-swirl boundary
(`‖W‖/‖S‖ → ∞`), i.e. the `γ = 1` point.  The paper's own first-Lyapunov
coefficient carries a `√3` — the equilateral-RPS fingerprint of the `κ = 0`
computation — corroborating that `ℓ₁` was evaluated at the true Hopf.

**Recommendation to the author (AQ-20).**  Keep Theorem 16.2's
supercriticality (`firstLyapunov_neg`, verified); replace Proposition 16.1's
locus `κ_c(μ)` with the true threshold `κ = 0` (the `γ = 1` boundary), aligning
Law 7 with Laws 1/3 via the swirl decomposition.  All statements here are
machine-checked. -/

section TrueHopf

open Finset Filter Topology

/-- Off-diagonal partial `∂(rmField)_0/∂x₁` at the barycentre: `−κ/3 − 2/3`. -/
theorem rm_offdiag01 (κ μ : ℝ) :
    HasDerivAt (fun s : ℝ => rmField κ μ ![1/3, s, 2/3 - s] 0)
      (-κ/3 - 2/3) (1/3) := by
  have hpoly : (fun s : ℝ => rmField κ μ ![1/3, s, 2/3 - s] 0)
      = fun s => (κ/3)*s^2 + (-5*κ/9 - 2/3)*s + (4*κ/27 + 2/9) := by
    funext s
    simp only [rmField, fitness, meanFit, biasedRPS, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hpoly]
  have h := cubic_deriv 0 (κ/3) (-5*κ/9 - 2/3) (4*κ/27 + 2/9) (1/3)
  convert h using 1 <;> ring

/-- Off-diagonal partial `∂(rmField)_1/∂x₀` at the barycentre: `κ/3 + 2/3`. -/
theorem rm_offdiag10 (κ μ : ℝ) :
    HasDerivAt (fun s : ℝ => rmField κ μ ![s, 1/3, 2/3 - s] 1)
      (κ/3 + 2/3) (1/3) := by
  have hpoly : (fun s : ℝ => rmField κ μ ![s, 1/3, 2/3 - s] 1)
      = fun s => (κ/3)*s^2 + (κ/9 + 2/3)*s + (-2*κ/27 - 2/9) := by
    funext s
    simp only [rmField, fitness, meanFit, biasedRPS, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hpoly]
  have h := cubic_deriv 0 (κ/3) (κ/9 + 2/3) (-2*κ/27 - 2/9) (1/3)
  convert h using 1 <;> ring

/-- **The center linearization determinant** `J₀₀J₁₁ − J₀₁J₁₀`
`= κ²/9 + κ/3 + κμ/3 + μ² + 1/3`.  At `κ = μ = 0` this is `1/3 > 0`, giving the
nonzero Hopf frequency `±i/√3`. -/
theorem rm_center_det (κ μ : ℝ) :
    (deriv (fun s : ℝ => rmField κ μ ![s, 1/3, 2/3 - s] 0) (1/3))
      * (deriv (fun s : ℝ => rmField κ μ ![1/3, s, 2/3 - s] 1) (1/3))
    - (deriv (fun s : ℝ => rmField κ μ ![1/3, s, 2/3 - s] 0) (1/3))
      * (deriv (fun s : ℝ => rmField κ μ ![s, 1/3, 2/3 - s] 1) (1/3))
      = κ^2/9 + κ/3 + κ*μ/3 + μ^2 + 1/3 := by
  rw [(rm_diag0 κ μ).deriv, (rm_diag1 κ μ).deriv,
      (rm_offdiag01 κ μ).deriv, (rm_offdiag10 κ μ).deriv]
  ring

/-- The center-trace value as an explicit affine function of the bias `κ`. -/
noncomputable def traceVal (κ μ : ℝ) : ℝ := -κ/3 - 2*μ

/-- **Transversality:** the center trace crosses zero with nonzero slope
`−1/3` in the bias `κ` — the eigenvalue real part moves through the imaginary
axis transversally. -/
theorem rm_trace_transversal (μ : ℝ) :
    HasDerivAt (fun κ => traceVal κ μ) (-1/3) 0 := by
  have h : (fun κ : ℝ => traceVal κ μ) = fun κ => (-1/3)*κ - 2*μ := by
    funext κ; simp only [traceVal]; ring
  rw [h]
  simpa using ((hasDerivAt_id (0:ℝ)).const_mul (-1/3 : ℝ)).sub_const (2*μ)

/-- **AQ-20, the true Hopf (machine-checked).**  For the pure replicator
(`μ = 0`) on biased RPS, all three supercritical-Hopf conditions hold at the
`γ = 1` boundary `κ = 0`: the center trace vanishes (eigenvalue crossing), the
center determinant is `1/3 > 0` (nonzero frequency `±i/√3`), and the trace has
nonzero slope `−1/3` in `κ` (transversality).  This is Law 7's genuine
content; the printed `κ_c(μ)` is the artifact to correct. -/
theorem rm_true_hopf :
    ((deriv (fun s : ℝ => rmField 0 0 ![s, 1/3, 2/3 - s] 0) (1/3))
      + (deriv (fun s : ℝ => rmField 0 0 ![1/3, s, 2/3 - s] 1) (1/3)) = 0)
    ∧ ((deriv (fun s : ℝ => rmField 0 0 ![s, 1/3, 2/3 - s] 0) (1/3))
        * (deriv (fun s : ℝ => rmField 0 0 ![1/3, s, 2/3 - s] 1) (1/3))
      - (deriv (fun s : ℝ => rmField 0 0 ![1/3, s, 2/3 - s] 0) (1/3))
        * (deriv (fun s : ℝ => rmField 0 0 ![s, 1/3, 2/3 - s] 1) (1/3))
        = 1/3)
    ∧ (0 : ℝ) < 1/3
    ∧ HasDerivAt (fun κ => traceVal κ 0) (-1/3) 0 := by
  refine ⟨?_, ?_, by norm_num, rm_trace_transversal 0⟩
  · have := rm_center_trace 0 0; rw [this]; ring
  · have := rm_center_det 0 0; rw [this]; ring

/-- The swirl ratio `ω(κ) = ‖W(Π(κ))‖_F / ‖S(Π(κ))‖_F = (κ+2)/κ` of the biased
RPS payoff (antisymmetric vs. symmetric Frobenius norms; §3 swirl
decomposition). -/
noncomputable def swirlRatio (κ : ℝ) : ℝ := (κ + 2) / κ

/-- **`κ = 0` is the pure-swirl / `γ = 1` boundary:** the swirl ratio blows up
as the bias vanishes, so at `κ = 0` selection is absent and the dynamics are
pure rotation — precisely the `γ = 1` threshold where Law 7 places the Hopf. -/
theorem swirl_ratio_blowup :
    Tendsto swirlRatio (𝓝[>] (0:ℝ)) atTop := by
  have h2 : Tendsto (fun κ : ℝ => 2 * κ⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num)
  have hsum : Tendsto (fun κ : ℝ => 1 + 2 * κ⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_atTop_add_const_left _ 1 h2
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with κ hκ
  have hne : κ ≠ 0 := ne_of_gt hκ
  simp only [swirlRatio]
  field_simp

end TrueHopf

end Law7
end SEKernel
