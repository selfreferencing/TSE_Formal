/-
SEKernel / Law2_ESDI.lean
Law 2 (ESDI Characterization) — arXiv:2512.07901 §5 and §12.1–12.2, kernel form.

The portfolio LP of §12.1:  max Σ r_i n_i  s.t.  Σ c_i n_i ≤ B, Σ ℓ_i n_i ≤ Q,
n ≥ 0, with dual  min μB + λQ  s.t.  μc_i + λℓ_i ≥ r_i, μ,λ ≥ 0.

Main results (definitional choices recorded in STATEMENTS.md, AQ-5..AQ-8):
* `KKT.isLPOptimal`      — Theorem 5.3, (KKT) ⟹ (LP): weak duality plus
  complementary slackness, fully proved.
* `KKT_of_optimal_dual`  — Theorem 5.3, (LP) ⟹ (KKT) **given a zero-gap dual
  witness**: complementary slackness is derived, not assumed.  The existence
  of the witness is LP strong duality — the ONE recorded conditional input
  of this file (handoff Tier-2 protocol; mirrors the CDC treatment).
* `NashEquilibrium` / `nash_iff_lpOptimal` — Theorem 5.3, (Nash) ⟺ (LP): for
  a lineage's linear objective, no-profitable-feasible-deviation *is* LP
  optimality (the recorded AQ-7 reading).
* `KKT.reduced_return`   — the ESDI (Definition 5.1) bridge: supported types
  have zero reduced return, all types nonpositive — the shadow-price form of
  equilibrium conditions (1)–(2).
* `esdi_exists_const`    — Theorem 5.2 (ESDI existence) for state-independent
  fitness, constructive (uniform mass on the argmax set).  The paper's
  general state-dependent claim is flagged REPAIR-CANDIDATE (AQ-6).
* `constraint_role_sparsity` — Theorem 5.4/Corollary 5.5: under generic
  position (no three cost-normalised points on a common shadow-price line),
  KKT support has at most two active types (the barbell bound, AQ-8).

Zero custom axioms; the strong-duality input enters only as an explicit
hypothesis of `KKT_of_optimal_dual`.
-/
import Mathlib
import SEKernel.Law1_Selection

namespace SEKernel
namespace Law2

open Finset

variable {ι : Type*} [Fintype ι]

/-- Primal feasibility for the portfolio LP (§12.1). -/
structure Feasible (c l : ι → ℝ) (B Q : ℝ) (n : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ n i
  budget : ∑ i, c i * n i ≤ B
  capacity : ∑ i, l i * n i ≤ Q

/-- The KKT conditions for ROC/return maximization (Theorem 5.3(2)):
dual feasibility plus complementary slackness. -/
structure KKT (r c l : ι → ℝ) (B Q : ℝ) (n : ι → ℝ) (μ lam : ℝ) : Prop where
  feas : Feasible c l B Q n
  mu_nonneg : 0 ≤ μ
  lam_nonneg : 0 ≤ lam
  dualFeas : ∀ i, r i ≤ μ * c i + lam * l i
  csPrimal : ∀ i, 0 < n i → r i = μ * c i + lam * l i
  csBudget : 0 < μ → ∑ i, c i * n i = B
  csCapacity : 0 < lam → ∑ i, l i * n i = Q

/-- LP optimality (Theorem 5.3(3)). -/
def IsLPOptimal (r c l : ι → ℝ) (B Q : ℝ) (n : ι → ℝ) : Prop :=
  Feasible c l B Q n ∧
    ∀ n', Feasible c l B Q n' → ∑ i, r i * n' i ≤ ∑ i, r i * n i

/-- Nash equilibrium of the population game, lineage-level reading (AQ-5,
AQ-7): no feasible deviation improves the portfolio value. -/
def NashEquilibrium (r c l : ι → ℝ) (B Q : ℝ) (n : ι → ℝ) : Prop :=
  Feasible c l B Q n ∧
    ∀ n', Feasible c l B Q n' → ∑ i, r i * n' i ≤ ∑ i, r i * n i

/-- Theorem 5.3, (Nash) ⟺ (LP): definitional under the recorded reading —
for a linear objective, "no feasible improving deviation" is LP optimality. -/
theorem nash_iff_lpOptimal {r c l : ι → ℝ} {B Q : ℝ} {n : ι → ℝ} :
    NashEquilibrium r c l B Q n ↔ IsLPOptimal r c l B Q n := Iff.rfl

/-- The complementary-slackness value identity: a KKT point attains the dual
objective `μB + λQ`. -/
theorem KKT.value_eq {r c l : ι → ℝ} {B Q : ℝ} {n : ι → ℝ} {μ lam : ℝ}
    (h : KKT r c l B Q n μ lam) :
    ∑ i, r i * n i = μ * B + lam * Q := by
  have hterm : ∀ i ∈ Finset.univ,
      r i * n i = (μ * c i + lam * l i) * n i := by
    intro i _
    rcases lt_or_eq_of_le (h.feas.nonneg i) with hi | hi
    · rw [h.csPrimal i hi]
    · rw [← hi, mul_zero, mul_zero]
  have hsplit : ∑ i, r i * n i
      = μ * ∑ i, c i * n i + lam * ∑ i, l i * n i := by
    rw [Finset.sum_congr rfl hterm, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  congr 1
  · rcases lt_or_eq_of_le h.mu_nonneg with hμ | hμ
    · rw [h.csBudget hμ]
    · rw [← hμ, zero_mul, zero_mul]
  · rcases lt_or_eq_of_le h.lam_nonneg with hlam | hlam
    · rw [h.csCapacity hlam]
    · rw [← hlam, zero_mul, zero_mul]

/-- Weak duality: any feasible portfolio's value is at most the dual
objective of any dual-feasible pair. -/
theorem weak_duality {r c l : ι → ℝ} {B Q : ℝ} {n' : ι → ℝ} {μ lam : ℝ}
    (hfeas : Feasible c l B Q n') (hμ : 0 ≤ μ) (hlam : 0 ≤ lam)
    (hdual : ∀ i, r i ≤ μ * c i + lam * l i) :
    ∑ i, r i * n' i ≤ μ * B + lam * Q := by
  have h1 : ∑ i, r i * n' i ≤ ∑ i, (μ * c i + lam * l i) * n' i :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hdual i) (hfeas.nonneg i)
  have h2 : ∑ i, (μ * c i + lam * l i) * n' i
      = μ * ∑ i, c i * n' i + lam * ∑ i, l i * n' i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : μ * ∑ i, c i * n' i ≤ μ * B :=
    mul_le_mul_of_nonneg_left hfeas.budget hμ
  have h4 : lam * ∑ i, l i * n' i ≤ lam * Q :=
    mul_le_mul_of_nonneg_left hfeas.capacity hlam
  linarith

/-- **Theorem 5.3, (KKT) ⟹ (LP).**  Weak duality plus complementary
slackness; fully proved, no strong duality needed. -/
theorem KKT.isLPOptimal {r c l : ι → ℝ} {B Q : ℝ} {n : ι → ℝ} {μ lam : ℝ}
    (h : KKT r c l B Q n μ lam) : IsLPOptimal r c l B Q n := by
  refine ⟨h.feas, fun n' hn' => ?_⟩
  calc ∑ i, r i * n' i ≤ μ * B + lam * Q :=
        weak_duality hn' h.mu_nonneg h.lam_nonneg h.dualFeas
    _ = ∑ i, r i * n i := h.value_eq.symm

/-- **Theorem 5.3, (LP) ⟹ (KKT), given a zero-gap dual witness.**  If `n` is
optimal and `(μ, λ)` is dual-feasible with dual objective equal to the
value of `n` (LP strong duality supplies such a pair — the recorded
conditional input), then complementary slackness is *derived* and
`(n, μ, λ)` is a KKT point. -/
theorem KKT_of_optimal_dual {r c l : ι → ℝ} {B Q : ℝ} {n : ι → ℝ}
    {μ lam : ℝ}
    (hopt : IsLPOptimal r c l B Q n)
    (hμ : 0 ≤ μ) (hlam : 0 ≤ lam)
    (hdual : ∀ i, r i ≤ μ * c i + lam * l i)
    (hgap : ∑ i, r i * n i = μ * B + lam * Q) :
    KKT r c l B Q n μ lam := by
  obtain ⟨hfeas, -⟩ := hopt
  have h2 : ∑ i, (μ * c i + lam * l i) * n i
      = μ * ∑ i, c i * n i + lam * ∑ i, l i * n i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h1 : ∑ i, r i * n i ≤ ∑ i, (μ * c i + lam * l i) * n i :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hdual i) (hfeas.nonneg i)
  have h3 : μ * ∑ i, c i * n i ≤ μ * B :=
    mul_le_mul_of_nonneg_left hfeas.budget hμ
  have h4 : lam * ∑ i, l i * n i ≤ lam * Q :=
    mul_le_mul_of_nonneg_left hfeas.capacity hlam
  have htight1 : ∑ i, r i * n i = ∑ i, (μ * c i + lam * l i) * n i := by
    have hub : ∑ i, (μ * c i + lam * l i) * n i ≤ μ * B + lam * Q := by
      rw [h2]; linarith
    linarith [hgap]
  have hterm : ∀ i ∈ Finset.univ,
      r i * n i = (μ * c i + lam * l i) * n i :=
    (Finset.sum_eq_sum_iff_of_le fun i _ =>
      mul_le_mul_of_nonneg_right (hdual i) (hfeas.nonneg i)).mp htight1
  have hcs : μ * ∑ i, c i * n i = μ * B
      ∧ lam * ∑ i, l i * n i = lam * Q := by
    have heq := htight1
    rw [h2] at heq
    constructor <;> linarith [hgap]
  refine ⟨hfeas, hμ, hlam, hdual, ?_, ?_, ?_⟩
  · intro i hi
    exact mul_right_cancel₀ (ne_of_gt hi) (hterm i (Finset.mem_univ i))
  · intro hμpos
    exact mul_left_cancel₀ (ne_of_gt hμpos) hcs.1
  · intro hlampos
    exact mul_left_cancel₀ (ne_of_gt hlampos) hcs.2

/-- ESDI bridge (Definition 5.1 in shadow-price form): at a KKT point, every
type has nonpositive reduced return and supported types have exactly zero —
equilibrium conditions (1)–(2) of Definition 5.1 for the reduced game. -/
theorem KKT.reduced_return {r c l : ι → ℝ} {B Q : ℝ} {n : ι → ℝ}
    {μ lam : ℝ} (h : KKT r c l B Q n μ lam) :
    (∀ i, r i - (μ * c i + lam * l i) ≤ 0)
      ∧ ∀ i, 0 < n i → r i - (μ * c i + lam * l i) = 0 :=
  ⟨fun i => sub_nonpos.mpr (h.dualFeas i),
    fun i hi => sub_eq_zero.mpr (h.csPrimal i hi)⟩

/-! ### Theorem 5.2: ESDI existence, state-independent case (AQ-6) -/

/-- **Theorem 5.2 (ESDI Existence), state-independent fitness.**  For
constant fitness `f` on a finite nonempty type set, the uniform distribution
on the argmax set is an equilibrium state: supported types have exactly mean
fitness and no type exceeds it.  Constructive; the paper's state-dependent
claim via the extreme value theorem is flagged REPAIR-CANDIDATE (AQ-6). -/
theorem esdi_exists_const [Nonempty ι] (f : ι → ℝ) :
    ∃ x : ι → ℝ, (∀ j, 0 ≤ x j) ∧ (∑ j, x j = 1) ∧
      (∀ j, 0 < x j → f j = Law1.mean x f) ∧ (∀ j, f j ≤ Law1.mean x f) := by
  classical
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty f with hM
  set A : Finset ι := Finset.univ.filter (fun j => f j = M) with hA
  have hAne : A.Nonempty := by
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    exact ⟨j₀, by simp [hA, ← hj₀, hM]⟩
  have hcardpos : (0:ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hAne
  have hcardne : (A.card : ℝ) ≠ 0 := ne_of_gt hcardpos
  set x : ι → ℝ := fun j => if j ∈ A then (A.card : ℝ)⁻¹ else 0 with hx
  have hfA : ∀ j ∈ A, f j = M := by
    intro j hj
    rw [hA] at hj
    exact (Finset.mem_filter.mp hj).2
  have hmean : Law1.mean x f = M := by
    simp only [Law1.mean, hx, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_congr rfl
      (fun j hj => by rw [hfA j hj] :
        ∀ j ∈ A, (A.card : ℝ)⁻¹ * f j = (A.card : ℝ)⁻¹ * M)]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [hx]
    split
    · positivity
    · exact le_refl 0
  · simp only [hx]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    field_simp
  · intro j hjpos
    have hjA : j ∈ A := by
      by_contra hno
      simp [hx, hno] at hjpos
    rw [hmean]
    exact hfA j hjA
  · intro j
    rw [hmean, hM]
    exact Finset.le_sup' f (Finset.mem_univ j)

/-! ### Theorem 5.4 / Corollary 5.5: sparsity and the barbell bound (AQ-8) -/

open scoped Classical in
/-- **Theorem 5.4 (Constraint-Role Sparsity) / Corollary 5.5 (Barbell).**
At a KKT point of the two-constraint portfolio LP, all supported types lie on
the shadow-price line `b = μ + λ·a` in the cost-normalised `(a, b)`-plane
(`a_i = ℓ_i/c_i`, `b_i = r_i/c_i` — Prop 2.8's coordinates).  Under generic
position — no shadow-price line contains three of the points — the support
has at most two active types: high-capability planners and low-capability
executors. -/
theorem constraint_role_sparsity {r c l : ι → ℝ} {B Q : ℝ} {n : ι → ℝ}
    {μ lam : ℝ}
    (h : KKT r c l B Q n μ lam) (hc : ∀ i, 0 < c i)
    (hgen : ∀ μ' lam' : ℝ,
      (Finset.univ.filter
        fun i => r i / c i = μ' + lam' * (l i / c i)).card ≤ 2) :
    (Finset.univ.filter fun i => 0 < n i).card ≤ 2 := by
  refine le_trans (Finset.card_le_card ?_) (hgen μ lam)
  intro i hi
  have hipos : 0 < n i := (Finset.mem_filter.mp hi).2
  have hcs := h.csPrimal i hipos
  have hci := ne_of_gt (hc i)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ i, ?_⟩
  rw [hcs]
  field_simp


/-! ### AQ-6 repair: what EVT gives, why the paper's route fails, and the
Nash-map reduction

Three machine-checked facts localise and repair the Theorem 5.2 gap.
1. `exists_mean_maximizer` — what the extreme-value argument really yields:
   a maximizer of `f̄` on the simplex (Definition 5.1's condition (3)).
2. `maximizer_method_gap` — the proof-method counterexample: a continuous
   state-dependent fitness whose `f̄`-maximizer **violates** equilibrium
   condition (1).  So "any maximum satisfies the ESDI conditions" fails as
   stated; the theorem needs a different route (below), not a bigger EVT.
3. `nashMap_fixedPoint_equilibrium` — the repair: Nash's improvement map;
   any fixed point on the simplex satisfies conditions (1)–(2), by pure
   algebra.  Existence of the fixed point is Brouwer's theorem applied to
   the (continuous) map — **Brouwer is not yet in Mathlib**, so the kernel
   records it as the named classical input (`esdi_exists_of_fixedPoint`),
   exactly the "formalize up to the classical theorem" protocol. -/

section ExistenceRepair

/-- Condition (2) implies condition (1) on the simplex: if no type beats the
mean, supported types sit exactly at it (weighted-average algebra). -/
theorem equilibrium_of_le_mean {x f : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hsum : ∑ j, x j = 1) (hle : ∀ j, f j ≤ Law1.mean x f) :
    ∀ j, 0 < x j → f j = Law1.mean x f := by
  intro j hj
  by_contra hne
  have hlt : f j < Law1.mean x f := lt_of_le_of_ne (hle j) hne
  have hstrict : ∑ k, x k * f k < ∑ k, x k * Law1.mean x f :=
    Finset.sum_lt_sum
      (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hx k))
      ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hlt hj⟩
  rw [← Finset.sum_mul, hsum, one_mul] at hstrict
  exact lt_irrefl _ hstrict

/-- **What the paper's EVT argument establishes** (and all it establishes):
a continuous mean-fitness functional attains a maximum on the simplex. -/
theorem exists_mean_maximizer [Nonempty ι] (F : (ι → ℝ) → ι → ℝ)
    (hF : Continuous fun x => Law1.mean x (F x)) :
    ∃ x ∈ stdSimplex ℝ ι, ∀ y ∈ stdSimplex ℝ ι,
      Law1.mean y (F y) ≤ Law1.mean x (F x) := by
  have hne : (stdSimplex ℝ ι).Nonempty := by
    refine ⟨fun _ => 1 / Fintype.card ι, fun _ => by positivity, ?_⟩
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    field_simp
  obtain ⟨x, hx, hmax⟩ :=
    (isCompact_stdSimplex ι).exists_isMaxOn hne hF.continuousOn
  exact ⟨x, hx, fun y hy => hmax hy⟩

/-- **REPAIR-CANDIDATE AQ-6, machine-checked:** the proof method of
Theorem 5.2 fails for state-dependent fitness.  With `F x = ![1 − x₀, 0]`
(continuous), the unique maximizer `(1/2, 1/2)` of `f̄(x) = x₀(1 − x₀)` has a
supported type whose fitness (1/2) differs from the mean (1/4) — equilibrium
condition (1) is violated at the `f̄`-maximizer. -/
theorem maximizer_method_gap :
    ∃ (F : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ),
      Continuous (fun y => Law1.mean y (F y)) ∧
      x ∈ stdSimplex ℝ (Fin 2) ∧
      (∀ y ∈ stdSimplex ℝ (Fin 2), Law1.mean y (F y) ≤ Law1.mean x (F x)) ∧
      ¬ (∀ j, 0 < x j → F x j = Law1.mean x (F x)) := by
  refine ⟨fun y => ![1 - y 0, 0], ![1/2, 1/2], ?_, ?_, ?_, ?_⟩
  · have hrw : (fun y : Fin 2 → ℝ => Law1.mean y ![1 - y 0, 0])
        = fun y => y 0 * (1 - y 0) := by
      funext y
      simp [Law1.mean, Fin.sum_univ_two]
    rw [hrw]
    exact (continuous_apply 0).mul (continuous_const.sub (continuous_apply 0))
  · refine ⟨fun j => ?_, ?_⟩
    · fin_cases j <;> norm_num
    · simp [Fin.sum_univ_two]
      norm_num
  · intro y _
    have hy : Law1.mean y ![1 - y 0, 0] = y 0 * (1 - y 0) := by
      simp [Law1.mean, Fin.sum_univ_two]
    have hx : Law1.mean ![(1:ℝ)/2, 1/2] ![1 - (![(1:ℝ)/2, 1/2]) 0, 0]
        = 1/4 := by
      simp [Law1.mean, Fin.sum_univ_two]
      norm_num
    rw [hy, hx]
    nlinarith [sq_nonneg (y 0 - 1/2)]
  · intro hcond
    have h0 := hcond 0 (by norm_num)
    simp [Law1.mean, Fin.sum_univ_two] at h0
    norm_num at h0

/-- Nash's improvement map: shift mass toward above-mean types and
renormalise.  Fixed points are exactly the equilibrium states. -/
noncomputable def nashMap (x f : ι → ℝ) : ι → ℝ := fun j =>
  (x j + max 0 (f j - Law1.mean x f))
    / (1 + ∑ k, max 0 (f k - Law1.mean x f))

/-- **The AQ-6 repair, algebraic half (fully proved):** a fixed point of the
Nash map on the simplex satisfies both equilibrium conditions of
Definition 5.1.  No topology is used — this is the reduction of ESDI
existence to a fixed-point principle. -/
theorem nashMap_fixedPoint_equilibrium {x f : ι → ℝ}
    (hx : ∀ j, 0 ≤ x j) (hsum : ∑ j, x j = 1)
    (hfix : nashMap x f = x) :
    (∀ j, f j ≤ Law1.mean x f) ∧
      (∀ j, 0 < x j → f j = Law1.mean x f) := by
  set K : ℝ := ∑ k, max 0 (f k - Law1.mean x f) with hK
  have hKnonneg : 0 ≤ K :=
    Finset.sum_nonneg fun k _ => le_max_left 0 _
  have hK1 : (0:ℝ) < 1 + K := by linarith
  -- fixed-point identity: max 0 (f j − f̄) = x j · K for every j
  have hkey : ∀ j, max 0 (f j - Law1.mean x f) = x j * K := by
    intro j
    have h := congrFun hfix j
    rw [nashMap, div_eq_iff (ne_of_gt hK1)] at h
    linarith [h]
  -- K must vanish: otherwise supported types all strictly beat the mean
  have hKzero : K = 0 := by
    by_contra hKne
    have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hKne)
    obtain ⟨j₀, -, hj₀⟩ : ∃ j ∈ Finset.univ, x j ≠ 0 := by
      apply Finset.exists_ne_zero_of_sum_ne_zero (f := x)
      rw [hsum]; exact one_ne_zero
    have hxj₀ : 0 < x j₀ := lt_of_le_of_ne (hx j₀) (Ne.symm hj₀)
    -- every supported type strictly beats the mean
    have hbeat : ∀ j, 0 < x j → Law1.mean x f < f j := by
      intro j hj
      have hmax : 0 < max 0 (f j - Law1.mean x f) := by
        rw [hkey j]; exact mul_pos hj hKpos
      by_contra hle
      push_neg at hle
      rw [max_eq_left (by linarith)] at hmax
      exact lt_irrefl 0 hmax
    -- so the mean strictly beats itself
    have hstrict : ∑ k, x k * Law1.mean x f < ∑ k, x k * f k := by
      refine Finset.sum_lt_sum (fun k _ => ?_)
        ⟨j₀, Finset.mem_univ j₀,
          mul_lt_mul_of_pos_left (hbeat j₀ hxj₀) hxj₀⟩
      rcases lt_or_eq_of_le (hx k) with hk | hk
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hbeat k hk)) (hx k)
      · rw [← hk, zero_mul, zero_mul]
    rw [← Finset.sum_mul, hsum, one_mul] at hstrict
    exact lt_irrefl _ hstrict
  -- with K = 0 all improvement terms vanish: condition (2), then (1)
  have hcond2 : ∀ j, f j ≤ Law1.mean x f := by
    intro j
    have h0 : max 0 (f j - Law1.mean x f) = 0 := by
      rw [hkey j, hKzero, mul_zero]
    by_contra hgt
    push_neg at hgt
    rw [max_eq_right (by linarith)] at h0
    linarith
  exact ⟨hcond2, equilibrium_of_le_mean hx hsum hcond2⟩

/-- **Theorem 5.2 (general ESDI existence), conditional form.**  Given a
fixed point of the Nash map on the simplex — supplied classically by
Brouwer's theorem (continuity of `nashMap` for continuous `F` is routine),
which is **not yet in Mathlib** and is the recorded classical input — an
equilibrium state exists. -/
theorem esdi_exists_of_fixedPoint (F : (ι → ℝ) → ι → ℝ)
    (hfix : ∃ x, (∀ j, 0 ≤ x j) ∧ (∑ j, x j = 1)
      ∧ nashMap x (F x) = x) :
    ∃ x, (∀ j, 0 ≤ x j) ∧ (∑ j, x j = 1)
      ∧ (∀ j, 0 < x j → F x j = Law1.mean x (F x))
      ∧ (∀ j, F x j ≤ Law1.mean x (F x)) := by
  obtain ⟨x, hx, hsum, hfp⟩ := hfix
  obtain ⟨h2, h1⟩ := nashMap_fixedPoint_equilibrium hx hsum hfp
  exact ⟨x, hx, hsum, h1, h2⟩

end ExistenceRepair

end Law2
end SEKernel
