/-
SEKernel / Law5_Duality.lean
Law 5 (Constitutional Duality) — arXiv:2512.07901 §12, kernel form.

The paper states Theorems 12.1 (First Welfare), 12.2 (Second Welfare) and
12.4 (Price-of-Anarchy bound) without body proofs; this file supplies them
for the GEP setting of §2.5/§12.1 — lineages with **private budgets** and a
**shared capacity** governed by one constitutional shadow price λ.
Definitional readings recorded in STATEMENTS.md (AQ-15, AQ-16).

Main results:
* `first_welfare`      — **Theorem 12.1**: a shadow-price-supported joint
  allocation is Pareto efficient among all feasible joint allocations.
  Proof: per-lineage complementary-slackness value identities, summed;
  the shared-capacity price transfers the joint constraint.  Fully proved.
* `shadow_price_implementation` — **Theorem 12.2, implementation half**:
  at the constitutional capacity price λ, every lineage's assigned
  portfolio maximises its *profit* `Σ (r_i − λℓ_i) m_i` over its private
  budget set alone — shadow prices decentralise the frontier allocation.
  The converse half (every Pareto-efficient allocation possesses supporting
  prices) is a separating-hyperplane statement: recorded, deferred (AQ-15).
* `poa_bound`, `poa_bound_ratio` — **Theorem 12.4**: under the ESDI
  equilibrium conditions (Definition 5.1(2)) and the cross-state H-γ bound
  (AQ-16: the static face of Assumption 3.2), every population state's mean
  fitness is within a factor 1/(1−γ) of the equilibrium's:
  `PoA ≤ 1/(1−γ)`, exactly the paper's bound.

Zero custom axioms.
-/
import Mathlib
import SEKernel.Law1_Selection

namespace SEKernel
namespace Law5

open Finset

variable {ι Λ : Type*} [Fintype ι] [Fintype Λ]

/-! ### Joint allocations (GEP: private budgets, shared capacity) -/

/-- Joint feasibility for lineages `Λ` over agent types `ι` (Definition 2.9's
three-level structure, §12.1 constraints): every lineage respects its private
budget `B ℓ`, and total load respects the shared capacity `Q`. -/
structure JointFeasible (c l : ι → ℝ) (B : Λ → ℝ) (Q : ℝ)
    (n : Λ → ι → ℝ) : Prop where
  nonneg : ∀ ℓ i, 0 ≤ n ℓ i
  budget : ∀ ℓ, ∑ i, c i * n ℓ i ≤ B ℓ
  capacity : ∑ ℓ, ∑ i, l i * n ℓ i ≤ Q

/-- Return (value) of lineage `ℓ` at joint allocation `n`. -/
def value (r : ι → ℝ) (n : Λ → ι → ℝ) (ℓ : Λ) : ℝ := ∑ i, r i * n ℓ i

/-- Pareto domination: no lineage worse off, some lineage strictly better. -/
def ParetoDominates (r : ι → ℝ) (n' n : Λ → ι → ℝ) : Prop :=
  (∀ ℓ, value r n ℓ ≤ value r n' ℓ) ∧ ∃ ℓ, value r n ℓ < value r n' ℓ

/-- Pareto efficiency in the space of feasible joint allocations
(Theorem 12.1's conclusion). -/
def ParetoEfficient (r c l : ι → ℝ) (B : Λ → ℝ) (Q : ℝ)
    (n : Λ → ι → ℝ) : Prop :=
  JointFeasible c l B Q n ∧
    ∀ n', JointFeasible c l B Q n' → ¬ ParetoDominates r n' n

/-- Shadow-price support (the "ESDI with appropriate shadow prices" of §12):
per-lineage budget prices `μ ℓ` and ONE constitutional capacity price `λ`
with dual feasibility and complementary slackness — the joint-allocation
form of the KKT conditions of Law 2. -/
structure PriceSupported (r c l : ι → ℝ) (B : Λ → ℝ) (Q : ℝ)
    (n : Λ → ι → ℝ) (μ : Λ → ℝ) (lam : ℝ) : Prop where
  feas : JointFeasible c l B Q n
  mu_nonneg : ∀ ℓ, 0 ≤ μ ℓ
  lam_nonneg : 0 ≤ lam
  dualFeas : ∀ ℓ i, r i ≤ μ ℓ * c i + lam * l i
  csPrimal : ∀ ℓ i, 0 < n ℓ i → r i = μ ℓ * c i + lam * l i
  csBudget : ∀ ℓ, 0 < μ ℓ → ∑ i, c i * n ℓ i = B ℓ
  csCapacity : 0 < lam → ∑ ℓ, ∑ i, l i * n ℓ i = Q

/-- Per-lineage complementary-slackness value identity at a supported
allocation: `value ℓ = μ_ℓ B_ℓ + λ · load_ℓ`. -/
theorem PriceSupported.value_eq {r c l : ι → ℝ} {B : Λ → ℝ} {Q : ℝ}
    {n : Λ → ι → ℝ} {μ : Λ → ℝ} {lam : ℝ}
    (h : PriceSupported r c l B Q n μ lam) (ℓ : Λ) :
    value r n ℓ = μ ℓ * B ℓ + lam * ∑ i, l i * n ℓ i := by
  have hterm : ∀ i ∈ Finset.univ,
      r i * n ℓ i = (μ ℓ * c i + lam * l i) * n ℓ i := by
    intro i _
    rcases lt_or_eq_of_le (h.feas.nonneg ℓ i) with hi | hi
    · rw [h.csPrimal ℓ i hi]
    · rw [← hi, mul_zero, mul_zero]
  have hsplit : value r n ℓ
      = μ ℓ * (∑ i, c i * n ℓ i) + lam * ∑ i, l i * n ℓ i := by
    rw [value, Finset.sum_congr rfl hterm, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  congr 1
  rcases lt_or_eq_of_le (h.mu_nonneg ℓ) with hμ | hμ
  · rw [h.csBudget ℓ hμ]
  · rw [← hμ, zero_mul, zero_mul]

/-- Per-lineage weak-duality bound at any feasible deviation:
`value' ℓ ≤ μ_ℓ B_ℓ + λ · load'_ℓ`. -/
theorem PriceSupported.value_le {r c l : ι → ℝ} {B : Λ → ℝ} {Q : ℝ}
    {n n' : Λ → ι → ℝ} {μ : Λ → ℝ} {lam : ℝ}
    (h : PriceSupported r c l B Q n μ lam)
    (hn' : JointFeasible c l B Q n') (ℓ : Λ) :
    value r n' ℓ ≤ μ ℓ * B ℓ + lam * ∑ i, l i * n' ℓ i := by
  have h1 : value r n' ℓ ≤ ∑ i, (μ ℓ * c i + lam * l i) * n' ℓ i :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (h.dualFeas ℓ i) (hn'.nonneg ℓ i)
  have h2 : ∑ i, (μ ℓ * c i + lam * l i) * n' ℓ i
      = μ ℓ * (∑ i, c i * n' ℓ i) + lam * ∑ i, l i * n' ℓ i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : μ ℓ * (∑ i, c i * n' ℓ i) ≤ μ ℓ * B ℓ :=
    mul_le_mul_of_nonneg_left (hn'.budget ℓ) (h.mu_nonneg ℓ)
  calc value r n' ℓ ≤ μ ℓ * (∑ i, c i * n' ℓ i) + lam * ∑ i, l i * n' ℓ i := by
        rw [← h2]; exact h1
    _ ≤ μ ℓ * B ℓ + lam * ∑ i, l i * n' ℓ i := by linarith

/-- **Theorem 12.1 (First Welfare Theorem for Strategic Replicators).**
A shadow-price-supported joint allocation is Pareto efficient: no feasible
reallocation of the shared capacity makes some lineage strictly better off
without making another worse off.  Fully proved — the constitutional price
`λ` internalises the shared-capacity externality. -/
theorem first_welfare {r c l : ι → ℝ} {B : Λ → ℝ} {Q : ℝ}
    {n : Λ → ι → ℝ} {μ : Λ → ℝ} {lam : ℝ}
    (h : PriceSupported r c l B Q n μ lam) :
    ParetoEfficient r c l B Q n := by
  refine ⟨h.feas, fun n' hn' hdom => ?_⟩
  -- per-lineage: value' ℓ − value ℓ ≤ λ (load' ℓ − load ℓ)
  have hkey : ∀ ℓ ∈ Finset.univ, value r n' ℓ
      ≤ value r n ℓ + lam * ((∑ i, l i * n' ℓ i) - ∑ i, l i * n ℓ i) := by
    intro ℓ _
    have h1 := h.value_le hn' ℓ
    have h2 := h.value_eq ℓ
    have hexp : lam * ((∑ i, l i * n' ℓ i) - ∑ i, l i * n ℓ i)
        = lam * (∑ i, l i * n' ℓ i) - lam * (∑ i, l i * n ℓ i) := by ring
    linarith
  -- sum over lineages; the capacity terms telescope against the shared Q
  have hsum : ∑ ℓ, value r n' ℓ
      ≤ ∑ ℓ, value r n ℓ
        + lam * ((∑ ℓ, ∑ i, l i * n' ℓ i) - ∑ ℓ, ∑ i, l i * n ℓ i) := by
    calc ∑ ℓ, value r n' ℓ
        ≤ ∑ ℓ, (value r n ℓ
            + lam * ((∑ i, l i * n' ℓ i) - ∑ i, l i * n ℓ i)) :=
          Finset.sum_le_sum hkey
      _ = ∑ ℓ, value r n ℓ
          + lam * ((∑ ℓ, ∑ i, l i * n' ℓ i) - ∑ ℓ, ∑ i, l i * n ℓ i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_sub_distrib]
  have hcap : lam * ((∑ ℓ, ∑ i, l i * n' ℓ i) - ∑ ℓ, ∑ i, l i * n ℓ i)
      ≤ 0 := by
    rcases lt_or_eq_of_le h.lam_nonneg with hl | hl
    · have h1 := hn'.capacity
      have h2 := h.csCapacity hl
      rw [h2]
      have hle : (∑ ℓ, ∑ i, l i * n' ℓ i) - Q ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hl) hle
    · rw [← hl, zero_mul]
  -- Pareto domination forces a strictly larger total — contradiction
  obtain ⟨hall, ℓ₀, hstrict⟩ := hdom
  have hlt : ∑ ℓ, value r n ℓ < ∑ ℓ, value r n' ℓ :=
    Finset.sum_lt_sum (fun ℓ _ => hall ℓ)
      ⟨ℓ₀, Finset.mem_univ _, hstrict⟩
  linarith

/-! ### Theorem 12.2: shadow-price implementation (decentralisation) -/

/-- Lineage profit at the constitutional capacity price `λ`:
`π(m) = Σ_i (r_i − λ ℓ_i) m_i` — return net of priced capacity use. -/
def profit (r l : ι → ℝ) (lam : ℝ) (m : ι → ℝ) : ℝ :=
  ∑ i, (r i - lam * l i) * m i

/-- **Theorem 12.2 (Second Welfare Theorem), implementation half.**
At a shadow-price-supported allocation, each lineage's assigned portfolio
maximises its profit at the constitutional price `λ` over its **private
budget set alone** — the shared-capacity constraint has been fully
decentralised into the price.  ("Shadow prices implement the frontier
allocation.")  The converse half — existence of supporting prices for an
arbitrary Pareto-efficient allocation (separating hyperplane) — is the separating-hyperplane
statement, recorded and deferred (AQ-15). -/
theorem shadow_price_implementation {r c l : ι → ℝ} {B : Λ → ℝ} {Q : ℝ}
    {n : Λ → ι → ℝ} {μ : Λ → ℝ} {lam : ℝ}
    (h : PriceSupported r c l B Q n μ lam) (ℓ : Λ)
    (m : ι → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hmB : ∑ i, c i * m i ≤ B ℓ) :
    profit r l lam m ≤ profit r l lam (n ℓ) := by
  -- deviation profit ≤ μ_ℓ B_ℓ
  have h1 : profit r l lam m ≤ ∑ i, μ ℓ * c i * m i := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := h.dualFeas ℓ i
    have hsub : r i - lam * l i ≤ μ ℓ * c i := by linarith
    exact mul_le_mul_of_nonneg_right hsub (hm0 i)
  have h2 : ∑ i, μ ℓ * c i * m i = μ ℓ * ∑ i, c i * m i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : μ ℓ * ∑ i, c i * m i ≤ μ ℓ * B ℓ :=
    mul_le_mul_of_nonneg_left hmB (h.mu_nonneg ℓ)
  -- assigned-portfolio profit = μ_ℓ B_ℓ exactly
  have h4 : profit r l lam (n ℓ) = μ ℓ * ∑ i, c i * n ℓ i := by
    have hterm : ∀ i ∈ Finset.univ,
        (r i - lam * l i) * n ℓ i = μ ℓ * c i * n ℓ i := by
      intro i _
      rcases lt_or_eq_of_le (h.feas.nonneg ℓ i) with hi | hi
      · have := h.csPrimal ℓ i hi
        have hsub : r i - lam * l i = μ ℓ * c i := by linarith
        rw [hsub]
      · rw [← hi, mul_zero, mul_zero]
    rw [profit, Finset.sum_congr rfl hterm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h5 : μ ℓ * ∑ i, c i * n ℓ i = μ ℓ * B ℓ := by
    rcases lt_or_eq_of_le (h.mu_nonneg ℓ) with hμ | hμ
    · rw [h.csBudget ℓ hμ]
    · rw [← hμ, zero_mul, zero_mul]
  calc profit r l lam m ≤ μ ℓ * B ℓ := by
        calc profit r l lam m ≤ ∑ i, μ ℓ * c i * m i := h1
          _ = μ ℓ * ∑ i, c i * m i := h2
          _ ≤ μ ℓ * B ℓ := h3
    _ = profit r l lam (n ℓ) := by rw [h4, h5]

/-! ### Theorem 12.4: Price-of-Anarchy bound (AQ-16) -/

/-- **Theorem 12.4 (PoA Bounds), division-free core.**  Let `x` be an
equilibrium state — Definition 5.1(2): no type's fitness exceeds the mean —
and `y` any population state.  Under the cross-state H-γ bound
`Σ_j y_j (f_j(y) − f_j(x)) ≤ γ·f̄(y)` (the static face of Assumption 3.2,
AQ-16), the mean fitness anywhere is within a `1/(1−γ)` factor of the
equilibrium mean:  `(1−γ)·f̄(y) ≤ f̄(x)`. -/
theorem poa_bound {x y fx fy : ι → ℝ} {γ : ℝ}
    (hynn : ∀ j, 0 ≤ y j) (hy1 : ∑ j, y j = 1)
    (hNE : ∀ j, fx j ≤ Law1.mean x fx)
    (hcross : ∑ j, y j * (fy j - fx j) ≤ γ * Law1.mean y fy) :
    (1 - γ) * Law1.mean y fy ≤ Law1.mean x fx := by
  have h1 : Law1.mean y fy
      = (∑ j, y j * fx j) + ∑ j, y j * (fy j - fx j) := by
    rw [Law1.mean, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, y j * fx j ≤ ∑ j, y j * Law1.mean x fx :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hNE j) (hynn j)
  have h3 : ∑ j, y j * Law1.mean x fx = Law1.mean x fx := by
    rw [← Finset.sum_mul, hy1, one_mul]
  linarith

/-- **Theorem 12.4 in ratio form: `PoA ≤ 1/(1−γ)`.**  With `y` the socially
optimal state and `x` the (worst) equilibrium, `f̄(y)/f̄(x) ≤ 1/(1−γ)`. -/
theorem poa_bound_ratio {x y fx fy : ι → ℝ} {γ : ℝ}
    (hynn : ∀ j, 0 ≤ y j) (hy1 : ∑ j, y j = 1)
    (hNE : ∀ j, fx j ≤ Law1.mean x fx)
    (hcross : ∑ j, y j * (fy j - fx j) ≤ γ * Law1.mean y fy)
    (hγ : γ < 1) (hxpos : 0 < Law1.mean x fx) :
    Law1.mean y fy / Law1.mean x fx ≤ 1 / (1 - γ) := by
  have hcore := poa_bound hynn hy1 hNE hcross
  rw [div_le_div_iff₀ hxpos (by linarith : (0:ℝ) < 1 - γ)]
  linarith

end Law5
end SEKernel
