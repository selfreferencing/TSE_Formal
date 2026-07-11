/-
SEKernel / PriceMarket.lean
Competitive markets with self-replicating agents — machine-verified core of the
price-theory companion paper ("Competitive Markets with Self-Replicating Agents")
and the constitutional-political-economy paper ("Constitutions for AI Economies
Must Be Sybil-Resistant").

Substrate-neutral: a competitive market plus one primitive, self-replication.
Depends only on Mathlib (calculus + order + finite sums); self-contained,
cold-verifies with zero custom axioms.

PART A — the marginal / single-position results:
* `replication_wedge` — **Prop. 1 (envelope wedge).** Marginal value of spawning is
  `-(q a)·p'(a) - K'(a)`; the quantity-manipulation term cancels.
* `spawnProof_iff_fnp` — **Result 2.** Spawn-proof ⟺ false-name-proof.
* `no_beneficial_spawn_of_fnp` — FNP + convex cost ⟹ no spawn beats `a = 0`.
* `cap_iff` / `cap_mono` / `cap_collapse` — **Result 5+ (SWT position cap).**
  Decentralizable ⟺ `q ≤ k/θ`; the set shrinks monotonically in manipulability;
  costless identities collapse it to autarky.

PART B — the expansive welfare model (First Welfare Theorem, end-to-end):
* `Market`, `totalSurplus`, `payoff`, `NashEq`, `Efficient`, `FNP` — a reduced-form
  self-replicating market: gains from trade minus spawning dissipation (rents are
  transfers and cancel; only spawn costs are deadweight).
* `efficient_iff_zero` — an allocation is efficient iff no lineage spawns.
* `zero_nashEq_iff_fnp` — the no-spawn profile is a Nash equilibrium iff FNP.
* `efficient_nashEq_iff_fnp` — **First Welfare Theorem ⟺ FNP.** An efficient Nash
  equilibrium exists **iff** the mechanism is false-name-proof.
* `spawn_inefficient` — any equilibrium with positive spawning is strictly
  inefficient; the welfare loss is exactly the dissipation `∑ K` (Posner–Tullock).
* `fnp_of_marginal` — the marginal condition (`rent ≤ k`, governed by the position
  cap) implies the global FNP used by the welfare theorem — the two parts cohere.

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace PriceMarket

open Finset

/-! # PART A — marginal / single-position results -/

/-! ## The replication wedge (envelope theorem, Prop. 1) -/

/-- **Replication wedge.** Along the optimal-quantity path `q(a)` obeying the
competitive first-order condition `V'(q(a)) = p(a)` (encoded `HasDerivAt V (p a)
(q a)`), the marginal value of self-replication is `-(q a)·p'(a) - K'(a)`.  The
quantity-manipulation term vanishes by the envelope theorem; `qd` (the
optimal-quantity slope) does not appear on the right. -/
theorem replication_wedge
    {V p K q : ℝ → ℝ} {a qd pd Kd : ℝ}
    (hV : HasDerivAt V (p a) (q a))
    (hq : HasDerivAt q qd a)
    (hp : HasDerivAt p pd a)
    (hK : HasDerivAt K Kd a) :
    HasDerivAt (fun x => V (q x) - p x * q x - K x) (-(q a) * pd - Kd) a := by
  have hVq : HasDerivAt (fun x => V (q x)) (p a * qd) a := hV.comp a hq
  have hpq : HasDerivAt (fun x => p x * q x) (pd * q a + p a * qd) a := hp.mul hq
  have h := (hVq.sub hpq).sub hK
  convert h using 1
  ring

/-! ## Spawn-proofness and false-name-proofness (single position) -/

/-- Marginal spawn rent `q·θ` exceeds marginal identity cost `k`: a beneficial
spawn (`θ` = per-identity price impact / manipulability). -/
def BeneficialSpawn (q θ k : ℝ) : Prop := k < q * θ
/-- No beneficial spawn: the position is spawn-proof. -/
def SpawnProof (q θ k : ℝ) : Prop := q * θ ≤ k
/-- False-name-proof at this position. -/
def FalseNameProof (q θ k : ℝ) : Prop := ¬ BeneficialSpawn q θ k

/-- **Result 2 (corrected).** Spawn-proofness ⟺ false-name-proofness. -/
theorem spawnProof_iff_fnp (q θ k : ℝ) :
    SpawnProof q θ k ↔ FalseNameProof q θ k :=
  ⟨fun h => not_lt.mpr h, fun h => not_lt.mp h⟩

/-- **FWT direction (marginal).** Under FNP (`R ≤ k`) with convex spawn cost, no
spawn intensity beats not spawning. -/
theorem no_beneficial_spawn_of_fnp {R k : ℝ} {K : ℝ → ℝ}
    (hK0 : K 0 = 0) (hconv : ∀ a, 0 ≤ a → k * a ≤ K a) (hfnp : R ≤ k) :
    ∀ a, 0 ≤ a → R * a - K a ≤ R * 0 - K 0 := by
  intro a ha
  have h1 : k * a ≤ K a := hconv a ha
  have h2 : R * a ≤ k * a := mul_le_mul_of_nonneg_right hfnp ha
  rw [hK0]; nlinarith

/-! ## The position cap: Second Welfare Theorem as a monotone constitutional cost -/

/-- **Position cap.** With `θ > 0`, a position is spawn-proof iff `q ≤ k/θ`. -/
theorem cap_iff {q θ k : ℝ} (hθ : 0 < θ) : SpawnProof q θ k ↔ q ≤ k / θ := by
  unfold SpawnProof; rw [le_div_iff₀ hθ]

/-- **Monotone constitutional cost.** Lower manipulability ⟹ larger decentralizable
set. -/
theorem cap_mono {q θ₁ θ₂ k : ℝ} (hq : 0 ≤ q) (h : θ₁ ≤ θ₂)
    (hsp : SpawnProof q θ₂ k) : SpawnProof q θ₁ k := by
  unfold SpawnProof at hsp ⊢
  exact le_trans (mul_le_mul_of_nonneg_left h hq) hsp

/-- **Costless-identity collapse.** With `θ > 0` and `k ≤ 0`, only `q = 0` (autarky)
is spawn-proof. -/
theorem cap_collapse {q θ k : ℝ} (hθ : 0 < θ) (hq : 0 ≤ q)
    (hsp : SpawnProof q θ k) (hk : k ≤ 0) : q = 0 := by
  unfold SpawnProof at hsp
  have hle : q ≤ 0 := by nlinarith
  linarith

/-! # PART B — the expansive welfare model: First Welfare Theorem ⟺ FNP -/

variable {ι : Type*} [Fintype ι]

/-- Nonnegative spawn intensities. -/
def Feasible (a : ι → ℝ) : Prop := ∀ i, 0 ≤ a i

/-- A self-replicating market in reduced form: gains from trade `G` at the
competitive allocation, a per-unit terms-of-trade rent `rent i = q_i·θ` each lineage
manufactures by spawning, and a spawn cost `K i` — convex (`k i·a ≤ K i a`),
`K i 0 = 0`, strictly positive off `0`. -/
structure Market (ι : Type*) [Fintype ι] where
  G : ℝ
  rent : ι → ℝ
  K : ι → ℝ → ℝ
  k : ι → ℝ
  hK0 : ∀ i, K i 0 = 0
  hKpos : ∀ i (a : ℝ), 0 < a → 0 < K i a
  hKconv : ∀ i (a : ℝ), 0 ≤ a → k i * a ≤ K i a

namespace Market
variable (M : Market ι)

/-- Total surplus = gains from trade minus dissipation.  The terms-of-trade rents
are transfers between lineages and cancel in aggregate; only spawn costs are
deadweight. -/
def totalSurplus (a : ι → ℝ) : ℝ := M.G - ∑ i, M.K i (a i)

/-- Lineage `i`'s payoff: rent captured minus its own spawn cost. -/
def payoff (a : ι → ℝ) (i : ι) : ℝ := M.rent i * a i - M.K i (a i)

/-- No unilateral feasible deviation raises any lineage's payoff. -/
def NashEq (a : ι → ℝ) : Prop :=
  Feasible a ∧ ∀ i a', 0 ≤ a' → M.rent i * a' - M.K i a' ≤ M.payoff a i

/-- Maximizes total surplus over feasible profiles. -/
def Efficient (a : ι → ℝ) : Prop :=
  Feasible a ∧ ∀ a', Feasible a' → M.totalSurplus a' ≤ M.totalSurplus a

/-- False-name-proof: no lineage has a beneficial spawn at any intensity. -/
def FNP : Prop := ∀ i a', 0 ≤ a' → M.rent i * a' ≤ M.K i a'

lemma K_nonneg (i : ι) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ M.K i a := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, M.hK0]
  · exact (M.hKpos i a h).le

lemma totalSurplus_zero : M.totalSurplus (fun _ => 0) = M.G := by
  unfold totalSurplus; simp [M.hK0]

/-- Zero spawning maximizes total surplus. -/
lemma zero_efficient : M.Efficient (fun _ => 0) := by
  refine ⟨fun _ => le_refl 0, fun a' ha' => ?_⟩
  rw [M.totalSurplus_zero]; unfold totalSurplus
  have : (0:ℝ) ≤ ∑ i, M.K i (a' i) := Finset.sum_nonneg fun i _ => M.K_nonneg i (ha' i)
  linarith

/-- An allocation is efficient iff no lineage spawns. -/
lemma efficient_iff_zero (a : ι → ℝ) : M.Efficient a ↔ ∀ i, a i = 0 := by
  constructor
  · rintro ⟨hfeas, hmax⟩
    have h0 : M.totalSurplus (fun _ => 0) ≤ M.totalSurplus a := hmax _ (fun _ => le_refl 0)
    rw [M.totalSurplus_zero] at h0
    have hsum : ∑ i, M.K i (a i) = 0 := by
      have hnn : (0:ℝ) ≤ ∑ i, M.K i (a i) := Finset.sum_nonneg fun i _ => M.K_nonneg i (hfeas i)
      unfold totalSurplus at h0; linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => M.K_nonneg i (hfeas i)).mp hsum
    intro i
    by_contra hne
    have hpos : 0 < a i := lt_of_le_of_ne (hfeas i) (Ne.symm hne)
    have h1 := M.hKpos i (a i) hpos
    have h2 := hz i (Finset.mem_univ i)
    linarith
  · intro h
    have : a = (fun _ => 0) := funext h
    rw [this]; exact M.zero_efficient

/-- The no-spawn profile is a Nash equilibrium iff the mechanism is
false-name-proof. -/
lemma zero_nashEq_iff_fnp : M.NashEq (fun _ => 0) ↔ M.FNP := by
  unfold NashEq FNP payoff
  constructor
  · rintro ⟨_, h⟩ i a' ha'
    have := h i a' ha'
    simp only [mul_zero, M.hK0, sub_zero] at this
    linarith
  · intro h
    refine ⟨fun _ => le_refl 0, fun i a' ha' => ?_⟩
    have := h i a' ha'
    simp only [mul_zero, M.hK0, sub_zero]
    linarith

/-- **First Welfare Theorem ⟺ false-name-proofness.** A self-replicating market has
an efficient Nash equilibrium if and only if its mechanism is false-name-proof. -/
theorem efficient_nashEq_iff_fnp : (∃ a, M.Efficient a ∧ M.NashEq a) ↔ M.FNP := by
  constructor
  · rintro ⟨a, heff, hnash⟩
    have hz : a = (fun _ => 0) := funext ((M.efficient_iff_zero a).mp heff)
    rw [hz] at hnash
    exact (M.zero_nashEq_iff_fnp).mp hnash
  · intro hfnp
    exact ⟨fun _ => 0, M.zero_efficient, (M.zero_nashEq_iff_fnp).mpr hfnp⟩

/-- The welfare loss of any profile is exactly the dissipation `∑ K i (a i)`. -/
lemma surplus_loss (a : ι → ℝ) :
    M.totalSurplus (fun _ => 0) - M.totalSurplus a = ∑ i, M.K i (a i) := by
  rw [M.totalSurplus_zero]; unfold totalSurplus; ring

/-- **Posner–Tullock dissipation.** Any feasible profile with positive spawning is
strictly inefficient; the loss is the resources burned forking. -/
lemma spawn_inefficient (a : ι → ℝ) (hfeas : Feasible a) (i : ι) (hi : 0 < a i) :
    M.totalSurplus a < M.totalSurplus (fun _ => 0) := by
  have hpos : 0 < ∑ j, M.K j (a j) :=
    Finset.sum_pos' (fun j _ => M.K_nonneg j (hfeas j))
      ⟨i, Finset.mem_univ i, M.hKpos i (a i) hi⟩
  have := M.surplus_loss a; linarith

/-- The marginal condition (`rent ≤ k`, governed by the position cap of Part A)
implies the global false-name-proofness the welfare theorem uses — Parts A and B
cohere. -/
lemma fnp_of_marginal (h : ∀ i, M.rent i ≤ M.k i) : M.FNP := by
  intro i a' ha'
  calc M.rent i * a' ≤ M.k i * a' := mul_le_mul_of_nonneg_right (h i) ha'
    _ ≤ M.K i a' := M.hKconv i a' ha'

end Market
end PriceMarket
end SEKernel
