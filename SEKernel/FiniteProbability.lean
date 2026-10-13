/-
Finite probability for the Chile epistemic-evolution extension.
All probability objects are explicit normalized finite mass functions.
Expectation and variance use the existing Law1 definitions verbatim.
-/
import SEKernel.Law1_Selection

namespace SEKernel.FiniteProbability

open Finset

/-- A probability law on an explicitly finite sample space. -/
structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

namespace Law

variable {Ω Λ Ξ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Ξ]

/-- Finite expectation, definitionally the kernel's existing weighted mean. -/
abbrev expect (L : Law Ω) (X : Ω → ℝ) : ℝ := Law1.mean L.mass X

/-- Finite variance, definitionally the kernel's existing variance. -/
abbrev variance (L : Law Ω) (X : Ω → ℝ) : ℝ := Law1.variance L.mass X

/-- Probability of an event. No arbitrary conditional value is introduced. -/
noncomputable def prob (L : Law Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then L.mass ω else 0

/-- Finite covariance. -/
def covariance (L : Law Ω) (X Y : Ω → ℝ) : ℝ :=
  L.expect (fun ω => (X ω - L.expect X) * (Y ω - L.expect Y))

@[simp] theorem expect_const (L : Law Ω) (c : ℝ) :
    L.expect (fun _ => c) = c := by
  simp only [expect, Law1.mean, ← Finset.sum_mul, L.total, one_mul]

theorem expect_add (L : Law Ω) (X Y : Ω → ℝ) :
    L.expect (fun ω => X ω + Y ω) = L.expect X + L.expect Y := by
  simp [expect, Law1.mean, mul_add, Finset.sum_add_distrib]

theorem expect_sub (L : Law Ω) (X Y : Ω → ℝ) :
    L.expect (fun ω => X ω - Y ω) = L.expect X - L.expect Y := by
  simp [expect, Law1.mean, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (L : Law Ω) (X : Ω → ℝ) (c : ℝ) :
    L.expect (fun ω => X ω * c) = L.expect X * c := by
  simp only [expect, Law1.mean, ← mul_assoc, Finset.sum_mul]

theorem expect_const_mul (L : Law Ω) (c : ℝ) (X : Ω → ℝ) :
    L.expect (fun ω => c * X ω) = c * L.expect X := by
  simpa only [mul_comm] using L.expect_mul_const X c

theorem expect_finset_sum {ι : Type*} (L : Law Ω) (s : Finset ι)
    (X : ι → Ω → ℝ) :
    L.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, L.expect (X i) := by
  simp only [expect, Law1.mean, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expect_sum {ι : Type*} [Fintype ι] (L : Law Ω) (X : ι → Ω → ℝ) :
    L.expect (fun ω => ∑ i, X i ω) = ∑ i, L.expect (X i) :=
  L.expect_finset_sum Finset.univ X

@[simp] theorem expect_centered (L : Law Ω) (X : Ω → ℝ) :
    L.expect (fun ω => X ω - L.expect X) = 0 := by
  rw [L.expect_sub, L.expect_const]
  exact sub_self _

theorem expect_mono (L : Law Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    L.expect X ≤ L.expect Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (L.nonneg ω)

theorem expect_nonneg (L : Law Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) :
    0 ≤ L.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (L.nonneg ω) (h ω)

@[simp] theorem prob_false (L : Law Ω) : L.prob (fun _ => False) = 0 := by
  simp [prob]

@[simp] theorem prob_true (L : Law Ω) : L.prob (fun _ => True) = 1 := by
  simp [prob, L.total]

theorem prob_nonneg (L : Law Ω) (E : Ω → Prop) : 0 ≤ L.prob E := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs; exact L.nonneg ω; rfl

theorem prob_mono (L : Law Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    L.prob E ≤ L.prob F := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · simp [he, h ω he]
  · simp only [he, ↓reduceIte]
    split_ifs; exact L.nonneg ω; rfl

theorem prob_le_one (L : Law Ω) (E : Ω → Prop) : L.prob E ≤ 1 := by
  simpa using L.prob_mono (E := E) (F := fun _ => True) (fun _ _ => trivial)

theorem prob_compl (L : Law Ω) (E : Ω → Prop) :
    L.prob (fun ω => ¬ E ω) = 1 - L.prob E := by
  classical
  have h : L.prob E + L.prob (fun ω => ¬ E ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib]
    convert L.total using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : E ω <;> simp [hω]
  linarith

theorem prob_union_le (L : Law Ω) (E F : Ω → Prop) :
    L.prob (fun ω => E ω ∨ F ω) ≤ L.prob E + L.prob F := by
  classical
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω <;> simp [he, hf, L.nonneg ω]

/-- Finite union bound, including an empty indexing type. -/
theorem prob_exists_le {ι : Type*} [Fintype ι] (L : Law Ω) (E : ι → Ω → Prop) :
    L.prob (fun ω => ∃ i, E i ω) ≤ ∑ i, L.prob (E i) := by
  classical
  rw [prob]
  simp only [prob, Finset.sum_comm (f := fun i ω => if E i ω then L.mass ω else 0)]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ i, E i ω
  · obtain ⟨i, hi⟩ := h
    simp only [show (∃ j, E j ω) from ⟨i, hi⟩, ↓reduceIte]
    calc
      L.mass ω = if E i ω then L.mass ω else 0 := by simp [hi]
      _ ≤ ∑ j, if E j ω then L.mass ω else 0 :=
        Finset.single_le_sum (f := fun j => if E j ω then L.mass ω else 0)
          (fun j _ => by dsimp only; split_ifs; exact L.nonneg ω; rfl) (Finset.mem_univ i)
  · simp only [h, ↓reduceIte]
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact L.nonneg ω; rfl)

theorem expect_indicator (L : Law Ω) (E : Ω → Prop) [DecidablePred E] :
    L.expect (fun ω => if E ω then 1 else 0) = L.prob E := by
  classical
  simp only [expect, Law1.mean, prob]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω <;> simp [he]

/-- Unnormalized expectation on one event. -/
noncomputable def cellExpect (L : Law Ω) (X : Ω → ℝ) (E : Ω → Prop) : ℝ := by
  classical
  exact L.expect (fun ω => if E ω then X ω else 0)

/-- Zero is used on null cells; only the mass-weighted value is subsequently used. -/
noncomputable def conditionalMean (L : Law Ω) (X : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  L.cellExpect X E / L.prob E

theorem mass_eq_zero_of_prob_eq_zero (L : Law Ω) (E : Ω → Prop)
    (hE : L.prob E = 0) {ω : Ω} (hω : E ω) : L.mass ω = 0 := by
  classical
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a ∈ (Finset.univ : Finset Ω)) =>
      show 0 ≤ (if E a then L.mass a else 0) by
        split_ifs; exact L.nonneg a; rfl)).1 hE
  simpa only [hω, ↓reduceIte] using hall ω (Finset.mem_univ ω)

theorem cellExpect_eq_zero_of_prob_eq_zero (L : Law Ω) (X : Ω → ℝ) (E : Ω → Prop)
    (hE : L.prob E = 0) : L.cellExpect X E = 0 := by
  classical
  unfold cellExpect expect Law1.mean
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hω : E ω
  · simp [hω, L.mass_eq_zero_of_prob_eq_zero E hE hω]
  · simp [hω]

theorem prob_mul_conditionalMean (L : Law Ω) (X : Ω → ℝ) (E : Ω → Prop) :
    L.prob E * L.conditionalMean X E = L.cellExpect X E := by
  by_cases hE : L.prob E = 0
  · rw [hE, zero_mul, L.cellExpect_eq_zero_of_prob_eq_zero X E hE]
  · unfold conditionalMean
    field_simp

/-- The law of total expectation for an explicitly given finite partition. -/
theorem total_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Law Ω) (X : Ω → ℝ) (cell : Ω → ι) :
    L.expect X = ∑ i, L.prob (fun ω => cell ω = i) *
      L.conditionalMean X (fun ω => cell ω = i) := by
  classical
  simp only [L.prob_mul_conditionalMean, cellExpect, expect, Law1.mean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [mul_ite]

theorem variance_nonneg (L : Law Ω) (X : Ω → ℝ) : 0 ≤ L.variance X :=
  Law1.variance_nonneg L.nonneg

theorem variance_eq (L : Law Ω) (X : Ω → ℝ) :
    L.variance X = L.expect (fun ω => X ω ^ 2) - L.expect X ^ 2 :=
  Law1.variance_eq L.total

/-- An event indicator bounded by a nonnegative observable bounds its probability. -/
theorem prob_le_expect (L : Law Ω) (E : Ω → Prop) {Z : Ω → ℝ}
    (hZ : ∀ ω, 0 ≤ Z ω) (hE : ∀ ω, E ω → 1 ≤ Z ω) :
    L.prob E ≤ L.expect Z := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · simpa only [he, ↓reduceIte, mul_one] using
      mul_le_mul_of_nonneg_left (hE ω he) (L.nonneg ω)
  · simpa only [he, ↓reduceIte] using mul_nonneg (L.nonneg ω) (hZ ω)

/-- Finite Markov inequality proved by a pointwise indicator bound. -/
theorem markov (L : Law Ω) {Z : Ω → ℝ} (hZ : ∀ ω, 0 ≤ Z ω)
    {c : ℝ} (hc : 0 < c) :
    L.prob (fun ω => c ≤ Z ω) ≤ L.expect Z / c := by
  classical
  apply (le_div_iff₀ hc).2
  rw [prob, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hz : c ≤ Z ω
  · simpa [hz] using mul_le_mul_of_nonneg_left hz (L.nonneg ω)
  · simpa [hz] using mul_nonneg (L.nonneg ω) (hZ ω)

/-- The equivalent probability-times-threshold form avoids division. -/
theorem markov_mul (L : Law Ω) {Z : Ω → ℝ} (hZ : ∀ ω, 0 ≤ Z ω)
    {c : ℝ} (hc : 0 < c) :
    L.prob (fun ω => c ≤ Z ω) * c ≤ L.expect Z :=
  (le_div_iff₀ hc).1 (L.markov hZ hc)

/-- Finite Chebyshev inequality, with the actual law's variance. -/
theorem chebyshev (L : Law Ω) (X : Ω → ℝ) {ε : ℝ} (hε : 0 < ε) :
    L.prob (fun ω => ε ≤ |X ω - L.expect X|) ≤ L.variance X / ε ^ 2 := by
  have hevent : L.prob (fun ω => ε ≤ |X ω - L.expect X|) ≤
      L.prob (fun ω => ε ^ 2 ≤ (X ω - L.expect X) ^ 2) := by
    apply L.prob_mono
    intro ω hω
    nlinarith [sq_nonneg (|X ω - L.expect X| - ε),
      sq_abs (X ω - L.expect X)]
  exact hevent.trans (L.markov (fun ω => sq_nonneg _) (sq_pos_of_pos hε))

/-- Centering removes the linear term in a shifted square. -/
theorem shifted_square (L : Law Ω) (X : Ω → ℝ) (b : ℝ) :
    L.expect (fun ω => (X ω - L.expect X + b) ^ 2) = L.variance X + b ^ 2 := by
  have hpoint : (fun ω => (X ω - L.expect X + b) ^ 2) =
      (fun ω => (X ω - L.expect X) ^ 2 +
        (2 * b) * (X ω - L.expect X) + b ^ 2) := by
    funext ω
    ring
  rw [hpoint, L.expect_add, L.expect_add, L.expect_const_mul,
    L.expect_sub, L.expect_const, L.expect_const]
  simp [variance, Law1.variance, expect, Law1.mean]

/-- One-sided finite Cantelli inequality; zero variance is included. -/
theorem cantelli (L : Law Ω) (X : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    L.prob (fun ω => L.expect X + t ≤ X ω) ≤
      L.variance X / (L.variance X + t ^ 2) := by
  let v := L.variance X
  let b := v / t
  have hv : 0 ≤ v := L.variance_nonneg X
  have hb : 0 ≤ b := div_nonneg hv ht.le
  have htb : 0 < t + b := by linarith
  have hevent : L.prob (fun ω => L.expect X + t ≤ X ω) ≤
      L.prob (fun ω => (t + b) ^ 2 ≤ (X ω - L.expect X + b) ^ 2) := by
    apply L.prob_mono
    intro ω hω
    nlinarith [sq_nonneg (X ω - L.expect X - t)]
  have hbound := L.markov (fun ω => sq_nonneg (X ω - L.expect X + b))
    (sq_pos_of_pos htb)
  rw [L.shifted_square X b] at hbound
  have hden : 0 < v + t ^ 2 := by positivity
  have halg : (v + b ^ 2) / (t + b) ^ 2 = v / (v + t ^ 2) := by
    dsimp [b]
    field_simp
    all_goals ring
  change L.prob _ ≤ (v + b ^ 2) / (t + b) ^ 2 at hbound
  rw [halg] at hbound
  exact hevent.trans hbound

/-- Product of two independent finite laws. -/
def prod (L : Law Ω) (K : Law Λ) : Law (Ω × Λ) where
  mass ω := L.mass ω.1 * K.mass ω.2
  nonneg ω := mul_nonneg (L.nonneg ω.1) (K.nonneg ω.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, K.total, mul_one, L.total]

@[simp] theorem prod_mass (L : Law Ω) (K : Law Λ) (ω : Ω) (η : Λ) :
    (L.prod K).mass (ω, η) = L.mass ω * K.mass η := rfl

/-- Independent finite product, including the empty product. -/
noncomputable def pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ωs : ι → Type*} [∀ i, Fintype (Ωs i)]
    (Ls : ∀ i, Law (Ωs i)) : Law (∀ i, Ωs i) where
  mass ω := ∏ i, (Ls i).mass (ω i)
  nonneg ω := Finset.prod_nonneg (fun i _ => (Ls i).nonneg (ω i))
  total := by
    rw [← Fintype.prod_sum]
    simp [fun i => (Ls i).total]

/-- Every product-coordinate observable has the expected product moment. -/
theorem expect_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ωs : ι → Type*} [∀ i, Fintype (Ωs i)]
    (Ls : ∀ i, Law (Ωs i)) (g : ∀ i, Ωs i → ℝ) :
    (pi Ls).expect (fun z => ∏ i, g i (z i)) = ∏ i, (Ls i).expect (g i) := by
  simp only [expect, Law1.mean, pi]
  calc
    (∑ z : ∀ i, Ωs i, (∏ i, (Ls i).mass (z i)) * ∏ i, g i (z i)) =
        ∑ z : ∀ i, Ωs i, ∏ i, (Ls i).mass (z i) * g i (z i) := by
      apply Finset.sum_congr rfl
      intro z _
      exact Finset.prod_mul_distrib.symm
    _ = ∏ i, ∑ a, (Ls i).mass a * g i a := (Fintype.prod_sum (fun i a => (Ls i).mass a * g i a)).symm

/-- The marginal law of a coordinate of an independent product is its input law. -/
theorem expect_pi_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ls : ι → Law Ω) (i : ι) (X : Ω → ℝ) :
    (pi Ls).expect (fun z => X (z i)) = (Ls i).expect X := by
  have h := expect_pi_prod Ls (fun j a => if j = i then X a else 1)
  have hp : (fun z : ι → Ω => ∏ j, if j = i then X (z j) else 1) =
      (fun z => X (z i)) := by
    funext z
    exact Fintype.prod_ite_eq' i _
  have he : ∀ j, (Ls j).expect (fun a => if j = i then X a else 1) =
      if j = i then (Ls j).expect X else 1 := by
    intro j
    by_cases hj : j = i <;> simp [hj]
  simpa only [hp, he, Fintype.prod_ite_eq'] using h

/-- Explicit separate-coordinate independence for two distinct coordinates. -/
theorem expect_pi_coord_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ls : ι → Law Ω) {i j : ι} (hij : i ≠ j) (X Y : Ω → ℝ) :
    (pi Ls).expect (fun z => X (z i) * Y (z j)) =
      (Ls i).expect X * (Ls j).expect Y := by
  have h := expect_pi_prod Ls
    (fun k a => (if k = i then X a else 1) * (if k = j then Y a else 1))
  have hp : (fun z : ι → Ω => ∏ k,
      (if k = i then X (z k) else 1) * (if k = j then Y (z k) else 1)) =
      (fun z => X (z i) * Y (z j)) := by
    funext z
    rw [Finset.prod_mul_distrib]
    simp only [Fintype.prod_ite_eq']
  have he : ∀ k, (Ls k).expect (fun a =>
        (if k = i then X a else 1) * (if k = j then Y a else 1)) =
      (if k = i then (Ls k).expect X else 1) *
        (if k = j then (Ls k).expect Y else 1) := by
    intro k
    by_cases hi : k = i <;> by_cases hj : k = j
    · exact False.elim (hij (hi.symm.trans hj))
    · simp [hi, hij]
    · simp [hj, Ne.symm hij]
    · simp [hi, hj]
  simpa only [hp, he, Finset.prod_mul_distrib, Fintype.prod_ite_eq'] using h

/-- Variance additivity on one finite law, with the exact mixed-moment premise. -/
theorem variance_sum_of_uncorrelated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Law Ω) (X : ι → Ω → ℝ)
    (hmixed : ∀ i j, i ≠ j → L.expect (fun ω => X i ω * X j ω) =
      L.expect (X i) * L.expect (X j)) :
    L.variance (fun ω => ∑ i, X i ω) = ∑ i, L.variance (X i) := by
  let C := fun i ω => X i ω - L.expect (X i)
  have hcross : ∀ i j, i ≠ j → L.expect (fun ω => C i ω * C j ω) = 0 := by
    intro i j hij
    have hp : (fun ω => C i ω * C j ω) = (fun ω =>
        X i ω * X j ω - L.expect (X j) * X i ω -
          L.expect (X i) * X j ω + L.expect (X i) * L.expect (X j)) := by
      funext ω
      dsimp [C]
      ring
    rw [hp, L.expect_add, L.expect_sub, L.expect_sub,
      L.expect_const_mul, L.expect_const_mul, L.expect_const, hmixed i j hij]
    ring
  have hcenter : (fun ω => (∑ i, X i ω) - L.expect (fun ω => ∑ i, X i ω)) =
      (fun ω => ∑ i, C i ω) := by
    funext ω
    rw [L.expect_sum, ← Finset.sum_sub_distrib]
  change L.expect (fun ω => ((∑ i, X i ω) -
    L.expect (fun ω => ∑ i, X i ω)) ^ 2) = _
  have hp : (fun ω => ((∑ i, X i ω) -
      L.expect (fun ω => ∑ i, X i ω)) ^ 2) =
      (fun ω => ∑ i, ∑ j, C i ω * C j ω) := by
    funext ω
    have hc := congrFun hcenter ω
    rw [hc, pow_two, Finset.sum_mul_sum]
  rw [hp, L.expect_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [L.expect_sum]
  rw [Finset.sum_eq_single i]
  · simp only [expect, Law1.mean, variance, Law1.variance, C, pow_two]
  · intro j _ hji
    exact hcross i j (Ne.symm hji)
  · simp

/-- General finite product variance: each observable uses its own coordinate. -/
theorem variance_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ls : ι → Law Ω) (X : ι → Ω → ℝ) :
    (pi Ls).variance (fun z => ∑ i, X i (z i)) = ∑ i, (Ls i).variance (X i) := by
  rw [(pi Ls).variance_sum_of_uncorrelated (fun i z => X i (z i))]
  · apply Finset.sum_congr rfl
    intro i _
    rw [(pi Ls).variance_eq, (Ls i).variance_eq,
      expect_pi_coord Ls i (fun a => X i a ^ 2), expect_pi_coord]
  · intro i j hij
    rw [expect_pi_coord_mul Ls hij, expect_pi_coord, expect_pi_coord]

/-- Scaling an observable scales variance by the square of the constant. -/
theorem variance_const_mul (L : Law Ω) (c : ℝ) (X : Ω → ℝ) :
    L.variance (fun ω => c * X ω) = c ^ 2 * L.variance X := by
  rw [L.variance_eq, L.expect_const_mul, L.variance_eq]
  have hp : (fun ω => (c * X ω) ^ 2) = (fun ω => c ^ 2 * X ω ^ 2) := by
    funext ω
    ring
  rw [hp, L.expect_const_mul]
  ring

/-- Iid empirical means, with independence represented by separate coordinates. -/
theorem iid_average {n : ℕ} (hn : 0 < n) (L : Law Ω) (X : Ω → ℝ) :
    let P := pi (fun _ : Fin n => L)
    P.expect (fun z => (∑ i, X (z i)) / n) = L.expect X ∧
      P.variance (fun z => (∑ i, X (z i)) / n) = L.variance X / n := by
  dsimp only
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  constructor
  · simp only [div_eq_mul_inv]
    rw [(pi _).expect_mul_const, (pi _).expect_sum]
    simp only [expect_pi_coord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  · simp only [div_eq_mul_inv, mul_comm (∑ _, _) (n : ℝ)⁻¹]
    rw [(pi _).variance_const_mul, variance_pi_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- Finite stochastic kernel application, with normalized law rows. -/
def bind (L : Law Ω) (K : Ω → Law Λ) : Law Λ where
  mass η := ∑ ω, L.mass ω * (K ω).mass η
  nonneg η := Finset.sum_nonneg fun ω _ => mul_nonneg (L.nonneg ω) ((K ω).nonneg η)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, fun ω => (K ω).total, mul_one, L.total]

/-- Deterministic pushforward; no positive-cell assumptions are needed. -/
noncomputable def map (L : Law Ω) (f : Ω → Λ) : Law Λ := by
  classical
  exact {
    mass := fun η => L.prob (fun ω => f ω = η)
    nonneg := fun η => L.prob_nonneg _
    total := by
      simp only [prob]
      rw [Finset.sum_comm]
      simp [L.total] }

theorem expect_bind (L : Law Ω) (K : Ω → Law Λ) (X : Λ → ℝ) :
    (L.bind K).expect X = L.expect (fun ω => (K ω).expect X) := by
  simp only [expect, Law1.mean, bind, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  ring

theorem expect_map (L : Law Ω) (f : Ω → Λ) (X : Λ → ℝ) :
    (L.map f).expect X = L.expect (fun ω => X (f ω)) := by
  classical
  simp only [expect, Law1.mean, map, prob, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

/-- Functions of separate product coordinates have factored moments. -/
theorem expect_prod_mul (L : Law Ω) (K : Law Λ) (X : Ω → ℝ) (Y : Λ → ℝ) :
    (L.prod K).expect (fun ω => X ω.1 * Y ω.2) = L.expect X * K.expect Y := by
  simp only [expect, Law1.mean, prod, Fintype.sum_prod_type]
  simp_rw [show ∀ ω η, L.mass ω * K.mass η * (X ω * Y η) =
    (L.mass ω * X ω) * (K.mass η * Y η) from fun _ _ => by ring]
  rw [Finset.sum_mul_sum]

theorem expect_prod_fst (L : Law Ω) (K : Law Λ) (X : Ω → ℝ) :
    (L.prod K).expect (fun ω => X ω.1) = L.expect X := by
  simpa using L.expect_prod_mul K X (fun _ => 1)

theorem expect_prod_snd (L : Law Ω) (K : Law Λ) (Y : Λ → ℝ) :
    (L.prod K).expect (fun ω => Y ω.2) = K.expect Y := by
  simpa using L.expect_prod_mul K (fun _ => 1) Y

/-- Product-coordinate variance additivity: independence is constructive. -/
theorem variance_prod_add (L : Law Ω) (K : Law Λ) (X : Ω → ℝ) (Y : Λ → ℝ) :
    (L.prod K).variance (fun ω => X ω.1 + Y ω.2) = L.variance X + K.variance Y := by
  rw [(L.prod K).variance_eq, L.variance_eq, K.variance_eq]
  have hm : (L.prod K).expect (fun ω => X ω.1 + Y ω.2) = L.expect X + K.expect Y := by
    rw [(L.prod K).expect_add, L.expect_prod_fst, L.expect_prod_snd]
  have hs : (L.prod K).expect (fun ω => (X ω.1 + Y ω.2) ^ 2) =
      L.expect (fun ω => X ω ^ 2) + 2 * (L.expect X * K.expect Y) +
        K.expect (fun ω => Y ω ^ 2) := by
    have hp : (fun ω : Ω × Λ => (X ω.1 + Y ω.2) ^ 2) =
        (fun ω => X ω.1 ^ 2 + 2 * (X ω.1 * Y ω.2) + Y ω.2 ^ 2) := by
      funext ω
      ring
    rw [hp, (L.prod K).expect_add, (L.prod K).expect_add,
      (L.prod K).expect_const_mul, L.expect_prod_fst K (fun ω => X ω ^ 2),
      L.expect_prod_snd K (fun η => Y η ^ 2), L.expect_prod_mul]
  rw [hm, hs]
  ring

end Law

/-- A finite stochastic kernel, implemented as a law for each input. -/
abbrev Kernel (Ω Λ : Type*) [Fintype Λ] := Ω → Law Λ

namespace Kernel

variable {Ω Λ Ξ : Type*} [Fintype Λ] [Fintype Ξ]

/-- Matrix multiplication of normalized finite kernels. -/
def comp (K : Kernel Ω Λ) (H : Kernel Λ Ξ) : Kernel Ω Ξ :=
  fun ω => (K ω).bind H

@[simp] theorem comp_mass (K : Kernel Ω Λ) (H : Kernel Λ Ξ) (ω : Ω) (ξ : Ξ) :
    (comp K H ω).mass ξ = ∑ η, (K ω).mass η * (H η).mass ξ := rfl

end Kernel
end SEKernel.FiniteProbability
