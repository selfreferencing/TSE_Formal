/-
Structural finite balancing helpers for Doc B A6.
Words retain every L/M/H position.  The reflection below is a concrete
involution on Fin s → Fin 3, not a scalar assumption about binomial masses.
The collapsed-plurality and general-majorization consumers are recorded in
the statement ledger when they are not yet formalized.
-/
import SEKernel.FirstAppearancePlurality
import SEKernel.FiniteProbability

namespace SEKernel.EpistemicConcentration

open Finset FiniteProbability
open scoped Classical

/-- The number of occurrences of one of L=0, M=1, H=2. -/
def symbolCount {s : ℕ} (z : Fin s → Fin 3) (a : Fin 3) : ℕ :=
  (Finset.univ.filter fun i => z i = a).card

theorem symbolCount_eq_sum {s : ℕ} (z : Fin s → Fin 3) (a : Fin 3) :
    symbolCount z a = ∑ i, if z i = a then 1 else 0 := by
  simp [symbolCount, Finset.sum_boole]

theorem symbolCount_sum {s : ℕ} (z : Fin s → Fin 3) :
    symbolCount z 0 + symbolCount z 1 + symbolCount z 2 = s := by
  rw [symbolCount_eq_sum, symbolCount_eq_sum, symbolCount_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    (∑ i, ((if z i = 0 then 1 else 0) + (if z i = 1 then 1 else 0) +
      (if z i = 2 then 1 else 0))) = ∑ _i : Fin s, 1 := by
        apply Finset.sum_congr rfl
        intro i _
        have h (a : Fin 3) : (if a=0 then 1 else 0) +
            (if a=1 then 1 else 0) + (if a=2 then 1 else 0) = (1:ℕ) := by
          fin_cases a <;> norm_num [Fin.ext_iff]
        exact h (z i)
    _ = s := by simp

/-- Interchange L and H and retain the M positions verbatim. -/
def reflect {s : ℕ} (z : Fin s → Fin 3) : Fin s → Fin 3 :=
  fun i => Equiv.swap 0 2 (z i)

theorem reflect_involutive {s : ℕ} (z : Fin s → Fin 3) :
    reflect (reflect z) = z := by
  funext i
  simp [reflect]

theorem symbolCount_reflect {s : ℕ} (z : Fin s → Fin 3) (a : Fin 3) :
    symbolCount (reflect z) a = symbolCount z (Equiv.swap 0 2 a) := by
  unfold symbolCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have ht := congrArg (Equiv.swap (0:Fin 3) 2) h
    simpa [reflect] using ht
  · intro h
    simp only [reflect]
    rw [h]
    simp

@[simp] theorem symbolCount_reflect_low {s : ℕ} (z : Fin s → Fin 3) :
    symbolCount (reflect z) 0 = symbolCount z 2 := by
  rw [symbolCount_reflect]; simp

@[simp] theorem symbolCount_reflect_mid {s : ℕ} (z : Fin s → Fin 3) :
    symbolCount (reflect z) 1 = symbolCount z 1 := by
  rw [symbolCount_reflect]; norm_num [Equiv.swap_apply_def, Fin.ext_iff]

@[simp] theorem symbolCount_reflect_high {s : ℕ} (z : Fin s → Fin 3) :
    symbolCount (reflect z) 2 = symbolCount z 0 := by
  rw [symbolCount_reflect]; simp

/-- Product mass for the L/M/H coupling, allowing zero-mass symbols. -/
def threeWeight (θ η : ℝ) (a : Fin 3) : ℝ :=
  if a=0 then θ else if a=1 then η-θ else 1-η

def wordMass {s : ℕ} (θ η : ℝ) (z : Fin s → Fin 3) : ℝ :=
  ∏ i, threeWeight θ η (z i)

theorem wordMass_counts {s : ℕ} (θ η : ℝ) (z : Fin s → Fin 3) :
    wordMass θ η z = θ^(symbolCount z 0) * (η-θ)^(symbolCount z 1) *
      (1-η)^(symbolCount z 2) := by
  have hp (a : Fin 3) : threeWeight θ η a =
      (if a=0 then θ else 1)*(if a=1 then η-θ else 1)*(if a=2 then 1-η else 1) := by
    fin_cases a <;> simp [threeWeight, Fin.ext_iff]
  unfold wordMass
  simp_rw [hp]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one, symbolCount]

theorem wordMass_nonneg {s : ℕ} (θ η : ℝ) (hθ : 0 ≤ θ) (hθη : θ ≤ η)
    (hη : η ≤ 1) (z : Fin s → Fin 3) : 0 ≤ wordMass θ η z := by
  have hm : 0 ≤ η-θ := sub_nonneg.mpr hθη
  have hh : 0 ≤ 1-η := sub_nonneg.mpr hη
  rw [wordMass_counts]
  positivity

/-- Exact algebra used by the reflection, including zero bases. -/
theorem power_swap_le {x y m : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hm : 0 ≤ m)
    {a b c : ℕ} (hca : c ≤ a) : x^a*m^b*y^c ≤ x^c*m^b*y^a := by
  have hy : 0 ≤ y := hx.trans hxy
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hca
  rw [pow_add, pow_add]
  calc
    x^c*x^d*m^b*y^c = (x^c*m^b*y^c)*x^d := by ring
    _ ≤ (x^c*m^b*y^c)*y^d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx hxy d) (by positivity)
    _ = x^c*m^b*(y^c*y^d) := by ring

/-- A loss word has no greater mass than its explicit reflected gain word. -/
theorem wordMass_reflect_ge {s : ℕ} (θ η : ℝ) (hθ : 0 ≤ θ)
    (hθη : θ ≤ η) (hη : η ≤ 1/2) (z : Fin s → Fin 3)
    (hcounts : symbolCount z 2 ≤ symbolCount z 0) :
    wordMass θ η z ≤ wordMass θ η (reflect z) := by
  rw [wordMass_counts, wordMass_counts,
    symbolCount_reflect_low, symbolCount_reflect_mid, symbolCount_reflect_high]
  exact power_swap_le hθ (by linarith) (sub_nonneg.mpr hθη) hcounts

/-- The central event for a fixed symbol count. -/
def central {s : ℕ} (ℓ : ℕ) (z : Fin s → Fin 3) (a : Fin 3) : Prop :=
  ℓ ≤ symbolCount z a ∧ symbolCount z a ≤ s-ℓ

theorem loss_count_order {s ℓ : ℕ} (z : Fin s → Fin 3)
    (hlow : central ℓ z 0) (hhigh : ¬ central ℓ z 2) :
    symbolCount z 2 ≤ symbolCount z 0 := by
  have hs := symbolCount_sum z
  unfold central at hlow hhigh
  omega

/-- Reflection is a bijection between the central-event loss and gain sets. -/
theorem reflect_loss_iff_gain {s ℓ : ℕ} (z : Fin s → Fin 3) :
    (central ℓ z 0 ∧ ¬ central ℓ z 2) ↔
      (central ℓ (reflect z) 2 ∧ ¬ central ℓ (reflect z) 0) := by
  simp [central]

/-- Finite central-interval balancing by a literal `Finset.sum_bij` on words.
This is the L/M/H coupling part of Doc B A6.1. -/
theorem central_word_mass_balancing {s ℓ : ℕ} (θ η : ℝ) (hθ : 0 ≤ θ)
    (hθη : θ ≤ η) (hη : η ≤ 1/2) :
    (∑ z : Fin s → Fin 3, if central ℓ z 0 then wordMass θ η z else 0) ≤
      ∑ z : Fin s → Fin 3, if central ℓ z 2 then wordMass θ η z else 0 := by
  classical
  let loss := Finset.univ.filter fun z : Fin s → Fin 3 => central ℓ z 0 ∧ ¬ central ℓ z 2
  let gain := Finset.univ.filter fun z : Fin s → Fin 3 => central ℓ z 2 ∧ ¬ central ℓ z 0
  have hbij : (∑ z ∈ loss, wordMass θ η (reflect z)) = ∑ z ∈ gain, wordMass θ η z := by
    apply Finset.sum_bij (fun z _ => reflect z)
    · intro z hz
      simp only [loss, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simpa [gain] using (reflect_loss_iff_gain z).1 hz
    · intro z hz z' hz' heq
      have ht := congrArg reflect heq
      simpa only [reflect_involutive] using ht
    · intro z hz
      refine ⟨reflect z, ?_, reflect_involutive z⟩
      have ht : central ℓ z 2 ∧ ¬ central ℓ z 0 := by simpa [gain] using hz
      simpa [loss, central] using ht
    · intro z _; rfl
  have hmass : (∑ z ∈ loss, wordMass θ η z) ≤ ∑ z ∈ gain, wordMass θ η z := by
    rw [← hbij]
    apply Finset.sum_le_sum
    intro z hz
    have ht : central ℓ z 0 ∧ ¬ central ℓ z 2 := by simpa [loss] using hz
    exact wordMass_reflect_ge θ η hθ hθη hη z (loss_count_order z ht.1 ht.2)
  have hdecomp :
      (∑ z : Fin s → Fin 3, if central ℓ z 0 then wordMass θ η z else 0) -
      (∑ z : Fin s → Fin 3, if central ℓ z 2 then wordMass θ η z else 0) =
      (∑ z ∈ loss, wordMass θ η z) - ∑ z ∈ gain, wordMass θ η z := by
    simp only [loss, gain, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hl : central ℓ z 0 <;> by_cases hh : central ℓ z 2 <;> simp [hl, hh]
  linarith

/-- Exact finite layer cake for a symmetric function, including both endpoints.
No differentiability or external stochastic-order theorem is used. -/
theorem symmetric_layer_cake (s : ℕ) (g : ℕ → ℝ)
    (hsym : ∀ a, a ≤ s → g a = g (s-a)) (a : ℕ) (ha : a ≤ s) :
    g a = g 0 + ∑ j ∈ Finset.range (s/2),
      if j+1 ≤ a ∧ a ≤ s-(j+1) then g (j+1)-g j else 0 := by
  have hfilter : (Finset.range (s/2)).filter
      (fun j => j+1 ≤ a ∧ a ≤ s-(j+1)) = Finset.range (min a (s-a)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hmin : g (min a (s-a)) = g a := by
    by_cases h : a ≤ s-a
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega)]
      exact (hsym a ha).symm
  rw [← Finset.sum_filter, hfilter, Finset.sum_range_sub, hmin]
  ring

/-- Weighted layer cake consumes the reflected central-event inequalities.
It formalizes the symmetric reward conclusion of Doc B A6.1 directly on
independent L/M/H words. -/
theorem symmetric_word_mass_balancing {s : ℕ} (θ η : ℝ) (hθ : 0 ≤ θ)
    (hθη : θ ≤ η) (hη : η ≤ 1/2) (g : ℕ → ℝ)
    (hsym : ∀ a, a ≤ s → g a = g (s-a))
    (hmono : ∀ j, j < s/2 → g j ≤ g (j+1)) :
    (∑ z : Fin s → Fin 3, wordMass θ η z * g (symbolCount z 0)) ≤
      ∑ z : Fin s → Fin 3, wordMass θ η z * g (symbolCount z 2) := by
  have hlayer (z : Fin s → Fin 3) (a : Fin 3) :
      g (symbolCount z a) = g 0 + ∑ j ∈ Finset.range (s/2),
        if central (j+1) z a then g (j+1)-g j else 0 := by
    rw [symmetric_layer_cake s g hsym (symbolCount z a)
      (Finset.card_filter_le _ _ |>.trans (by simp))]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j+1 ≤ symbolCount z a ∧ symbolCount z a ≤ s-(j+1) <;>
      simp [central, h]
  simp_rw [hlayer, mul_add, Finset.sum_add_distrib]
  apply add_le_add_right
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  have hd : 0 ≤ g (j+1)-g j := sub_nonneg.mpr (hmono j (Finset.mem_range.mp hj))
  have hid (a : Fin 3) :
      (∑ z : Fin s → Fin 3, wordMass θ η z *
        (if central (j+1) z a then g (j+1)-g j else 0)) =
      (∑ z : Fin s → Fin 3, if central (j+1) z a then wordMass θ η z else 0) *
        (g (j+1)-g j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : central (j+1) z a <;> simp [h]
  rw [hid, hid]
  exact mul_le_mul_of_nonneg_right (central_word_mass_balancing θ η hθ hθη hη) hd

/-- The normalized single-coordinate law of the explicit balancing coupling. -/
noncomputable def balancingLaw (θ η : ℝ) (hθ : 0 ≤ θ) (hθη : θ ≤ η)
    (hη : η ≤ 1/2) : Law (Fin 3) where
  mass := threeWeight θ η
  nonneg a := by
    unfold threeWeight
    split_ifs <;> linarith
  total := by
    change (∑ a : Fin 3, threeWeight θ η a) = 1
    rw [Fin.sum_univ_succ, Fin.sum_univ_two]
    change threeWeight θ η 0 + (threeWeight θ η 1 + threeWeight θ η 2) = 1
    norm_num [threeWeight, Fin.ext_iff]

/-- The L/M/H product law's central interval probability for #L is at most
that for #L+#M.  Both marginals are generated on separate IID coordinates. -/
theorem central_probability_balancing {s ℓ : ℕ} (θ η : ℝ) (hθ : 0 ≤ θ)
    (hθη : θ ≤ η) (hη : η ≤ 1/2) :
    (Law.pi (fun _ : Fin s => balancingLaw θ η hθ hθη hη)).prob
      (fun z => ℓ ≤ symbolCount z 0 ∧ symbolCount z 0 ≤ s-ℓ) ≤
    (Law.pi (fun _ : Fin s => balancingLaw θ η hθ hθη hη)).prob
      (fun z => ℓ ≤ symbolCount z 0+symbolCount z 1 ∧
        symbolCount z 0+symbolCount z 1 ≤ s-ℓ) := by
  have he (z : Fin s → Fin 3) :
      (ℓ ≤ symbolCount z 0+symbolCount z 1 ∧
        symbolCount z 0+symbolCount z 1 ≤ s-ℓ) ↔ central ℓ z 2 := by
    have hs := symbolCount_sum z
    unfold central
    omega
  simp_rw [he]
  simpa only [Law.prob, Law.pi, balancingLaw, wordMass, central] using
    central_word_mass_balancing (s:=s) (ℓ:=ℓ) θ η hθ hθη hη

/-- The layer-cake conclusion expressed as a normalized finite expectation
of X=#L and Y=#L+#M, on the same actual coupling words. -/
theorem symmetric_expectation_balancing {s : ℕ} (θ η : ℝ) (hθ : 0 ≤ θ)
    (hθη : θ ≤ η) (hη : η ≤ 1/2) (g : ℕ → ℝ)
    (hsym : ∀ a, a ≤ s → g a = g (s-a))
    (hmono : ∀ j, j < s/2 → g j ≤ g (j+1)) :
    (Law.pi (fun _ : Fin s => balancingLaw θ η hθ hθη hη)).expect
      (fun z => g (symbolCount z 0)) ≤
    (Law.pi (fun _ : Fin s => balancingLaw θ η hθ hθη hη)).expect
      (fun z => g (symbolCount z 0+symbolCount z 1)) := by
  have hg (z : Fin s → Fin 3) : g (symbolCount z 2) =
      g (symbolCount z 0+symbolCount z 1) := by
    have hs := symbolCount_sum z
    rw [hsym _ (by omega)]
    congr 1
    omega
  have hb := symmetric_word_mass_balancing θ η hθ hθη hη g hsym hmono
  simp_rw [hg] at hb
  simpa only [Law.expect, Law1.mean, Law.pi, balancingLaw, wordMass] using hb

/-- A word containing a zero-mass label has exactly zero product mass. -/
theorem zero_label_word_mass {A : Type*} [Fintype A]
    (π : Law (Option A)) (s : ℕ) (a : Option A) (ha : π.mass a = 0)
    (z : Epistemic.OrderedWord s A) (hz : ∃ i, z i = a) :
    (Epistemic.iidWordLaw π s).mass z = 0 := by
  obtain ⟨i, hi⟩ := hz
  unfold Epistemic.iidWordLaw Law.pi
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa only [hi] using ha)

/-- Zero-mass labels are inert for every event, without a conditional-law
argument on a null event. -/
theorem zero_label_event_restriction {A : Type*} [Fintype A]
    (π : Law (Option A)) (s : ℕ) (a : Option A) (ha : π.mass a = 0)
    (E : Epistemic.OrderedWord s A → Prop) :
    (Epistemic.iidWordLaw π s).prob E =
      (Epistemic.iidWordLaw π s).prob (fun z => E z ∧ ∀ i, z i ≠ a) := by
  classical
  unfold Law.prob
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : ∃ i, z i = a
  · have hm := zero_label_word_mass π s a ha z hz
    simp [hm]
  · have hn : ∀ i, z i ≠ a := by simpa using hz
    simp [hn]

end SEKernel.EpistemicConcentration
