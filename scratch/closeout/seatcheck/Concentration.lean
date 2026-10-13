/-
Close-out pass, Doc B A6.2–A6.5: concentrating wrong answers.

* A6.2 (one balancing transfer): `balancing_transfer_cells`,
  `concentrating_transfer_cells`, `balancing_transfer_premium`.  Route: collapse
  wrong labels `i, j` into a wildcard (`collapseWord`/`decodeWord`), factor the
  IID word sum as collapsed-word weight × labelling weight `m(j)^#j m(i)^#i`
  (`wordSum_collapse`), average the success indicator over each count fiber of
  the labelling (`fiberAverage`: symmetric, nondecreasing toward the centre),
  and apply the existing L/M/H coupling `symmetric_word_mass_balancing`.
* A6.3 (HLP): `hlp_majorizes`, by induction on the number of disagreeing
  coordinates of the sorted vectors (`hlp_sorted`); zeros and ties allowed.
* A6.4: `concentration_cells`, `concentration_premium` (pick-up constants `κ`
  are FIXED PARAMETERS in `[0,1]³`, never conditional means of a kernel).
* A6.5: `size_interaction_counterexample` on actual IID laws via the count
  formula `plurality_multinomial_formula`, evaluated by `simp`/`norm_num`.
Standard axioms only.
-/
import SEKernel.PluralityConcentration
import SEKernel.EpistemicPayoff
import SEKernel.PluralityCountFormula

namespace SEKernel.Closeout.Concentration

open Finset Relation SEKernel.FiniteProbability SEKernel.Epistemic SEKernel.EpistemicConcentration

section BoolWords

variable {ι : Type*} [Fintype ι]

/-- Number of `true` bits of a labelling. -/
def trueCount (b : ι → Bool) : ℕ := (univ.filter fun t => b t = true).card

/-- Number of `false` bits of a labelling. -/
def falseCount (b : ι → Bool) : ℕ := (univ.filter fun t => b t = false).card

theorem trueCount_add_falseCount (b : ι → Bool) :
    trueCount b + falseCount b = Fintype.card ι := by
  unfold trueCount falseCount
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι))
    (fun t => b t = true)
  simpa using h

theorem trueCount_le (b : ι → Bool) : trueCount b ≤ Fintype.card ι := by
  have := trueCount_add_falseCount b; omega

@[simp] theorem trueCount_not (b : ι → Bool) : trueCount (fun t => !b t) = falseCount b := by
  simp [trueCount, falseCount]

@[simp] theorem falseCount_not (b : ι → Bool) : falseCount (fun t => !b t) = trueCount b := by
  simp [trueCount, falseCount]

theorem prod_bool_weight (b : ι → Bool) (x y : ℝ) :
    (∏ t, if b t then y else x) = y ^ trueCount b * x ^ falseCount b := by
  rw [Finset.prod_ite]
  simp [trueCount, falseCount, Finset.prod_const]

/-- Complementing every bit, as an explicit involutive bijection. -/
def notEquiv (ι : Type*) : (ι → Bool) ≃ (ι → Bool) where
  toFun b t := !b t
  invFun b t := !b t
  left_inv b := by funext t; simp
  right_inv b := by funext t; simp

theorem sum_not_eq [DecidableEq ι] (f : (ι → Bool) → ℝ) :
    (∑ b : ι → Bool, f (fun t => !b t)) = ∑ b, f b :=
  Fintype.sum_equiv (notEquiv ι) _ _ (fun _ => rfl)

theorem trueCount_comp_equiv {κ : Type*} [Fintype κ] (e : ι ≃ κ) (b : κ → Bool) :
    trueCount (fun t => b (e t)) = trueCount b := by
  unfold trueCount
  apply Finset.card_nbij' (fun t => e t) (fun u => e.symm u)
  · intro t ht; simpa using ht
  · intro u hu; simpa using hu
  · intro t _; simp
  · intro u _; simp

theorem falseCount_comp_equiv {κ : Type*} [Fintype κ] (e : ι ≃ κ) (b : κ → Bool) :
    falseCount (fun t => b (e t)) = falseCount b := by
  unfold falseCount
  apply Finset.card_nbij' (fun t => e t) (fun u => e.symm u)
  · intro t ht; simpa using ht
  · intro u hu; simpa using hu
  · intro t _; simp
  · intro u _; simp

end BoolWords

/-- Marginalizing independent L/M/H words to the Boolean word recording one
predicate of each symbol. -/
theorem fin3_marginal {s : ℕ} (w : Fin 3 → ℝ) (P : Fin 3 → Bool) (h : ℕ → ℝ) :
    (∑ z : Fin s → Fin 3, (∏ t, w (z t)) * h (trueCount (fun t => P (z t)))) =
    ∑ b : Fin s → Bool, (∏ t, ∑ x : Fin 3, if P x = b t then w x else 0) *
      h (trueCount b) := by
  symm
  calc (∑ b : Fin s → Bool, (∏ t, ∑ x : Fin 3, if P x = b t then w x else 0) *
        h (trueCount b))
      = ∑ b : Fin s → Bool, ∑ z : Fin s → Fin 3,
          (∏ t, if P (z t) = b t then w (z t) else 0) * h (trueCount b) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Fintype.prod_sum, Finset.sum_mul]
    _ = ∑ z : Fin s → Fin 3, ∑ b : Fin s → Bool,
          (∏ t, if P (z t) = b t then w (z t) else 0) * h (trueCount b) :=
        Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.sum_eq_single (fun t => P (z t))]
        · simp
        · intro b _ hb
          obtain ⟨t, ht⟩ : ∃ t, P (z t) ≠ b t := by
            by_contra hc
            push_neg at hc
            exact hb (funext fun t => (hc t).symm)
          rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht]), zero_mul]
        · simp

/-- The binomial form of the existing L/M/H balancing theorem. -/
theorem binomial_balance_fin {s : ℕ} (h : ℕ → ℝ) (hsym : ∀ a, a ≤ s → h a = h (s - a))
    (hmono : ∀ j, j < s / 2 → h j ≤ h (j + 1)) {θ η : ℝ} (hθ : 0 ≤ θ) (hθη : θ ≤ η)
    (hη : η ≤ 1/2) :
    (∑ b : Fin s → Bool, θ ^ trueCount b * (1 - θ) ^ falseCount b * h (trueCount b)) ≤
    ∑ b : Fin s → Bool, η ^ trueCount b * (1 - η) ^ falseCount b * h (trueCount b) := by
  have key := symmetric_word_mass_balancing θ η hθ hθη hη h hsym hmono
  have e0 : (∑ z : Fin s → Fin 3, wordMass θ η z * h (symbolCount z 0)) =
      ∑ b : Fin s → Bool, θ ^ trueCount b * (1 - θ) ^ falseCount b * h (trueCount b) := by
    have hc (z : Fin s → Fin 3) : symbolCount z 0 = trueCount (fun t => decide (z t = 0)) := by
      simp [symbolCount, trueCount]
    simp_rw [hc, wordMass]
    rw [fin3_marginal (threeWeight θ η) (fun x => decide (x = 0)) h]
    apply Finset.sum_congr rfl
    intro b _
    have hw (t : Fin s) : (∑ x : Fin 3, if decide (x = 0) = b t then threeWeight θ η x else 0) =
        if b t then θ else 1 - θ := by
      cases b t <;> simp [Fin.sum_univ_three, threeWeight]
    simp_rw [hw, prod_bool_weight]
  have e2 : (∑ z : Fin s → Fin 3, wordMass θ η z * h (symbolCount z 2)) =
      ∑ b : Fin s → Bool, η ^ trueCount b * (1 - η) ^ falseCount b * h (trueCount b) := by
    have hc (z : Fin s → Fin 3) : symbolCount z 2 = trueCount (fun t => decide (z t = 2)) := by
      simp [symbolCount, trueCount]
    simp_rw [hc, wordMass]
    rw [fin3_marginal (threeWeight θ η) (fun x => decide (x = 2)) h]
    have hw (b : Fin s → Bool) (t : Fin s) :
        (∑ x : Fin 3, if decide (x = 2) = b t then threeWeight θ η x else 0) =
        if b t then 1 - η else η := by
      cases b t <;> simp [Fin.sum_univ_three, threeWeight]
    simp_rw [hw, prod_bool_weight]
    rw [← sum_not_eq]
    apply Finset.sum_congr rfl
    intro b _
    have hs := trueCount_add_falseCount b
    simp only [trueCount_not, falseCount_not, Fintype.card_fin] at hs ⊢
    rw [hsym (falseCount b) (by omega), show s - falseCount b = trueCount b by omega]
    ring
  rw [e0, e2] at key
  exact key

/-- Two-weight binomial balancing: for weight pairs with the same sum, the more
balanced pair gives the larger value of a symmetric, centre-nondecreasing `h`. -/
theorem binomial_pair_balance {s : ℕ} (h : ℕ → ℝ) (hsym : ∀ a, a ≤ s → h a = h (s - a))
    (hmono : ∀ j, j < s / 2 → h j ≤ h (j + 1)) {x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hx' : 0 ≤ x') (hy' : 0 ≤ y') (hsum : x' + y' = x + y) (hbal : |x' - y'| ≤ |x - y|) :
    (∑ b : Fin s → Bool, y ^ trueCount b * x ^ (s - trueCount b) * h (trueCount b)) ≤
    ∑ b : Fin s → Bool, y' ^ trueCount b * x' ^ (s - trueCount b) * h (trueCount b) := by
  let Q : ℝ → ℝ → ℝ := fun p q => ∑ b : Fin s → Bool,
    q ^ trueCount b * p ^ (s - trueCount b) * h (trueCount b)
  let B : ℝ → ℝ := fun θ => ∑ b : Fin s → Bool,
    θ ^ trueCount b * (1 - θ) ^ falseCount b * h (trueCount b)
  have hfc (b : Fin s → Bool) : falseCount b = s - trueCount b := by
    have := trueCount_add_falseCount b
    simp only [Fintype.card_fin] at this
    omega
  have hswap (p q : ℝ) : Q p q = Q q p := by
    simp only [Q]
    rw [← sum_not_eq]
    apply Finset.sum_congr rfl
    intro b _
    have hle := trueCount_le b
    simp only [Fintype.card_fin] at hle
    rw [trueCount_not, hfc, Nat.sub_sub_self hle, ← hsym _ hle]
    ring
  have hscale (p q : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) (hσ : 0 < p + q) :
      Q p q = (p + q) ^ s * B (q / (p + q)) := by
    simp only [Q, B]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hle := trueCount_le b
    simp only [Fintype.card_fin] at hle
    rw [hfc]
    have h1 : 1 - q / (p + q) = p / (p + q) := by field_simp; ring
    rw [h1, div_pow, div_pow]
    have hp : (p + q) ^ s = (p + q) ^ (trueCount b) * (p + q) ^ (s - trueCount b) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [hp]
    have h2 : (p + q) ^ (trueCount b) ≠ 0 := pow_ne_zero _ hσ.ne'
    have h3 : (p + q) ^ (s - trueCount b) ≠ 0 := pow_ne_zero _ hσ.ne'
    field_simp
  have e1 : 2 * min x y = x + y - |x - y| := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have e2 : 2 * min x' y' = x' + y' - |x' - y'| := by
    rcases le_total x' y' with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have hmin1 : min x y ≤ min x' y' := by linarith
  have hmin2 : 2 * min x' y' ≤ x + y := by linarith [abs_nonneg (x' - y')]
  by_cases hσ : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    have hx0' : x' = 0 := by linarith
    have hy0' : y' = 0 := by linarith
    subst hx0 hy0 hx0' hy0'
    exact le_rfl
  · have hσpos : 0 < x + y := lt_of_le_of_ne (by linarith) (Ne.symm hσ)
    have hQ : ∀ p q, 0 ≤ p → 0 ≤ q → p + q = x + y →
        Q p q = (x + y) ^ s * B (min p q / (x + y)) := by
      intro p q hp hq hpq
      rcases le_total q p with h | h
      · rw [min_eq_right h, hscale p q hq h (by linarith), hpq]
      · rw [hswap, min_eq_left h, hscale q p hp h (by linarith), add_comm q p, hpq]
    show Q x y ≤ Q x' y'
    rw [hQ x y hx hy rfl, hQ x' y' hx' hy' hsum]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hσpos.le s)
    apply binomial_balance_fin h hsym hmono
    · exact div_nonneg (le_min hx hy) hσpos.le
    · exact div_le_div_of_nonneg_right hmin1 hσpos.le
    · rw [div_le_iff₀ hσpos]; linarith

section Averaging

variable {s : ℕ}

/-- Labellings with exactly `n` true bits. -/
def countFiber (s n : ℕ) : Finset (Fin s → Bool) := univ.filter fun b => trueCount b = n

/-- Average of `F` over one count fiber; an empty fiber has the explicit value zero. -/
noncomputable def fiberAverage (F : (Fin s → Bool) → ℝ) (n : ℕ) : ℝ :=
  (∑ b ∈ countFiber s n, F b) / (countFiber s n).card

theorem sum_count_weight_average (F : (Fin s → Bool) → ℝ) (W : ℕ → ℝ) :
    (∑ b : Fin s → Bool, W (trueCount b) * F b) =
      ∑ b : Fin s → Bool, W (trueCount b) * fiberAverage F (trueCount b) := by
  have hmaps : ∀ b ∈ (univ : Finset (Fin s → Bool)), trueCount b ∈ range (s + 1) := by
    intro b _
    have := trueCount_le b
    simp only [Fintype.card_fin] at this
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro n _
  have hL : (∑ b ∈ univ.filter (fun b : Fin s → Bool => trueCount b = n),
      W (trueCount b) * F b) = W n * ∑ b ∈ countFiber s n, F b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [(Finset.mem_filter.mp hb).2]
  have hR : (∑ b ∈ univ.filter (fun b : Fin s → Bool => trueCount b = n),
      W (trueCount b) * fiberAverage F (trueCount b)) =
      (countFiber s n).card * (W n * fiberAverage F n) := by
    rw [Finset.sum_congr rfl (g := fun _ => W n * fiberAverage F n)
      (fun b hb => by rw [(Finset.mem_filter.mp hb).2])]
    simp [countFiber]
  rw [hL, hR]
  unfold fiberAverage
  by_cases hc : (countFiber s n).card = 0
  · have he : countFiber s n = ∅ := Finset.card_eq_zero.mp hc
    simp [he]
  · have hc' : ((countFiber s n).card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

theorem fiber_sum_not (f : (Fin s → Bool) → ℝ) (hf : ∀ b, f (fun t => !b t) = f b)
    (n : ℕ) (hn : n ≤ s) :
    (∑ b ∈ countFiber s n, f b) = ∑ b ∈ countFiber s (s - n), f b := by
  have hfc (b : Fin s → Bool) : falseCount b = s - trueCount b := by
    have := trueCount_add_falseCount b
    simp only [Fintype.card_fin] at this
    omega
  apply Finset.sum_nbij' (fun b t => !b t) (fun b t => !b t)
  · intro b hb
    simp only [countFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [trueCount_not, hfc, hb]
  · intro b hb
    simp only [countFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    have hle := trueCount_le b
    simp only [Fintype.card_fin] at hle
    rw [trueCount_not, hfc, hb]
    omega
  · intro b _; funext t; simp
  · intro b _; funext t; simp
  · intro b _; exact (hf b).symm

theorem fiberAverage_symm (F : (Fin s → Bool) → ℝ) (hF : ∀ b, F (fun t => !b t) = F b)
    (n : ℕ) (hn : n ≤ s) : fiberAverage F n = fiberAverage F (s - n) := by
  unfold fiberAverage
  have h1 := fiber_sum_not F hF n hn
  have h2 := fiber_sum_not (fun _ => (1:ℝ)) (fun _ => rfl) n hn
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  rw [h1, h2]

theorem countFiber_nonempty (n : ℕ) (hn : n ≤ s) :
    ∃ b, b ∈ countFiber s n := by
  refine ⟨fun t => decide (t.val < n), ?_⟩
  simp only [countFiber, Finset.mem_filter, Finset.mem_univ, true_and, trueCount,
    decide_eq_true_eq]
  exact prefixPositions_card hn

theorem fiberAverage_mono (F : (Fin s → Bool) → ℝ) (m : ℕ) (hnn : ∀ b, 0 ≤ F b)
    (hzero : ∀ b, m < trueCount b ∨ m < falseCount b → F b = 0)
    (hmax : ∀ b, trueCount b < m → falseCount b < m → ∀ b', F b' ≤ F b)
    (n : ℕ) (hn : n < s / 2) : fiberAverage F n ≤ fiberAverage F (n + 1) := by
  have h2 : 2 * (n + 1) ≤ s := by omega
  have hfc (b : Fin s → Bool) : falseCount b = s - trueCount b := by
    have := trueCount_add_falseCount b
    simp only [Fintype.card_fin] at this
    omega
  have hge : 0 ≤ fiberAverage F (n + 1) :=
    div_nonneg (Finset.sum_nonneg fun b _ => hnn b) (Nat.cast_nonneg _)
  by_cases hc : m < s - n
  · have hz : (∑ b ∈ countFiber s n, F b) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hb' : trueCount b = n := (Finset.mem_filter.mp hb).2
      exact hzero b (Or.inr (by rw [hfc, hb']; exact hc))
    have h0 : fiberAverage F n = 0 := by unfold fiberAverage; rw [hz, zero_div]
    rw [h0]; exact hge
  · push_neg at hc
    obtain ⟨b0, hb0⟩ := countFiber_nonempty (s := s) (n + 1) (by omega)
    have hb0' : trueCount b0 = n + 1 := (Finset.mem_filter.mp hb0).2
    have hcen : ∀ b ∈ countFiber s (n + 1), trueCount b < m ∧ falseCount b < m := by
      intro b hb
      have hb' : trueCount b = n + 1 := (Finset.mem_filter.mp hb).2
      rw [hfc, hb']
      omega
    have hb0max := hmax b0 (hcen b0 hb0).1 (hcen b0 hb0).2
    have hle1 : fiberAverage F n ≤ F b0 := by
      unfold fiberAverage
      by_cases hz : (countFiber s n).card = 0
      · rw [hz, Nat.cast_zero, div_zero]; exact hnn b0
      · have hpos : (0:ℝ) < (countFiber s n).card := by
          exact_mod_cast Nat.pos_of_ne_zero hz
        rw [div_le_iff₀ hpos]
        calc (∑ b ∈ countFiber s n, F b) ≤ ∑ _b ∈ countFiber s n, F b0 :=
              Finset.sum_le_sum fun b _ => hb0max b
          _ = F b0 * (countFiber s n).card := by simp [mul_comm]
    have hle2 : F b0 ≤ fiberAverage F (n + 1) := by
      unfold fiberAverage
      have hpos : (0:ℝ) < (countFiber s (n + 1)).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨b0, hb0⟩
      rw [le_div_iff₀ hpos]
      calc F b0 * (countFiber s (n + 1)).card = ∑ _b ∈ countFiber s (n + 1), F b0 := by
            simp [mul_comm]
        _ ≤ ∑ b ∈ countFiber s (n + 1), F b :=
            Finset.sum_le_sum fun b hb => hmax b (hcen b hb).1 (hcen b hb).2 b0
    linarith

/-- One-pair balancing for any symmetric labelling functional whose central
labellings are maximal and whose labellings with an over-full side vanish. -/
theorem bool_balancing_fin (F : (Fin s → Bool) → ℝ) (m : ℕ)
    (hsym : ∀ b, F (fun t => !b t) = F b) (hnn : ∀ b, 0 ≤ F b)
    (hzero : ∀ b, m < trueCount b ∨ m < falseCount b → F b = 0)
    (hmax : ∀ b, trueCount b < m → falseCount b < m → ∀ b', F b' ≤ F b)
    {x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y')
    (hsum : x' + y' = x + y) (hbal : |x' - y'| ≤ |x - y|) :
    (∑ b, (∏ t, if b t then y else x) * F b) ≤
      ∑ b, (∏ t, if b t then y' else x') * F b := by
  have hgs : ∀ a, a ≤ s → fiberAverage F a = fiberAverage F (s - a) :=
    fun a ha => fiberAverage_symm F hsym a ha
  have hgm := fiberAverage_mono F m hnn hzero hmax
  have hfc (b : Fin s → Bool) : falseCount b = s - trueCount b := by
    have := trueCount_add_falseCount b
    simp only [Fintype.card_fin] at this
    omega
  have hW (p q : ℝ) : (∑ b : Fin s → Bool, (∏ t, if b t then q else p) * F b) =
      ∑ b : Fin s → Bool, q ^ trueCount b * p ^ (s - trueCount b) *
        fiberAverage F (trueCount b) := by
    simp_rw [prod_bool_weight, hfc]
    exact sum_count_weight_average F (fun n => q ^ n * p ^ (s - n))
  rw [hW x y, hW x' y']
  exact binomial_pair_balance (fiberAverage F) hgs hgm hx hy hx' hy' hsum hbal

end Averaging

/-- The same one-pair balancing on labellings of an arbitrary finite position set. -/
theorem bool_balancing {ι : Type*} [Fintype ι] [DecidableEq ι] (F : (ι → Bool) → ℝ) (m : ℕ)
    (hsym : ∀ b, F (fun t => !b t) = F b) (hnn : ∀ b, 0 ≤ F b)
    (hzero : ∀ b, m < trueCount b ∨ m < falseCount b → F b = 0)
    (hmax : ∀ b, trueCount b < m → falseCount b < m → ∀ b', F b' ≤ F b)
    {x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y')
    (hsum : x' + y' = x + y) (hbal : |x' - y'| ≤ |x - y|) :
    (∑ b : ι → Bool, (∏ t, if b t then y else x) * F b) ≤
      ∑ b : ι → Bool, (∏ t, if b t then y' else x') * F b := by
  let e := Fintype.equivFin ι
  let G : (Fin (Fintype.card ι) → Bool) → ℝ := fun b => F (fun t => b (e t))
  have htr (p q : ℝ) : (∑ b : ι → Bool, (∏ t, if b t then q else p) * F b) =
      ∑ b : Fin (Fintype.card ι) → Bool, (∏ t, if b t then q else p) * G b := by
    apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
    intro b
    have h1 : (∏ u, if b (e.symm u) then q else p) = ∏ t, if b t then q else p :=
      Equiv.prod_comp e.symm (fun t => if b t then q else p)
    simp only [G, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq, h1,
      Equiv.symm_apply_apply]
  rw [htr x y, htr x' y']
  apply bool_balancing_fin G m _ _ _ _ hx hy hx' hy' hsum hbal
  · intro b; exact hsym _
  · intro b; exact hnn _
  · intro b hb
    apply hzero
    rwa [trueCount_comp_equiv, falseCount_comp_equiv]
  · intro b h1 h2 b'
    apply hmax
    · rwa [trueCount_comp_equiv]
    · rwa [falseCount_comp_equiv]

/-! ### Ordered plurality under weakened opponents -/

theorem mem_candidatePositions {N : ℕ} {A : Type*} (z : OrderedWord N A) (t : Fin N) :
    t ∈ candidatePositions z ↔
      z t ≠ none ∧ ∀ u, z u ≠ none → labelCount z (z u) ≤ labelCount z (z t) := by
  unfold candidatePositions
  simp

/-- If `a` wins `z'`, keeps exactly the same positions in `z`, and every other
readable label of `z` is either strictly short of `a`'s count or carried over
verbatim (same position, same count) from `z'`, then `a` also wins `z`. -/
theorem plurality_of_dominated {N : ℕ} {A : Type*} (z z' : OrderedWord N A) (a : A)
    (h' : plurality z' = some a)
    (hpos : ∀ t, z t = some a ↔ z' t = some a)
    (hother : ∀ t, z t ≠ none → z t ≠ some a →
      labelCount z (z t) < labelCount z (some a) ∨
        (z' t = z t ∧ labelCount z' (z t) = labelCount z (z t))) :
    plurality z = some a := by
  classical
  have hcount : labelCount z (some a) = labelCount z' (some a) := by
    unfold labelCount
    congr 1
    ext t
    simp [hpos t]
  obtain ⟨u0, hu0⟩ := plurality_mem_word z' a h'
  have hu0z : z u0 = some a := (hpos u0).2 hu0
  have hz'max : ∀ u, z' u ≠ none → labelCount z' (z' u) ≤ labelCount z' (some a) :=
    fun u hu => plurality_maximal_count z' a h' u hu
  have hA : ∀ u, z u ≠ none → labelCount z (z u) ≤ labelCount z (some a) := by
    intro u hu
    by_cases hua : z u = some a
    · rw [hua]
    · rcases hother u hu hua with hlt | ⟨heq, hc⟩
      · exact hlt.le
      · rw [← hc, hcount, ← heq]
        exact hz'max u (by rw [heq]; exact hu)
  have hsub : ∀ t ∈ candidatePositions z, t ∈ candidatePositions z' := by
    intro t ht
    rw [mem_candidatePositions] at ht ⊢
    obtain ⟨htn, htmax⟩ := ht
    have hge : labelCount z (some a) ≤ labelCount z (z t) := by
      have := htmax u0 (by rw [hu0z]; simp)
      rwa [hu0z] at this
    by_cases hta : z t = some a
    · refine ⟨by rw [(hpos t).1 hta]; simp, ?_⟩
      intro u hu
      rw [(hpos t).1 hta]
      exact hz'max u hu
    · rcases hother t htn hta with hlt | ⟨heq, hc⟩
      · omega
      · refine ⟨by rw [heq]; exact htn, ?_⟩
        intro u hu
        rw [heq, hc]
        calc labelCount z' (z' u) ≤ labelCount z' (some a) := hz'max u hu
          _ = labelCount z (some a) := hcount.symm
          _ ≤ labelCount z (z t) := hge
  unfold plurality at h' ⊢
  split_ifs at h' with hc'
  have ht0z : z ((candidatePositions z').min' hc') = some a :=
    (hpos _).2 h'
  have ht0cand : (candidatePositions z').min' hc' ∈ candidatePositions z := by
    rw [mem_candidatePositions]
    refine ⟨by rw [ht0z]; simp, ?_⟩
    intro u hu
    rw [ht0z]
    exact hA u hu
  have hne : (candidatePositions z).Nonempty := ⟨_, ht0cand⟩
  rw [dif_pos hne]
  have hmin : (candidatePositions z).min' hne = (candidatePositions z').min' hc' := by
    apply le_antisymm
    · exact Finset.min'_le _ _ ht0cand
    · exact Finset.min'_le _ _ (hsub _ (Finset.min'_mem _ _))
  rw [hmin]
  exact ht0z

/-! ### Collapsed words: wildcard factorization of the IID word law -/

section Collapse

variable {A : Type*} [Fintype A] [DecidableEq A] {N : ℕ}

/-- Collapse wrong label `j` onto wrong label `i`; every other symbol is retained. -/
def collapseLabel (i j : A) (x : Option A) : Option A := if x = some j then some i else x

/-- The collapsed word records every position verbatim except that `j` is read as `i`. -/
def collapseWord (i j : A) (z : OrderedWord N A) : OrderedWord N A :=
  fun t => collapseLabel i j (z t)

/-- The wildcard positions of a collapsed word. -/
abbrev WildPos (i : A) (c : OrderedWord N A) := {t : Fin N // c t = some i}

/-- Relabel the wildcard positions of `c` by a Boolean labelling (`true` = `j`). -/
def decodeWord (i j : A) (c : OrderedWord N A) (l : WildPos i c → Bool) : OrderedWord N A :=
  fun t => if h : c t = some i then (if l ⟨t, h⟩ then some j else some i) else c t

theorem decodeWord_wild (i j : A) (c : OrderedWord N A) (l : WildPos i c → Bool)
    (u : WildPos i c) : decodeWord i j c l u.1 = if l u then some j else some i := by
  unfold decodeWord
  rw [dif_pos u.2]

theorem decodeWord_wild' (i j : A) (c : OrderedWord N A) (l : WildPos i c → Bool)
    (t : Fin N) (h : c t = some i) :
    decodeWord i j c l t = if l ⟨t, h⟩ then some j else some i := by
  unfold decodeWord
  rw [dif_pos h]

theorem decodeWord_nonwild (i j : A) (c : OrderedWord N A) (l : WildPos i c → Bool)
    (t : Fin N) (h : ¬ c t = some i) : decodeWord i j c l t = c t := by
  unfold decodeWord
  rw [dif_neg h]

theorem decodeWord_eq_iff (i j : A) (c : OrderedWord N A) (l : WildPos i c → Bool)
    (x : Option A) (hxi : x ≠ some i) (hxj : x ≠ some j) (t : Fin N) :
    decodeWord i j c l t = x ↔ c t = x := by
  by_cases h : c t = some i
  · rw [decodeWord_wild i j c l ⟨t, h⟩, h]
    constructor
    · intro hx
      exfalso
      split_ifs at hx
      · exact hxj hx.symm
      · exact hxi hx.symm
    · intro hx
      exact absurd hx.symm hxi
  · rw [decodeWord_nonwild i j c l t h]

theorem labelCount_decode (i j : A) (c : OrderedWord N A) (l : WildPos i c → Bool)
    (x : Option A) (hxi : x ≠ some i) (hxj : x ≠ some j) :
    labelCount (decodeWord i j c l) x = labelCount c x := by
  unfold labelCount
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact decodeWord_eq_iff i j c l x hxi hxj t

theorem labelCount_decode_j (i j : A) (hij : i ≠ j) (c : OrderedWord N A)
    (hc : ∀ t, c t ≠ some j) (l : WildPos i c → Bool) :
    labelCount (decodeWord i j c l) (some j) = trueCount l := by
  unfold labelCount trueCount
  symm
  apply Finset.card_bij (fun u _ => u.1)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [decodeWord_wild, hu]
    rfl
  · intro u _ v _ h
    exact Subtype.ext h
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    by_cases h : c t = some i
    · refine ⟨⟨t, h⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [decodeWord_wild i j c l ⟨t, h⟩] at ht
      by_contra hl
      simp only [hl] at ht
      simp at ht
      exact hij ht
    · rw [decodeWord_nonwild i j c l t h] at ht
      exact absurd ht (hc t)

theorem labelCount_decode_i (i j : A) (hij : i ≠ j) (c : OrderedWord N A)
    (l : WildPos i c → Bool) :
    labelCount (decodeWord i j c l) (some i) = falseCount l := by
  unfold labelCount falseCount
  symm
  apply Finset.card_bij (fun u _ => u.1)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [decodeWord_wild, hu]
    rfl
  · intro u _ v _ h
    exact Subtype.ext h
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    by_cases h : c t = some i
    · refine ⟨⟨t, h⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [decodeWord_wild i j c l ⟨t, h⟩] at ht
      by_contra hl
      simp only [Bool.not_eq_false] at hl
      simp only [hl] at ht
      simp at ht
      exact hij ht.symm
    · rw [decodeWord_nonwild i j c l t h] at ht
      exact absurd ht h

/-- Complementing the labelling is the wrong-label transposition `i ↔ j`. -/
theorem decodeWord_not (i j : A) (c : OrderedWord N A) (hc : ∀ t, c t ≠ some j)
    (l : WildPos i c → Bool) :
    decodeWord i j c (fun u => !l u) =
      fun t => Equiv.swap (some i) (some j) (decodeWord i j c l t) := by
  funext t
  by_cases h : c t = some i
  · rw [decodeWord_wild i j c _ ⟨t, h⟩, decodeWord_wild i j c l ⟨t, h⟩]
    cases l ⟨t, h⟩ <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rw [decodeWord_nonwild i j c _ t h, decodeWord_nonwild i j c l t h]
    exact (Equiv.swap_apply_of_ne_of_ne h (hc t)).symm

/-- The fiber of the collapse map over a `j`-free collapsed word is in explicit
bijection with the Boolean labellings of its wildcard positions. -/
theorem sum_collapse_fiber (i j : A) (hij : i ≠ j) (c : OrderedWord N A)
    (hc : ∀ t, c t ≠ some j) (f : OrderedWord N A → ℝ) :
    (∑ z ∈ univ.filter (fun z => collapseWord i j z = c), f z) =
      ∑ l : WildPos i c → Bool, f (decodeWord i j c l) := by
  symm
  apply Finset.sum_nbij' (fun l => decodeWord i j c l) (fun z u => decide (z u.1 = some j))
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    funext t
    simp only [collapseWord, collapseLabel]
    by_cases h : c t = some i
    · rw [decodeWord_wild i j c l ⟨t, h⟩, h]
      cases l ⟨t, h⟩ <;> simp [hij]
    · rw [decodeWord_nonwild i j c l t h]
      simp [hc t]
  · intro z _
    simp
  · intro l _
    funext u
    rw [decodeWord_wild]
    cases l u <;> simp [hij]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    funext t
    have hzt : collapseLabel i j (z t) = c t := congrFun hz t
    unfold collapseLabel at hzt
    by_cases h : c t = some i
    · rw [decodeWord_wild i j c _ ⟨t, h⟩]
      by_cases hj : z t = some j
      · simp [hj]
      · rw [if_neg hj] at hzt
        simp [hzt, h]
        exact fun e => e.symm
    · rw [decodeWord_nonwild i j c _ t h]
      by_cases hj : z t = some j
      · rw [if_pos hj] at hzt
        exact absurd hzt.symm h
      · rw [if_neg hj] at hzt
        exact hzt.symm
  · intro l _
    rfl

theorem prod_decode (i j : A) (m : Option A → ℝ) (c : OrderedWord N A)
    (l : WildPos i c → Bool) :
    (∏ t, m (decodeWord i j c l t)) =
      (∏ u : WildPos i c, if l u then m (some j) else m (some i)) *
        ∏ t : {t : Fin N // ¬ c t = some i}, m (c t) := by
  have hfun : (fun t => m (decodeWord i j c l t)) = fun t =>
      if h : c t = some i then (if l ⟨t, h⟩ then m (some j) else m (some i)) else m (c t) := by
    funext t
    by_cases h : c t = some i
    · rw [dif_pos h, decodeWord_wild i j c l ⟨t, h⟩]
      split_ifs <;> rfl
    · rw [dif_neg h, decodeWord_nonwild i j c l t h]
  rw [hfun, Fintype.prod_dite]

/-- Unnormalized product-word functional of a (nonnegative) mass function. -/
noncomputable def wordSum (m : Option A → ℝ) (F : OrderedWord N A → ℝ) : ℝ :=
  ∑ z : OrderedWord N A, (∏ t, m (z t)) * F z

/-- Collapsed-word factorization: collapsed-word weight times the labelling
weight `m(j)^#j m(i)^#i` of the wildcard positions. -/
theorem wordSum_collapse (i j : A) (hij : i ≠ j) (m : Option A → ℝ)
    (F : OrderedWord N A → ℝ) :
    wordSum m F = ∑ c : OrderedWord N A, if ∀ t, c t ≠ some j then
      (∏ t : {t : Fin N // ¬ c t = some i}, m (c t)) *
        ∑ l : WildPos i c → Bool,
          (∏ u, if l u then m (some j) else m (some i)) * F (decodeWord i j c l)
      else 0 := by
  unfold wordSum
  rw [← Finset.sum_fiberwise univ (collapseWord i j)]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hc
  · rw [sum_collapse_fiber i j hij c hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [prod_decode]
    ring
  · push_neg at hc
    obtain ⟨t, ht⟩ := hc
    apply Finset.sum_eq_zero
    intro z hz
    exfalso
    have hzt := congrFun (Finset.mem_filter.mp hz).2 t
    simp only [collapseWord, collapseLabel] at hzt
    split_ifs at hzt with h
    · rw [ht] at hzt
      exact hij (Option.some.inj hzt)
    · rw [ht] at hzt
      exact h hzt

/-- Abstract one-transfer comparison: any functional satisfying the four
labelling conditions on every collapsed word weakly increases. -/
theorem wordSum_balancing (i j : A) (hij : i ≠ j) (m m' : Option A → ℝ)
    (hm : ∀ x, 0 ≤ m x) (hm' : ∀ x, 0 ≤ m' x)
    (hoff : ∀ x, x ≠ some i → x ≠ some j → m' x = m x)
    (hsum : m' (some i) + m' (some j) = m (some i) + m (some j))
    (hbal : |m' (some i) - m' (some j)| ≤ |m (some i) - m (some j)|)
    (F : OrderedWord N A → ℝ)
    (hF : ∀ c : OrderedWord N A, (∀ t, c t ≠ some j) → ∃ k : ℕ,
      (∀ l, F (decodeWord i j c (fun u => !l u)) = F (decodeWord i j c l)) ∧
      (∀ l, 0 ≤ F (decodeWord i j c l)) ∧
      (∀ l, k < trueCount l ∨ k < falseCount l → F (decodeWord i j c l) = 0) ∧
      (∀ l, trueCount l < k → falseCount l < k → ∀ l',
        F (decodeWord i j c l') ≤ F (decodeWord i j c l))) :
    wordSum m F ≤ wordSum m' F := by
  rw [wordSum_collapse i j hij m F, wordSum_collapse i j hij m' F]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with hc
  · have hP : (∏ t : {t : Fin N // ¬ c t = some i}, m' (c t)) =
        ∏ t : {t : Fin N // ¬ c t = some i}, m (c t) := by
      apply Finset.prod_congr rfl
      intro t _
      exact hoff _ t.2 (hc t)
    rw [hP]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun t _ => hm _)
    obtain ⟨k, h1, h2, h3, h4⟩ := hF c hc
    exact bool_balancing (fun l => F (decodeWord i j c l)) k h1 h2 h3 h4
      (hm _) (hm _) (hm' _) (hm' _) hsum hbal
  · exact le_rfl

end Collapse

/-! ### The one-transfer theorem for the actual ordered plurality cells -/

section Transfer

variable {A : Type*} [Fintype A] [DecidableEq A] {N : ℕ}

/-- Indicator that `a` is the ordered plurality winner and `E` holds. -/
noncomputable def winIndicator (a : A) (E : OrderedWord N A → Prop) (z : OrderedWord N A) : ℝ := by
  classical
  exact if plurality z = some a ∧ E z then 1 else 0

theorem winIndicator_of {a : A} {E : OrderedWord N A → Prop} {z : OrderedWord N A}
    (h : plurality z = some a ∧ E z) : winIndicator a E z = 1 := by
  unfold winIndicator
  rw [if_pos h]

theorem winIndicator_of_not {a : A} {E : OrderedWord N A → Prop} {z : OrderedWord N A}
    (h : ¬ (plurality z = some a ∧ E z)) : winIndicator a E z = 0 := by
  unfold winIndicator
  rw [if_neg h]

theorem winIndicator_nonneg {a : A} {E : OrderedWord N A → Prop} {z : OrderedWord N A} :
    0 ≤ winIndicator a E z := by
  by_cases h : plurality z = some a ∧ E z
  · rw [winIndicator_of h]; norm_num
  · rw [winIndicator_of_not h]

theorem winIndicator_congr {a : A} {E : OrderedWord N A → Prop} {z z' : OrderedWord N A}
    (h : (plurality z = some a ∧ E z) ↔ (plurality z' = some a ∧ E z')) :
    winIndicator a E z = winIndicator a E z' := by
  by_cases hz : plurality z = some a ∧ E z
  · rw [winIndicator_of hz, winIndicator_of (h.mp hz)]
  · rw [winIndicator_of_not hz, winIndicator_of_not (fun h' => hz (h.mpr h'))]

/-- An event that reads only the positions of the correct answer `a`
(for instance prefix reach of `a`, its negation, or `True`). -/
def ReadsOnly (a : A) (E : OrderedWord N A → Prop) : Prop :=
  ∀ z z' : OrderedWord N A, (∀ t, z t = some a ↔ z' t = some a) → (E z ↔ E z')

theorem readsOnly_true (a : A) : ReadsOnly (N := N) a (fun _ => True) :=
  fun _ _ _ => Iff.rfl

theorem readsOnly_reaches (a : A) (k : ℕ) : ReadsOnly (N := N) a (fun z => reaches z k a) := by
  intro z z' h
  unfold reaches
  constructor
  · rintro ⟨t, ht, hz⟩; exact ⟨t, ht, (h t).1 hz⟩
  · rintro ⟨t, ht, hz⟩; exact ⟨t, ht, (h t).2 hz⟩

theorem readsOnly_not_reaches (a : A) (k : ℕ) :
    ReadsOnly (N := N) a (fun z => ¬ reaches z k a) := by
  intro z z' h
  exact not_congr (readsOnly_reaches a k z z' h)

/-- The four labelling conditions of `bool_balancing`, verified for the
ordered first-appearance plurality on every `j`-free collapsed word, with
threshold the collapsed word's correct count. -/
theorem decode_win_conditions (i j a : A) (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j)
    (E : OrderedWord N A → Prop) (hE : ReadsOnly a E) (c : OrderedWord N A)
    (hc : ∀ t, c t ≠ some j) :
    (∀ l, winIndicator a E (decodeWord i j c (fun u => !l u)) =
      winIndicator a E (decodeWord i j c l)) ∧
    (∀ l, 0 ≤ winIndicator a E (decodeWord i j c l)) ∧
    (∀ l, labelCount c (some a) < trueCount l ∨ labelCount c (some a) < falseCount l →
      winIndicator a E (decodeWord i j c l) = 0) ∧
    (∀ l, trueCount l < labelCount c (some a) → falseCount l < labelCount c (some a) →
      ∀ l', winIndicator a E (decodeWord i j c l') ≤ winIndicator a E (decodeWord i j c l)) := by
  have hai' : some a ≠ some i := by simpa using hai
  have haj' : some a ≠ some j := by simpa using haj
  have hapos : ∀ l t, decodeWord i j c l t = some a ↔ c t = some a :=
    fun l t => decodeWord_eq_iff i j c l (some a) hai' haj' t
  have hacount : ∀ l, labelCount (decodeWord i j c l) (some a) = labelCount c (some a) :=
    fun l => labelCount_decode i j c l (some a) hai' haj'
  refine ⟨?_, fun l => winIndicator_nonneg, ?_, ?_⟩
  · intro l
    apply winIndicator_congr
    rw [decodeWord_not i j c hc l]
    set z := decodeWord i j c l
    set σ := Equiv.swap (some i) (some j)
    have hσn : σ none = none := Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
    have hσa : σ (some a) = some a := Equiv.swap_apply_of_ne_of_ne hai' haj'
    have hsa : ∀ x, σ x = some a ↔ x = some a := by
      intro x
      constructor
      · intro h
        apply σ.injective
        rw [h, hσa]
      · intro h
        rw [h, hσa]
    rw [plurality_relabel z σ hσn]
    have hEz := hE (fun t => σ (z t)) z (fun t => hsa (z t))
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hsa _).1 h1, hEz.1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hsa _).2 h1, hEz.2 h2⟩
  · intro l hl
    apply winIndicator_of_not
    rintro ⟨hp, _⟩
    have hj := plurality_dominates_readable _ a hp j
    have hi := plurality_dominates_readable _ a hp i
    rw [labelCount_decode_j i j hij c hc l, hacount] at hj
    rw [labelCount_decode_i i j hij c l, hacount] at hi
    omega
  · intro l h1 h2 l'
    by_cases hw : plurality (decodeWord i j c l') = some a ∧ E (decodeWord i j c l')
    · rw [winIndicator_of hw]
      apply le_of_eq
      symm
      apply winIndicator_of
      have hposw : ∀ t, decodeWord i j c l t = some a ↔ decodeWord i j c l' t = some a := by
        intro t
        rw [hapos, hapos]
      refine ⟨?_, (hE _ _ hposw).2 hw.2⟩
      apply plurality_of_dominated (decodeWord i j c l) (decodeWord i j c l') a hw.1 hposw
      intro t _ _
      by_cases h : c t = some i
      · left
        rw [decodeWord_wild' i j c l t h]
        cases hl : l ⟨t, h⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [labelCount_decode_i i j hij c l, hacount]
          exact h2
        · simp only [↓reduceIte]
          rw [labelCount_decode_j i j hij c hc l, hacount]
          exact h1
      · right
        rw [decodeWord_nonwild i j c l t h, decodeWord_nonwild i j c l' t h]
        refine ⟨rfl, ?_⟩
        rw [labelCount_decode i j c l' (c t) h (hc t), labelCount_decode i j c l (c t) h (hc t)]
    · rw [winIndicator_of_not hw]
      exact winIndicator_nonneg

/-- One balancing transfer at the level of nonnegative (unnormalized) masses. -/
theorem wordSum_win_balancing (i j a : A) (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j)
    (m m' : Option A → ℝ) (hm : ∀ x, 0 ≤ m x) (hm' : ∀ x, 0 ≤ m' x)
    (hoff : ∀ x, x ≠ some i → x ≠ some j → m' x = m x)
    (hsum : m' (some i) + m' (some j) = m (some i) + m (some j))
    (hbal : |m' (some i) - m' (some j)| ≤ |m (some i) - m (some j)|)
    (E : OrderedWord N A → Prop) (hE : ReadsOnly a E) :
    wordSum m (winIndicator a E) ≤ wordSum m' (winIndicator a E) :=
  wordSum_balancing i j hij m m' hm hm' hoff hsum hbal _
    (fun c hc => ⟨labelCount c (some a), decode_win_conditions i j a hij hai haj E hE c hc⟩)

theorem prob_win_eq_wordSum (π : Law (Option A)) (N : ℕ) (a : A)
    (E : OrderedWord N A → Prop) :
    (iidWordLaw π N).prob (fun z => plurality z = some a ∧ E z) =
      wordSum π.mass (winIndicator a E) := by
  classical
  unfold Law.prob wordSum
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : plurality z = some a ∧ E z
  · rw [if_pos h, winIndicator_of h, mul_one]
    rfl
  · rw [if_neg h, winIndicator_of_not h, mul_zero]

/-- **Doc B A6.2.** Replacing the masses of two wrong labels `i, j` by a pair
with the same sum and weakly smaller absolute difference (all other masses,
including the correct mass and abstention, fixed) weakly raises the
probability that `a` wins the ordered plurality jointly with any event `E`
that reads only the positions of `a`. -/
theorem balancing_transfer_win (π π' : Law (Option A)) (a i j : A) (hij : i ≠ j)
    (hai : a ≠ i) (haj : a ≠ j)
    (hoff : ∀ x, x ≠ some i → x ≠ some j → π'.mass x = π.mass x)
    (hsum : π'.mass (some i) + π'.mass (some j) = π.mass (some i) + π.mass (some j))
    (hbal : |π'.mass (some i) - π'.mass (some j)| ≤ |π.mass (some i) - π.mass (some j)|)
    (N : ℕ) (E : OrderedWord N A → Prop) (hE : ReadsOnly a E) :
    (iidWordLaw π N).prob (fun z => plurality z = some a ∧ E z) ≤
      (iidWordLaw π' N).prob (fun z => plurality z = some a ∧ E z) := by
  rw [prob_win_eq_wordSum, prob_win_eq_wordSum]
  exact wordSum_win_balancing i j a hij hai haj π.mass π'.mass π.nonneg π'.nonneg
    hoff hsum hbal E hE

theorem voteAccuracy_eq_win (π : Law (Option A)) (N : ℕ) (a : A) :
    voteAccuracy π N a = (iidWordLaw π N).prob (fun z => plurality z = some a ∧ True) := by
  unfold voteAccuracy correctVote
  simp only [and_true]

theorem jointVoteReach_eq_win (π : Law (Option A)) (N k : ℕ) (a : A) :
    jointVoteReach π N k a =
      (iidWordLaw π N).prob (fun z => plurality z = some a ∧ reaches z k a) := rfl

theorem jointVoteAbsent_eq_win (π : Law (Option A)) (N k : ℕ) (a : A) :
    jointVoteAbsent π N k a =
      (iidWordLaw π N).prob (fun z => plurality z = some a ∧ ¬ reaches z k a) := rfl

/-- Reach of the correct answer depends on the law only through its mass,
for every prefix length (an over-long prefix is the full word). -/
theorem reachProbability_eq_min (π : Law (Option A)) (N k : ℕ) (a : A) :
    reachProbability π N k a = 1 - (1 - π.mass (some a)) ^ (min k N) := by
  have h : reachProbability π N k a = reachProbability π N (min k N) a := by
    unfold reachProbability
    congr 1
    funext z
    apply propext
    unfold reaches
    constructor
    · rintro ⟨t, ht, hz⟩; exact ⟨t, lt_min ht t.isLt, hz⟩
    · rintro ⟨t, ht, hz⟩; exact ⟨t, lt_of_lt_of_le ht (min_le_left _ _), hz⟩
  rw [h, reach_prefix_probability π N (min k N) (min_le_right _ _) a]

/-- The full A6.2 conclusion for one balancing transfer: accuracy and both
correct-vote cells weakly rise; both wrong-vote cells weakly fall. -/
theorem balancing_transfer_cells (π π' : Law (Option A)) (a i j : A) (hij : i ≠ j)
    (hai : a ≠ i) (haj : a ≠ j)
    (hoff : ∀ x, x ≠ some i → x ≠ some j → π'.mass x = π.mass x)
    (hsum : π'.mass (some i) + π'.mass (some j) = π.mass (some i) + π.mass (some j))
    (hbal : |π'.mass (some i) - π'.mass (some j)| ≤ |π.mass (some i) - π.mass (some j)|)
    (N k : ℕ) :
    voteAccuracy π N a ≤ voteAccuracy π' N a ∧
    jointVoteReach π N k a ≤ jointVoteReach π' N k a ∧
    jointVoteAbsent π N k a ≤ jointVoteAbsent π' N k a ∧
    cellProbability π' N k a .posted ≤ cellProbability π N k a .posted ∧
    cellProbability π' N k a .absent ≤ cellProbability π N k a .absent := by
  have hV : voteAccuracy π N a ≤ voteAccuracy π' N a := by
    rw [voteAccuracy_eq_win, voteAccuracy_eq_win]
    exact balancing_transfer_win π π' a i j hij hai haj hoff hsum hbal N _ (readsOnly_true a)
  have hR : jointVoteReach π N k a ≤ jointVoteReach π' N k a := by
    rw [jointVoteReach_eq_win, jointVoteReach_eq_win]
    exact balancing_transfer_win π π' a i j hij hai haj hoff hsum hbal N _
      (readsOnly_reaches a k)
  have hA : jointVoteAbsent π N k a ≤ jointVoteAbsent π' N k a := by
    rw [jointVoteAbsent_eq_win, jointVoteAbsent_eq_win]
    exact balancing_transfer_win π π' a i j hij hai haj hoff hsum hbal N _
      (readsOnly_not_reaches a k)
  have hpa : π'.mass (some a) = π.mass (some a) :=
    hoff _ (by simpa using hai) (by simpa using haj)
  have hreach : reachProbability π' N k a = reachProbability π N k a := by
    rw [reachProbability_eq_min, reachProbability_eq_min, hpa]
  refine ⟨hV, hR, hA, ?_, ?_⟩
  · rw [cellProbability_posted, cellProbability_posted, hreach]; linarith
  · rw [cellProbability_absent, cellProbability_absent, hreach]; linarith

/-- The concentrating direction stated as in Doc B: moving mass `τ` from the
smaller wrong label `j` to the larger wrong label `i` weakly lowers accuracy
and weakly raises both wrong-vote cells. -/
theorem concentrating_transfer_cells (π πc : Law (Option A)) (a i j : A) (hij : i ≠ j)
    (hai : a ≠ i) (haj : a ≠ j) (τ : ℝ) (hτ : 0 ≤ τ)
    (horder : π.mass (some j) ≤ π.mass (some i))
    (hoff : ∀ x, x ≠ some i → x ≠ some j → πc.mass x = π.mass x)
    (hi : πc.mass (some i) = π.mass (some i) + τ)
    (hj : πc.mass (some j) = π.mass (some j) - τ) (N k : ℕ) :
    voteAccuracy πc N a ≤ voteAccuracy π N a ∧
    cellProbability π N k a .posted ≤ cellProbability πc N k a .posted ∧
    cellProbability π N k a .absent ≤ cellProbability πc N k a .absent := by
  have hoff' : ∀ x, x ≠ some i → x ≠ some j → π.mass x = πc.mass x :=
    fun x h1 h2 => (hoff x h1 h2).symm
  have hsum : π.mass (some i) + π.mass (some j) = πc.mass (some i) + πc.mass (some j) := by
    rw [hi, hj]; ring
  have hbal : |π.mass (some i) - π.mass (some j)| ≤ |πc.mass (some i) - πc.mass (some j)| := by
    rw [hi, hj, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  obtain ⟨hV, -, -, hP, hA⟩ :=
    balancing_transfer_cells πc π a i j hij hai haj hoff' hsum hbal N k
  exact ⟨hV, hP, hA⟩

end Transfer

/-! ### Hardy–Littlewood–Pólya: majorization ⇒ finitely many balancing transfers -/

section HLP

/-- One balancing transfer on a vector: two distinct coordinates are replaced
by a pair with the same sum and weakly smaller absolute difference; all other
coordinates are fixed.  (A swap of two coordinates is the equality case.) -/
def BalancingStep {W : Type*} (x x' : W → ℝ) : Prop :=
  ∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → x' k = x k) ∧
    x' i + x' j = x i + x j ∧ |x' i - x' j| ≤ |x i - x j|

/-- The sum of the first `r` coordinates of a vector on `Fin d`. -/
def prefixSum {d : ℕ} (x : Fin d → ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin d => i.val < r), x i

/-- Majorization of two nonincreasing vectors: prefix-sum dominance, equal totals. -/
def SortedMajorizes {d : ℕ} (x y : Fin d → ℝ) : Prop :=
  Antitone x ∧ Antitone y ∧ (∀ r, prefixSum y r ≤ prefixSum x r) ∧ ∑ i, x i = ∑ i, y i

/-- Doc B A6.3 convention: `x` majorizes `y` (is more concentrated) when the
nonincreasing rearrangements of `x` and `y` satisfy prefix-sum dominance with
equal totals.  The rearrangements are explicit enumerations `σ, τ`. -/
def Majorizes {W : Type*} [Fintype W] (x y : W → ℝ) : Prop :=
  ∃ σ τ : Fin (Fintype.card W) ≃ W, SortedMajorizes (fun i => x (σ i)) (fun i => y (τ i))

theorem antitone_of_transfer {d : ℕ} (x y x' : Fin d → ℝ) (hx : Antitone x) (hy : Antitone y)
    (j k : Fin d) (hjk : j < k) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ x j - y j)
    (hδ2 : δ ≤ y k - x k) (hbetween : ∀ l, j < l → l < k → x l = y l)
    (ej : x' j = x j - δ) (ek : x' k = x k + δ) (eo : ∀ l, l ≠ j → l ≠ k → x' l = x l) :
    Antitone x' := by
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  have hyjk : y k ≤ y j := hy hjk.le
  by_cases hak : a = k
  · subst hak
    have hbk : b ≠ a := ne_of_gt hlt
    have hbj : b ≠ j := ne_of_gt (lt_trans hjk hlt)
    rw [eo b hbj hbk, ek]
    linarith [hx hlt.le]
  by_cases haj : a = j
  · subst haj
    by_cases hbk : b = k
    · subst hbk
      rw [ej, ek]
      linarith
    · have hbj : b ≠ a := ne_of_gt hlt
      rw [eo b hbj hbk, ej]
      rcases lt_or_gt_of_ne hbk with hb | hb
      · rw [hbetween b hlt hb]
        linarith [hy hlt.le]
      · linarith [hx hb.le]
  rw [eo a haj hak]
  by_cases hbk : b = k
  · subst hbk
    rw [ek]
    rcases lt_or_gt_of_ne haj with ha | ha
    · linarith [hx ha.le]
    · rw [hbetween a ha hlt]
      linarith [hy hlt.le]
  by_cases hbj : b = j
  · subst hbj
    rw [ej]
    linarith [hx hlt.le]
  · rw [eo b hbj hbk]
    exact hx hlt.le

/-- HLP for sorted vectors, by induction on the number of coordinates where
`x` and `y` differ (Robin Hood / T-transform step; no coordinate is deleted). -/
theorem hlp_sorted {d : ℕ} : ∀ (n : ℕ) (x y : Fin d → ℝ),
    (univ.filter fun i => x i ≠ y i).card = n → SortedMajorizes x y →
    ReflTransGen BalancingStep x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y hn hmaj
  obtain ⟨hx, hy, hpre, htot⟩ := hmaj
  by_cases hxy : x = y
  · subst hxy
    exact ReflTransGen.refl
  have hex : ∃ k, x k < y k := by
    by_contra hno
    push_neg at hno
    apply hxy
    funext k
    have hs : ∑ i, (x i - y i) = 0 := by rw [Finset.sum_sub_distrib, htot, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sub_nonneg.mpr (hno i))).1 hs k (mem_univ k)
    linarith
  let K := univ.filter fun k => x k < y k
  have hKne : K.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, by simp [K, hk]⟩
  set k := K.min' hKne with hkdef
  have hk : x k < y k := (Finset.mem_filter.mp (K.min'_mem hKne)).2
  have hbefore : ∀ l, l < k → y l ≤ x l := by
    intro l hl
    by_contra h
    push_neg at h
    have := K.min'_le l (by simp [K, h])
    exact absurd hl (not_lt.mpr this)
  have hJ : ∃ l, l < k ∧ x l ≠ y l := by
    by_contra hno
    push_neg at hno
    have h1 := hpre (k.val + 1)
    have h2 : prefixSum y (k.val + 1) - prefixSum x (k.val + 1) = y k - x k := by
      unfold prefixSum
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
      · intro b hb hbk
        have hbv : b.val < k.val + 1 := (Finset.mem_filter.mp hb).2
        have hblt : b < k := lt_of_le_of_ne (Fin.le_def.mpr (by omega)) hbk
        rw [hno b hblt]
        ring
      · intro hk'
        exact absurd (Finset.mem_filter.mpr ⟨mem_univ k, Nat.lt_succ_self k.val⟩ :
          k ∈ univ.filter (fun i : Fin d => i.val < k.val + 1)) hk'
    linarith
  let J := univ.filter fun l => l < k ∧ x l ≠ y l
  have hJne : J.Nonempty := by
    obtain ⟨l, hl⟩ := hJ
    exact ⟨l, by simp [J, hl]⟩
  set j := J.max' hJne with hjdef
  have hj : j < k ∧ x j ≠ y j := (Finset.mem_filter.mp (J.max'_mem hJne)).2
  have hjgt : y j < x j := lt_of_le_of_ne (hbefore j hj.1) (Ne.symm hj.2)
  have hbetween : ∀ l, j < l → l < k → x l = y l := by
    intro l h1 h2
    by_contra h
    have := J.le_max' l (by simp [J, h2, h])
    exact absurd h1 (not_lt.mpr this)
  set δ := min (x j - y j) (y k - x k) with hδdef
  have hδ1 : δ ≤ x j - y j := min_le_left _ _
  have hδ2 : δ ≤ y k - x k := min_le_right _ _
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hjk : j ≠ k := ne_of_lt hj.1
  let x' : Fin d → ℝ := fun l => x l + (if l = k then δ else 0) - (if l = j then δ else 0)
  have ej : x' j = x j - δ := by simp [x', hjk]
  have ek : x' k = x k + δ := by simp [x', hjk.symm]
  have eo : ∀ l, l ≠ j → l ≠ k → x' l = x l := by
    intro l h1 h2
    simp [x', h1, h2]
  have hyjk : y k ≤ y j := hy hj.1.le
  -- the transfer step
  have hstep : BalancingStep x x' := by
    refine ⟨j, k, hjk, eo, by rw [ej, ek]; ring, ?_⟩
    rw [ej, ek, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  -- the residual is sorted and still majorizes y
  have hx' : Antitone x' :=
    antitone_of_transfer x y x' hx hy j k hj.1 δ hδpos.le hδ1 hδ2 hbetween ej ek eo
  have hpsum : ∀ r, prefixSum x' r = prefixSum x r + (if k.val < r then δ else 0) -
      (if j.val < r then δ else 0) := by
    intro r
    unfold prefixSum
    simp only [x', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_filter, Finset.mem_univ, true_and]
  have hpre' : ∀ r, prefixSum y r ≤ prefixSum x' r := by
    intro r
    rw [hpsum r]
    by_cases hkr : k.val < r
    · have hjr : j.val < r := lt_trans (Fin.lt_def.mp hj.1) hkr
      simp only [hkr, hjr, ↓reduceIte]
      linarith [hpre r]
    · simp only [hkr, ↓reduceIte, add_zero]
      by_cases hjr : j.val < r
      · simp only [hjr, ↓reduceIte]
        have hsum : x j - y j ≤ ∑ i ∈ univ.filter (fun i : Fin d => i.val < r), (x i - y i) := by
          apply Finset.single_le_sum (f := fun i => x i - y i)
          · intro i hi
            have hiv : i.val < r := (Finset.mem_filter.mp hi).2
            have hik : i < k := Fin.lt_def.mpr (by omega)
            exact sub_nonneg.mpr (hbefore i hik)
          · exact Finset.mem_filter.mpr ⟨mem_univ _, hjr⟩
        rw [Finset.sum_sub_distrib] at hsum
        unfold prefixSum
        linarith
      · simp only [hjr, ↓reduceIte, sub_zero]
        exact hpre r
  have htot' : ∑ i, x' i = ∑ i, y i := by
    rw [← htot]
    simp [x', Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- strictly fewer disagreements
  have hsub : (univ.filter fun i => x' i ≠ y i) ⊂ (univ.filter fun i => x i ≠ y i) := by
    have hss : (univ.filter fun i => x' i ≠ y i) ⊆ (univ.filter fun i => x i ≠ y i) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      by_cases h1 : l = j
      · rw [h1]; exact hj.2
      · by_cases h2 : l = k
        · rw [h2]; exact ne_of_lt hk
        · rwa [eo l h1 h2] at hl
    rw [Finset.ssubset_iff_of_subset hss]
    rcases le_total (x j - y j) (y k - x k) with h | h
    · refine ⟨j, by simp [hj.2], ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [ej, hδdef, min_eq_left h]
      ring
    · refine ⟨k, by simp [ne_of_lt hk], ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [ek, hδdef, min_eq_right h]
      ring
  have hlt : (univ.filter fun i => x' i ≠ y i).card < n := hn ▸ Finset.card_lt_card hsub
  exact ReflTransGen.head hstep (ih _ hlt x' y rfl ⟨hx', hy, hpre', htot'⟩)

theorem balancingStep_comp_equiv {W V : Type*} (e : W ≃ V) {x x' : W → ℝ}
    (h : BalancingStep x x') :
    BalancingStep (fun v => x (e.symm v)) (fun v => x' (e.symm v)) := by
  obtain ⟨i, j, hij, hoff, hsum, hbal⟩ := h
  refine ⟨e i, e j, fun h' => hij (e.injective h'), ?_, by simpa using hsum, by simpa using hbal⟩
  intro k hk1 hk2
  apply hoff
  · intro h'; apply hk1; rw [← h']; simp
  · intro h'; apply hk2; rw [← h']; simp

/-- Any rearrangement of `y` reaches `y` by swaps, each a balancing step. -/
theorem perm_reaches {W : Type*} [Fintype W] [DecidableEq W] (ρ : Equiv.Perm W) :
    ∀ y : W → ℝ, ReflTransGen BalancingStep (fun w => y (ρ w)) y := by
  induction ρ using Equiv.Perm.swap_induction_on with
  | one =>
    intro y
    exact ReflTransGen.refl
  | swap_mul f a b hab ih =>
    intro y
    have h1 := ih (fun w => y (Equiv.swap a b w))
    have h2 : BalancingStep (fun w => y (Equiv.swap a b w)) y := by
      refine ⟨a, b, hab, ?_, ?_, ?_⟩
      · intro k hk1 hk2
        show y k = y (Equiv.swap a b k)
        rw [Equiv.swap_apply_of_ne_of_ne hk1 hk2]
      · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
        ring
      · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
        rw [abs_sub_comm]
    simpa only [Equiv.Perm.mul_apply] using h1.tail h2

/-- **Doc B A6.3 (HLP, direction used).** If `x` majorizes `y`, then `y` is
reached from `x` by finitely many balancing transfers (permutations included,
as products of swaps). -/
theorem hlp_majorizes {W : Type*} [Fintype W] [DecidableEq W] (x y : W → ℝ)
    (h : Majorizes x y) : ReflTransGen BalancingStep x y := by
  obtain ⟨σ, τ, hs⟩ := h
  have h1 := hlp_sorted _ _ _ rfl hs
  have h2 : ReflTransGen BalancingStep x (fun w => y (τ (σ.symm w))) := by
    have := ReflTransGen.lift (fun v : Fin (Fintype.card W) → ℝ => fun w => v (σ.symm w))
      (fun a b hab => balancingStep_comp_equiv σ hab) h1
    simpa only [Equiv.apply_symm_apply] using this
  have h3 := perm_reaches (σ.symm.trans τ) y
  simp only [Equiv.trans_apply] at h3
  exact h2.trans h3

end HLP

/-! ### Doc B A6.4: the concentration theorem for both cells and the premium -/

section Concentration

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A mass function rebuilt from abstention mass `u`, correct mass `p`, and a
wrong-mass vector indexed by the wrong labels. -/
def massOf (a : A) (u p : ℝ) (q : {b : A // b ≠ a} → ℝ) : Option A → ℝ
  | none => u
  | some b => if h : b = a then p else q ⟨b, h⟩

/-- The wrong-mass vector of an answer law. -/
def wrongMass (π : Law (Option A)) (a : A) : {b : A // b ≠ a} → ℝ :=
  fun w => π.mass (some w.1)

theorem massOf_wrongMass (π : Law (Option A)) (a : A) :
    massOf a (π.mass none) (π.mass (some a)) (wrongMass π a) = π.mass := by
  funext x
  cases x with
  | none => rfl
  | some b =>
    by_cases h : b = a
    · subst h
      simp [massOf]
    · simp [massOf, h, wrongMass]

theorem massOf_some_wrong (a : A) (u p : ℝ) (q : {b : A // b ≠ a} → ℝ)
    (w : {b : A // b ≠ a}) : massOf a u p q (some w.1) = q w := by
  simp [massOf, w.2]

theorem massOf_nonneg (a : A) {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p)
    {q : {b : A // b ≠ a} → ℝ} (hq : ∀ w, 0 ≤ q w) : ∀ x, 0 ≤ massOf a u p q x := by
  intro x
  cases x with
  | none => exact hu
  | some b =>
    by_cases h : b = a
    · simp [massOf, h, hp]
    · simp only [massOf, h, dite_false]
      exact hq _

/-- A balancing step keeps a nonnegative vector nonnegative. -/
theorem balancingStep_nonneg {W : Type*} {q q' : W → ℝ} (h : BalancingStep q q')
    (hq : ∀ w, 0 ≤ q w) : ∀ w, 0 ≤ q' w := by
  obtain ⟨i, j, hij, hoff, hsum, hbal⟩ := h
  have hab : |q i - q j| ≤ q i + q j :=
    abs_sub_le_iff.mpr ⟨by linarith [hq j], by linarith [hq i]⟩
  have h1 := le_abs_self (q' i - q' j)
  have h2 := neg_abs_le (q' i - q' j)
  intro w
  by_cases hwi : w = i
  · subst hwi
    linarith
  · by_cases hwj : w = j
    · subst hwj
      linarith
    · rw [hoff w hwi hwj]
      exact hq w

theorem reflTransGen_nonneg {W : Type*} {q q' : W → ℝ}
    (h : ReflTransGen BalancingStep q q') (hq : ∀ w, 0 ≤ q w) : ∀ w, 0 ≤ q' w := by
  induction h with
  | refl => exact hq
  | tail _ hbc ih => exact balancingStep_nonneg hbc ih

theorem wordSum_step (a : A) {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p)
    {q q' : {b : A // b ≠ a} → ℝ} (hq : ∀ w, 0 ≤ q w) (hq' : ∀ w, 0 ≤ q' w)
    (hs : BalancingStep q q') {N : ℕ} (E : OrderedWord N A → Prop) (hE : ReadsOnly a E) :
    wordSum (massOf a u p q) (winIndicator a E) ≤
      wordSum (massOf a u p q') (winIndicator a E) := by
  obtain ⟨i, j, hij, hoff, hsum, hbal⟩ := hs
  apply wordSum_win_balancing i.1 j.1 a (fun h => hij (Subtype.ext h)) (Ne.symm i.2)
    (Ne.symm j.2) _ _ (massOf_nonneg a hu hp hq) (massOf_nonneg a hu hp hq') _ _ _ E hE
  · intro x hx1 hx2
    cases x with
    | none => rfl
    | some b =>
      by_cases h : b = a
      · simp [massOf, h]
      · simp only [massOf, h, dite_false]
        apply hoff
        · intro he
          apply hx1
          rw [← he]
        · intro he
          apply hx2
          rw [← he]
  · rw [massOf_some_wrong, massOf_some_wrong, massOf_some_wrong, massOf_some_wrong]
    exact hsum
  · rw [massOf_some_wrong, massOf_some_wrong, massOf_some_wrong, massOf_some_wrong]
    exact hbal

theorem wordSum_chain (a : A) {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p)
    {q q' : {b : A // b ≠ a} → ℝ} (h : ReflTransGen BalancingStep q q')
    (hq : ∀ w, 0 ≤ q w) {N : ℕ} (E : OrderedWord N A → Prop) (hE : ReadsOnly a E) :
    wordSum (massOf a u p q) (winIndicator a E) ≤
      wordSum (massOf a u p q') (winIndicator a E) := by
  induction h with
  | refl => exact le_rfl
  | tail hab hbc ih =>
    exact ih.trans (wordSum_step a hu hp (reflTransGen_nonneg hab hq)
      (balancingStep_nonneg hbc (reflTransGen_nonneg hab hq)) hbc E hE)

/-- Majorization of wrong masses (same correct mass and abstention) weakly
lowers the probability that `a` wins jointly with any event reading only the
positions of `a`. -/
theorem concentration_win (π π' : Law (Option A)) (a : A)
    (hu : π'.mass none = π.mass none) (hp : π'.mass (some a) = π.mass (some a))
    (hmaj : Majorizes (wrongMass π a) (wrongMass π' a)) (N : ℕ)
    (E : OrderedWord N A → Prop) (hE : ReadsOnly a E) :
    (iidWordLaw π N).prob (fun z => plurality z = some a ∧ E z) ≤
      (iidWordLaw π' N).prob (fun z => plurality z = some a ∧ E z) := by
  rw [prob_win_eq_wordSum, prob_win_eq_wordSum]
  have e1 := massOf_wrongMass π a
  have e2 := massOf_wrongMass π' a
  rw [hu, hp] at e2
  rw [← e1, ← e2]
  exact wordSum_chain a (π.nonneg _) (π.nonneg _) (hlp_majorizes _ _ hmaj)
    (fun w => π.nonneg _) E hE

/-- **Doc B A6.4 (cells).** If the wrong-mass vector of `π` majorizes that of
`π'` (same `N, k`, correct mass and abstention), then `V_N(π) ≤ V_N(π')`,
`pPost(π) ≥ pPost(π')` and `pNone(π) ≥ pNone(π')`. -/
theorem concentration_cells (π π' : Law (Option A)) (a : A)
    (hu : π'.mass none = π.mass none) (hp : π'.mass (some a) = π.mass (some a))
    (hmaj : Majorizes (wrongMass π a) (wrongMass π' a)) (N k : ℕ) :
    voteAccuracy π N a ≤ voteAccuracy π' N a ∧
    cellProbability π' N k a .posted ≤ cellProbability π N k a .posted ∧
    cellProbability π' N k a .absent ≤ cellProbability π N k a .absent := by
  have hV : voteAccuracy π N a ≤ voteAccuracy π' N a := by
    rw [voteAccuracy_eq_win, voteAccuracy_eq_win]
    exact concentration_win π π' a hu hp hmaj N _ (readsOnly_true a)
  have hR : jointVoteReach π N k a ≤ jointVoteReach π' N k a := by
    rw [jointVoteReach_eq_win, jointVoteReach_eq_win]
    exact concentration_win π π' a hu hp hmaj N _ (readsOnly_reaches a k)
  have hA : jointVoteAbsent π N k a ≤ jointVoteAbsent π' N k a := by
    rw [jointVoteAbsent_eq_win, jointVoteAbsent_eq_win]
    exact concentration_win π π' a hu hp hmaj N _ (readsOnly_not_reaches a k)
  have hreach : reachProbability π' N k a = reachProbability π N k a := by
    rw [reachProbability_eq_min, reachProbability_eq_min, hp]
  refine ⟨hV, ?_, ?_⟩
  · rw [cellProbability_posted, cellProbability_posted, hreach]; linarith
  · rw [cellProbability_absent, cellProbability_absent, hreach]; linarith

theorem cellOf_post_iff (v r : Prop) : EpistemicPayoff.cellOf v r = .post ↔ ¬ v ∧ r := by
  classical
  by_cases hv : v <;> by_cases hr : r <;> simp [EpistemicPayoff.cellOf, hv, hr]

theorem cellOf_absent_iff (v r : Prop) :
    EpistemicPayoff.cellOf v r = .absent ↔ ¬ v ∧ ¬ r := by
  classical
  by_cases hv : v <;> by_cases hr : r <;> simp [EpistemicPayoff.cellOf, hv, hr]

/-- The constant-pick-up premium of the actual comparator cells, with the
pick-up constants `κ` a fixed parameter (not conditional means of a kernel). -/
noncomputable def premium (κ : EpistemicPayoff.Cell → ℝ) (π : Law (Option A)) (N k : ℕ)
    (a : A) : ℝ :=
  (EpistemicPayoff.comparatorModel (iidWordLaw π N) (fun z => correctVote z a)
    (fun z => reaches z k a)).premium κ

theorem premium_eq (κ : EpistemicPayoff.Cell → ℝ) (π : Law (Option A)) (N k : ℕ) (a : A) :
    premium κ π N k a = κ .post * cellProbability π N k a .posted +
      κ .absent * cellProbability π N k a .absent - (1 - κ .keep) * voteAccuracy π N a := by
  unfold premium
  rw [EpistemicPayoff.premium_identity, EpistemicPayoff.comparatorModel_keep]
  have hpost : (EpistemicPayoff.comparatorModel (iidWordLaw π N) (fun z => correctVote z a)
      (fun z => reaches z k a)).weight .post = cellProbability π N k a .posted := by
    change (iidWordLaw π N).prob (fun z => EpistemicPayoff.cellOf (correctVote z a)
      (reaches z k a) = .post) = (iidWordLaw π N).prob (fun z => comparatorCell z k a = .posted)
    congr 1
    funext z
    apply propext
    rw [cellOf_post_iff, comparatorCell_posted_iff]
  have habs : (EpistemicPayoff.comparatorModel (iidWordLaw π N) (fun z => correctVote z a)
      (fun z => reaches z k a)).weight .absent = cellProbability π N k a .absent := by
    change (iidWordLaw π N).prob (fun z => EpistemicPayoff.cellOf (correctVote z a)
      (reaches z k a) = .absent) = (iidWordLaw π N).prob (fun z => comparatorCell z k a = .absent)
    congr 1
    funext z
    apply propext
    rw [cellOf_absent_iff, comparatorCell_absent_iff]
  rw [hpost, habs]
  unfold voteAccuracy
  ring

/-- **Doc B A6.4 (premium).** For FIXED pick-up constants `κ ∈ [0,1]³`,
majorization of the wrong masses weakly raises the premium. -/
theorem concentration_premium (π π' : Law (Option A)) (a : A)
    (hu : π'.mass none = π.mass none) (hp : π'.mass (some a) = π.mass (some a))
    (hmaj : Majorizes (wrongMass π a) (wrongMass π' a))
    (κ : EpistemicPayoff.Cell → ℝ) (hκ : ∀ c, 0 ≤ κ c ∧ κ c ≤ 1) (N k : ℕ) :
    premium κ π' N k a ≤ premium κ π N k a := by
  obtain ⟨hV, hP, hA⟩ := concentration_cells π π' a hu hp hmaj N k
  rw [premium_eq, premium_eq]
  have h1 := mul_le_mul_of_nonneg_left hP (hκ .post).1
  have h2 := mul_le_mul_of_nonneg_left hA (hκ .absent).1
  have h3 := mul_le_mul_of_nonneg_left hV (sub_nonneg.mpr (hκ .keep).2)
  linarith

/-- The fixed-κ premium also weakly rises under one balancing transfer (A6.2). -/
theorem balancing_transfer_premium (π π' : Law (Option A)) (a i j : A) (hij : i ≠ j)
    (hai : a ≠ i) (haj : a ≠ j)
    (hoff : ∀ x, x ≠ some i → x ≠ some j → π'.mass x = π.mass x)
    (hsum : π'.mass (some i) + π'.mass (some j) = π.mass (some i) + π.mass (some j))
    (hbal : |π'.mass (some i) - π'.mass (some j)| ≤ |π.mass (some i) - π.mass (some j)|)
    (κ : EpistemicPayoff.Cell → ℝ) (hκ : ∀ c, 0 ≤ κ c ∧ κ c ≤ 1) (N k : ℕ) :
    premium κ π' N k a ≤ premium κ π N k a := by
  obtain ⟨hV, -, -, hP, hA⟩ := balancing_transfer_cells π π' a i j hij hai haj hoff hsum hbal N k
  rw [premium_eq, premium_eq]
  have h1 := mul_le_mul_of_nonneg_left hP (hκ .post).1
  have h2 := mul_le_mul_of_nonneg_left hA (hκ .absent).1
  have h3 := mul_le_mul_of_nonneg_left hV (sub_nonneg.mpr (hκ .keep).2)
  linarith

end Concentration

/-! ### Doc B A6.5: concentration need not raise the gain from size -/

section SizeCounterexample

/-- Count profile with no abstentions: counts `c0` (correct), `c1`, `c2`. -/
def prof3 (c0 c1 c2 : ℕ) : Option (Fin 3) → ℕ
  | none => 0
  | some b => ![c0, c1, c2] b

/-- Mass function with no abstention: correct `p`, wrong labels `q1, q2`. -/
def mass3 (p q1 q2 : ℝ) : Option (Fin 3) → ℝ
  | none => 0
  | some b => ![p, q1, q2] b

/-- The answer law with no abstention, correct mass `p`, wrong masses `q1, q2`. -/
noncomputable def law3 (p q1 q2 : ℝ) (hp : 0 ≤ p) (h1 : 0 ≤ q1) (h2 : 0 ≤ q2)
    (ht : p + q1 + q2 = 1) : Law (Option (Fin 3)) where
  mass := mass3 p q1 q2
  nonneg x := by
    cases x with
    | none => exact le_rfl
    | some b => fin_cases b <;> simp [mass3, hp, h1, h2]
  total := by
    simp only [Fintype.sum_option, Fin.sum_univ_three, mass3]
    simp [ht]

theorem sum_validCountProfiles_fin3 (N : ℕ) (T : (Option (Fin 3) → ℕ) → ℝ)
    (hT : ∀ c, c none ≠ 0 → T c = 0) :
    ∑ c ∈ validCountProfiles (Fin 3) N, T c =
      ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.2, T (prof3 p.1 q.1 q.2) := by
  classical
  have hback : ∀ c ∈ (validCountProfiles (Fin 3) N).filter (fun c => c none = 0),
      prof3 (c (some 0)) (c (some 1)) (c (some 2)) = c := by
    intro c hc
    simp only [Finset.mem_filter] at hc
    funext x
    cases x with
    | none => exact hc.2.symm
    | some b => fin_cases b <;> rfl
  rw [Finset.sum_sigma']
  rw [← Finset.sum_filter_of_ne (p := fun c => c none = 0)
    (fun c _ hc => by by_contra h; exact hc (hT c h))]
  apply Finset.sum_nbij' (fun c => (⟨(c (some 0), c (some 1) + c (some 2)),
      (c (some 1), c (some 2))⟩ : (_ : ℕ × ℕ) × (ℕ × ℕ)))
    (fun x => prof3 x.1.1 x.2.1 x.2.2)
  · intro c hc
    simp only [Finset.mem_filter, validCountProfiles, Finset.mem_piAntidiag] at hc
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal, and_true]
    have hs := hc.1.1
    rw [Fintype.sum_option, Fin.sum_univ_three, hc.2] at hs
    omega
  · intro x hx
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx
    simp only [Finset.mem_filter, validCountProfiles, Finset.mem_piAntidiag,
      Finset.mem_univ, implies_true, and_true]
    refine ⟨?_, rfl⟩
    rw [Fintype.sum_option, Fin.sum_univ_three]
    simp only [prof3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    omega
  · intro c hc
    exact hback c hc
  · intro x hx
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx
    obtain ⟨_, hcd⟩ := hx
    subst hcd
    rfl
  · intro c hc
    dsimp only
    rw [hback c hc]

theorem multinomial_prof3 (c0 c1 c2 : ℕ) :
    (Nat.multinomial univ (prof3 c0 c1 c2) : ℝ) =
      ((c0 + c1 + c2).factorial : ℝ) / (c0.factorial * c1.factorial * c2.factorial) := by
  have h := Nat.multinomial_spec (univ : Finset (Option (Fin 3))) (prof3 c0 c1 c2)
  simp only [Fintype.prod_option, Fintype.sum_option, Fin.prod_univ_three, Fin.sum_univ_three,
    prof3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Nat.factorial_zero, one_mul, zero_add] at h
  have hpos : (0:ℝ) < c0.factorial * c1.factorial * c2.factorial := by positivity
  rw [eq_div_iff hpos.ne']
  have h' : ((c0.factorial * c1.factorial * c2.factorial * Nat.multinomial univ (prof3 c0 c1 c2) : ℕ) : ℝ) =
      ((c0 + c1 + c2).factorial : ℕ) := by
    rw [← h]
  push_cast at h'
  linarith

theorem prod_mass3_prof3 (p q1 q2 : ℝ) (c0 c1 c2 : ℕ) :
    (∏ q, mass3 p q1 q2 q ^ prof3 c0 c1 c2 q) = p ^ c0 * q1 ^ c1 * q2 ^ c2 := by
  simp only [Fintype.prod_option, Fin.prod_univ_three, mass3, prof3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_zero,
    one_mul]

theorem mem0_prof3 (c0 c1 c2 : ℕ) :
    (0 : Fin 3) ∈ readableModes (prof3 c0 c1 c2) ↔ 0 < c0 ∧ c1 ≤ c0 ∧ c2 ≤ c0 := by
  simp only [readableModes, Finset.mem_filter, Finset.mem_univ, true_and, prof3,
    Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.forall_iff]
  simp

theorem card_prof3 (c0 c1 c2 : ℕ) (h : 0 < c0 ∧ c1 ≤ c0 ∧ c2 ≤ c0) :
    (readableModes (prof3 c0 c1 c2)).card =
      1 + (if c1 = c0 then 1 else 0) + (if c2 = c0 then 1 else 0) := by
  classical
  have hset : readableModes (prof3 c0 c1 c2) =
      univ.filter (fun b : Fin 3 => ![c0, c1, c2] b = c0) := by
    ext b
    simp only [readableModes, Finset.mem_filter, Finset.mem_univ, true_and, prof3]
    fin_cases b <;> simp [Fin.forall_fin_succ] <;> omega
  rw [hset, Finset.card_filter, Fin.sum_univ_three]
  simp

/-- Doc B A3.1 specialized: accuracy of `law3` as an explicit double sum. -/
theorem voteAccuracy_law3 (p q1 q2 : ℝ) (hp : 0 ≤ p) (h1 : 0 ≤ q1) (h2 : 0 ≤ q2)
    (ht : p + q1 + q2 = 1) (N : ℕ) :
    voteAccuracy (law3 p q1 q2 hp h1 h2 ht) N 0 =
      ∑ x ∈ antidiagonal N, ∑ y ∈ antidiagonal x.2,
        ((x.1 + y.1 + y.2).factorial : ℝ) / (x.1.factorial * y.1.factorial * y.2.factorial) *
          (p ^ x.1 * q1 ^ y.1 * q2 ^ y.2) *
          (if 0 < x.1 ∧ y.1 ≤ x.1 ∧ y.2 ≤ x.1 then
            1 / ((1 + (if y.1 = x.1 then 1 else 0) + (if y.2 = x.1 then 1 else 0) : ℕ) : ℝ)
            else 0) := by
  rw [plurality_multinomial_formula]
  rw [sum_validCountProfiles_fin3]
  · apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [multinomial_prof3]
    have hprod : (∏ q, (law3 p q1 q2 hp h1 h2 ht).mass q ^ prof3 x.1 y.1 y.2 q) =
        p ^ x.1 * q1 ^ y.1 * q2 ^ y.2 := prod_mass3_prof3 p q1 q2 x.1 y.1 y.2
    rw [hprod]
    congr 1
    by_cases h : 0 < x.1 ∧ y.1 ≤ x.1 ∧ y.2 ≤ x.1
    · rw [if_pos ((mem0_prof3 _ _ _).mpr h), if_pos h, card_prof3 _ _ _ h]
    · rw [if_neg (fun hm => h ((mem0_prof3 _ _ _).mp hm)), if_neg h]
  · intro c hc
    have hz : (∏ q, (law3 p q1 q2 hp h1 h2 ht).mass q ^ c q) = 0 := by
      rw [Fintype.prod_option]
      change mass3 p q1 q2 none ^ c none * _ = 0
      simp [mass3, zero_pow hc]
    rw [hz]
    ring

/-- Concentrated wrong masses `(1/4, 0)` with correct mass `3/4`, no abstention. -/
noncomputable def concLaw : Law (Option (Fin 3)) :=
  law3 (3/4) (1/4) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)

/-- Diffuse wrong masses `(1/8, 1/8)` with correct mass `3/4`, no abstention. -/
noncomputable def diffLaw : Law (Option (Fin 3)) :=
  law3 (3/4) (1/8) (1/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem vote_conc_4 : voteAccuracy concLaw 4 0 = 27/32 := by
  unfold concLaw
  rw [voteAccuracy_law3]
  simp [Finset.Nat.sum_antidiagonal_succ, Nat.factorial]
  norm_num

theorem vote_conc_5 : voteAccuracy concLaw 5 0 = 459/512 := by
  unfold concLaw
  rw [voteAccuracy_law3]
  simp [Finset.Nat.sum_antidiagonal_succ, Nat.factorial]
  norm_num

theorem vote_diff_4 : voteAccuracy diffLaw 4 0 = 459/512 := by
  unfold diffLaw
  rw [voteAccuracy_law3]
  simp [Finset.Nat.sum_antidiagonal_succ, Nat.factorial]
  norm_num

theorem vote_diff_5 : voteAccuracy diffLaw 5 0 = 3807/4096 := by
  unfold diffLaw
  rw [voteAccuracy_law3]
  simp [Finset.Nat.sum_antidiagonal_succ, Nat.factorial]
  norm_num

/-- With the whole comparator posted (`k = N`) and `κ = (keep 1, post 1, none 0)`,
the premium is reach minus accuracy. -/
theorem premium_full_post {A : Type*} [Fintype A] [DecidableEq A] (π : Law (Option A))
    (N : ℕ) (a : A) (κ : EpistemicPayoff.Cell → ℝ) (hk : κ .keep = 1) (hp : κ .post = 1)
    (hn : κ .absent = 0) :
    premium κ π N N a = 1 - (1 - π.mass (some a)) ^ N - voteAccuracy π N a := by
  rw [premium_eq, hk, hp, hn, cellProbability_posted, reach_prefix_probability π N N le_rfl a]
  have hj : jointVoteReach π N N a = voteAccuracy π N a := by
    rw [jointVote_partition π N N a]
    have h0 : jointVoteAbsent π N N a = 0 := by
      unfold jointVoteAbsent
      have he : (fun z : OrderedWord N A => correctVote z a ∧ ¬ reaches z N a) =
          fun _ => False := by
        funext z
        apply propext
        constructor
        · rintro ⟨h1, h2⟩
          exact h2 (correctVote_reaches_full z a h1)
        · exact False.elim
      rw [he, Law.prob_false]
    rw [h0, add_zero]
  rw [hj]
  ring

/-- The fixed pick-up constants of the A6.5 example: keep 1, post 1, none 0. -/
def kappaFullPost : EpistemicPayoff.Cell → ℝ
  | .keep => 1
  | .post => 1
  | .absent => 0

/-- **Doc B A6.5 (size-interaction counterexample), on the actual IID laws.**
`p = 3/4`, no abstention, `k = N`, `κ = (1, 1, 0)`.  Concentrated `(1/4, 0)`:
`D₄ = 39/256`, `D₅ = 105/1024`; diffuse `(1/8, 1/8)`: `D₄ = 51/512`,
`D₅ = 285/4096`.  Concentration raises the premium at each size, but lowers the
size change `D₅ - D₄` by `81/4096`. -/
theorem size_interaction_counterexample :
    premium kappaFullPost concLaw 4 4 0 = 39/256 ∧
    premium kappaFullPost concLaw 5 5 0 = 105/1024 ∧
    premium kappaFullPost diffLaw 4 4 0 = 51/512 ∧
    premium kappaFullPost diffLaw 5 5 0 = 285/4096 ∧
    premium kappaFullPost diffLaw 4 4 0 < premium kappaFullPost concLaw 4 4 0 ∧
    premium kappaFullPost diffLaw 5 5 0 < premium kappaFullPost concLaw 5 5 0 ∧
    (premium kappaFullPost concLaw 5 5 0 - premium kappaFullPost concLaw 4 4 0) -
      (premium kappaFullPost diffLaw 5 5 0 - premium kappaFullPost diffLaw 4 4 0) =
        -81/4096 := by
  have hc : concLaw.mass (some 0) = 3/4 := by simp [concLaw, law3, mass3]
  have hd : diffLaw.mass (some 0) = 3/4 := by simp [diffLaw, law3, mass3]
  have e1 : premium kappaFullPost concLaw 4 4 0 = 39/256 := by
    rw [premium_full_post _ _ _ _ rfl rfl rfl, hc, vote_conc_4]; norm_num
  have e2 : premium kappaFullPost concLaw 5 5 0 = 105/1024 := by
    rw [premium_full_post _ _ _ _ rfl rfl rfl, hc, vote_conc_5]; norm_num
  have e3 : premium kappaFullPost diffLaw 4 4 0 = 51/512 := by
    rw [premium_full_post _ _ _ _ rfl rfl rfl, hd, vote_diff_4]; norm_num
  have e4 : premium kappaFullPost diffLaw 5 5 0 = 285/4096 := by
    rw [premium_full_post _ _ _ _ rfl rfl rfl, hd, vote_diff_5]; norm_num
  rw [e1, e2, e3, e4]
  norm_num

/-- The wrong labels `1, 2` of `Fin 3`, enumerated in the order used below. -/
def wrongEnum : Fin 2 ≃ {b : Fin 3 // b ≠ 0} where
  toFun i := if i = 0 then ⟨1, by simp⟩ else ⟨2, by simp⟩
  invFun w := if w.1 = 1 then 0 else 1
  left_inv i := by fin_cases i <;> simp
  right_inv w := by
    obtain ⟨b, hb⟩ := w
    fin_cases b
    · exact absurd rfl hb
    · simp
    · simp

theorem prefixSum_fin2 (f : Fin 2 → ℝ) (r : ℕ) :
    prefixSum f r = (if 0 < r then f 0 else 0) + (if 1 < r then f 1 else 0) := by
  unfold prefixSum
  rw [Finset.sum_filter, Fin.sum_univ_two]
  simp

/-- The A6.5 concentrated wrong masses `(1/4, 0)` majorize the diffuse `(1/8, 1/8)`,
so the fixed-size theorem `concentration_premium` applies at every size. -/
theorem conc_majorizes_diff : Majorizes (wrongMass concLaw 0) (wrongMass diffLaw 0) := by
  unfold Majorizes
  have hcard : Fintype.card {b : Fin 3 // b ≠ 0} = 2 :=
    (Fintype.card_congr wrongEnum).symm.trans (Fintype.card_fin 2)
  generalize hn : Fintype.card {b : Fin 3 // b ≠ 0} = n
  obtain rfl : n = 2 := hn.symm.trans hcard
  have hx0 : wrongMass concLaw 0 (wrongEnum 0) = 1/4 := by
    simp [wrongMass, wrongEnum, concLaw, law3, mass3]
  have hx1 : wrongMass concLaw 0 (wrongEnum 1) = 0 := by
    simp [wrongMass, wrongEnum, concLaw, law3, mass3]
  have hy0 : wrongMass diffLaw 0 (wrongEnum 0) = 1/8 := by
    simp [wrongMass, wrongEnum, diffLaw, law3, mass3]
  have hy1 : wrongMass diffLaw 0 (wrongEnum 1) = 1/8 := by
    simp [wrongMass, wrongEnum, diffLaw, law3, mass3]
  refine ⟨wrongEnum, wrongEnum, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro a b _
    fin_cases a <;> fin_cases b <;> simp [hy0, hy1]
  · intro r
    rw [prefixSum_fin2, prefixSum_fin2, hx0, hx1, hy0, hy1]
    rcases Nat.lt_or_ge 1 r with h1 | h1
    · have h0 : 0 < r := by omega
      simp [h0, h1] <;> norm_num
    · rcases Nat.lt_or_ge 0 r with h0 | h0
      · have h1' : ¬ 1 < r := by omega
        simp [h0, h1'] <;> norm_num
      · have h0' : ¬ 0 < r := by omega
        have h1' : ¬ 1 < r := by omega
        simp [h0', h1']
  · rw [Fin.sum_univ_two, Fin.sum_univ_two, hx0, hx1, hy0, hy1]
    norm_num

/-- Hence, at every size and for every fixed `κ ∈ [0,1]³`, the concentrated
premium is at least the diffuse one (consistent with the values above). -/
theorem conc_premium_ge_diff (κ : EpistemicPayoff.Cell → ℝ) (hκ : ∀ c, 0 ≤ κ c ∧ κ c ≤ 1)
    (N k : ℕ) : premium κ diffLaw N k 0 ≤ premium κ concLaw N k 0 :=
  concentration_premium concLaw diffLaw 0 (by simp [concLaw, diffLaw, law3, mass3])
    (by simp [concLaw, diffLaw, law3, mass3]) conc_majorizes_diff κ hκ N k

end SizeCounterexample

end SEKernel.Closeout.Concentration

#print axioms SEKernel.Closeout.Concentration.concentrating_transfer_cells
#print axioms SEKernel.Closeout.Concentration.hlp_majorizes
#print axioms SEKernel.Closeout.Concentration.concentration_premium
#print axioms SEKernel.Closeout.Concentration.size_interaction_counterexample
