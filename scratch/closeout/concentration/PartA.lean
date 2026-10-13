import SEKernel.PluralityConcentration

namespace SEKernel.Closeout.Concentration

open Finset SEKernel.FiniteProbability SEKernel.Epistemic SEKernel.EpistemicConcentration

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

/-- Swapping the two weights does not change a symmetric binomial functional. -/
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

end SEKernel.Closeout.Concentration
