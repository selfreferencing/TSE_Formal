import SEKernel.PluralityConcentration

namespace SEKernel.Closeout.Concentration

open Finset Relation

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

end SEKernel.Closeout.Concentration
