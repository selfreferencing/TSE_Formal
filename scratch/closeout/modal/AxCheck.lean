/-
Close-out: Doc B Theorem A3.4 (finite monotonicity for a correct mode).

Let `A` be the finite type of readable labels (nonempty, since a correct label
`c : A` is given), `M = Fintype.card A`, `π` a law on `Option A` with abstention
mass `u = π.mass none`, and suppose `c` is a weak sampling mode:
`π.mass (some c) ≥ π.mass (some b)` for every `b` (ties allowed).  Then for
every `N`,
  `voteAccuracy π (N+1) c - voteAccuracy π N c ≥ u^N (1-u) / M`.

Proof by finite symmetrization (Doc B, A3.3).  The uniform prior over
permutations of the readable labels (abstention fixed) is only an algebraic
device; nothing is conditioned on.  We use the unnormalized joint weight
  `jointWeight π c z d = Σ_{ρ : ρ d = c} Π_i π.mass (ρ (z i))`,
which is `M!` times Doc B's `W_N(z,d)` (reindexed by `ρ = σ⁻¹`): in state `ρ`
the observed label `x` carries the original mass of `ρ x`, and the designated
correct label is `ρ⁻¹ c`.
  * swap pairing (`jointWeight_le_of_labelCount_le`): a label with at least
    the count of `d` has at least the weight of `d`;
  * hence the plurality winner (or `c` on the all-abstention word) attains the
    maximal weight (`jointWeight_le_winnerOr`);
  * label equivariance (`plurality_relabel`) gives
    `J_N = Σ_z max_d W_N(z,d) = V_N + u^N / M` (`normalized_J_eq`);
  * `W_N(z,d) = Σ_a W_{N+1}(a·z, d)` (`jointWeight_eq_sum_cons`) and
    max-of-sum ≤ sum-of-max give `J_N ≤ J_{N+1}`.
Only finite sums and products appear; standard axioms only.
-/
import SEKernel.PluralityBounds

namespace SEKernel.Closeout.ModalMonotonicity

open Finset
open SEKernel.FiniteProbability
open SEKernel.Epistemic

/-! ### The two-label exchange inequality -/

section Pairing

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A product over word positions is a product over labels of count powers. -/
theorem prod_word_eq_prod_pow_labelCount {n : ℕ}
    (f : Option A → ℝ) (z : OrderedWord n A) :
    ∏ i, f (z i) = ∏ x : Option A, f x ^ labelCount z x := by
  rw [← Finset.prod_fiberwise' Finset.univ z f]
  apply Finset.prod_congr rfl
  intro x _
  rw [Finset.prod_const]
  congr 1
  unfold labelCount
  congr

/-- Exchange of two exponents: if `f v ≤ f u` and `k u ≤ k v`, moving the
larger exponent onto the larger base does not decrease the product.  This is
the factor `(pq)^b (p^(a-b) - q^(a-b)) ≥ 0` of Doc B. -/
theorem prod_pow_le_prod_pow_swap (f : Option A → ℝ) (hf : ∀ x, 0 ≤ f x)
    (k : Option A → ℕ) (u v : Option A) (hfuv : f v ≤ f u) (hk : k u ≤ k v) :
    ∏ x, f x ^ k x ≤ ∏ x, f x ^ k (Equiv.swap u v x) := by
  by_cases huv : u = v
  · subst huv
    simp
  have hu : u ∈ (univ : Finset (Option A)) := mem_univ u
  have hv : v ∈ (univ.erase u) := mem_erase.2 ⟨Ne.symm huv, mem_univ v⟩
  have hsplit : ∀ F : Option A → ℝ,
      ∏ x, F x = F u * (F v * ∏ x ∈ (univ.erase u).erase v, F x) := by
    intro F
    rw [Finset.mul_prod_erase _ _ hv, Finset.mul_prod_erase _ _ hu]
  rw [hsplit, hsplit]
  have hrest : ∏ x ∈ (univ.erase u).erase v, f x ^ k (Equiv.swap u v x) =
      ∏ x ∈ (univ.erase u).erase v, f x ^ k x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv := ne_of_mem_erase hx
    have hxu := ne_of_mem_erase (mem_of_mem_erase hx)
    rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
  rw [hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]
  set R := ∏ x ∈ (univ.erase u).erase v, f x ^ k x
  have hR : 0 ≤ R := Finset.prod_nonneg fun x _ => pow_nonneg (hf x) _
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk
  rw [hm, pow_add, pow_add]
  have h1 : f v ^ m ≤ f u ^ m := pow_le_pow_left₀ (hf v) hfuv m
  have h2 : 0 ≤ f u ^ k u * f v ^ k u * R :=
    mul_nonneg (mul_nonneg (pow_nonneg (hf u) _) (pow_nonneg (hf v) _)) hR
  calc
    f u ^ k u * (f v ^ k u * f v ^ m * R) = (f u ^ k u * f v ^ k u * R) * f v ^ m := by ring
    _ ≤ (f u ^ k u * f v ^ k u * R) * f u ^ m := mul_le_mul_of_nonneg_left h1 h2
    _ = f u ^ k u * f u ^ m * (f v ^ k u * R) := by ring

/-- Word form of the exchange: swapping the labels `u` and `v` in every
position does not decrease the likelihood when `v` occurs at least as often
as `u` and has at most the mass of `u`. -/
theorem prod_word_le_prod_word_swap {n : ℕ} (f : Option A → ℝ) (hf : ∀ x, 0 ≤ f x)
    (z : OrderedWord n A) (u v : Option A) (hfuv : f v ≤ f u)
    (hk : labelCount z u ≤ labelCount z v) :
    ∏ i, f (z i) ≤ ∏ i, f (Equiv.swap u v (z i)) := by
  rw [prod_word_eq_prod_pow_labelCount f z,
    prod_word_eq_prod_pow_labelCount (fun x => f (Equiv.swap u v x)) z]
  have hre := Equiv.prod_comp (Equiv.swap u v)
    (fun x => f x ^ labelCount z (Equiv.swap u v x))
  simp only [Equiv.swap_apply_self] at hre
  rw [hre]
  exact prod_pow_le_prod_pow_swap f hf (labelCount z) u v hfuv hk

end Pairing

/-! ### Symmetrized joint weights -/

section Symmetrization

variable {A : Type*} [Fintype A]

/-- Likelihood of an ordered word in the relabelled state `ρ`: the observed
label `x` carries the original mass of `ρ x` (abstention is fixed). -/
noncomputable def stateLikelihood (π : Law (Option A)) (ρ : Equiv.Perm A) {n : ℕ}
    (z : OrderedWord n A) : ℝ :=
  ∏ i, π.mass (Equiv.optionCongr ρ (z i))

/-- Unnormalized joint weight of the word `z` and candidate `d`: the sum of
state likelihoods over the states designating `d` correct (`ρ d = c`).  It is
`M!` times Doc B's `W_N(z,d)`. -/
noncomputable def jointWeight [DecidableEq A] (π : Law (Option A)) (c : A) {n : ℕ}
    (z : OrderedWord n A) (d : A) : ℝ :=
  ∑ ρ : Equiv.Perm A, if ρ d = c then stateLikelihood π ρ z else 0

/-- The plurality winner, and the correct label `c` on the all-abstention word. -/
noncomputable def winnerOr (c : A) {n : ℕ} (z : OrderedWord n A) : A :=
  (plurality z).getD c

/-- The number of permutations fixing `c` (as a real), `(M-1)!`. -/
noncomputable def fixCount [DecidableEq A] (c : A) : ℝ :=
  ∑ ρ : Equiv.Perm A, if ρ c = c then (1 : ℝ) else 0

theorem stateLikelihood_nonneg (π : Law (Option A)) (ρ : Equiv.Perm A) {n : ℕ}
    (z : OrderedWord n A) : 0 ≤ stateLikelihood π ρ z :=
  Finset.prod_nonneg fun _ _ => π.nonneg _

/-- Swap pairing (Doc B): if `count_d(z) ≤ count_e(z)` and `c` is a weak mode,
then `W(z,d) ≤ W(z,e)`.  The bijection `ρ ↦ ρ * swap d e` pairs the states
designating `e` correct with those designating `d` correct. -/
theorem jointWeight_le_of_labelCount_le [DecidableEq A] (π : Law (Option A)) (c : A)
    (hmode : ∀ b : A, π.mass (some b) ≤ π.mass (some c)) {n : ℕ}
    (z : OrderedWord n A) (d e : A)
    (hde : labelCount z (some d) ≤ labelCount z (some e)) :
    jointWeight π c z d ≤ jointWeight π c z e := by
  unfold jointWeight
  rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap d e))
    (fun ρ => if ρ e = c then stateLikelihood π ρ z else 0)]
  apply Finset.sum_le_sum
  intro ρ _
  simp only [Equiv.coe_mulRight, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.swap_apply_right]
  split_ifs with h
  · unfold stateLikelihood
    have hsw : ∀ x : Option A, Equiv.optionCongr (ρ * Equiv.swap d e) x =
        Equiv.optionCongr ρ (Equiv.swap (some d) (some e) x) := by
      intro x
      rw [← Equiv.optionCongr_swap, Equiv.optionCongr_apply, Equiv.optionCongr_apply,
        Equiv.optionCongr_apply, Option.map_map, Equiv.Perm.coe_mul]
    simp only [hsw]
    apply prod_word_le_prod_word_swap (fun x => π.mass (Equiv.optionCongr ρ x))
      (fun x => π.nonneg _) z (some d) (some e)
    · simp only [Equiv.optionCongr_apply, Option.map_some, h]
      exact hmode (ρ e)
    · exact hde
  · exact le_rfl

theorem stateLikelihood_cons (π : Law (Option A)) (ρ : Equiv.Perm A) {n : ℕ}
    (a : Option A) (z : OrderedWord n A) :
    stateLikelihood π ρ (Fin.cons a z : OrderedWord (n + 1) A) =
      π.mass (Equiv.optionCongr ρ a) * stateLikelihood π ρ z := by
  unfold stateLikelihood
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem sum_mass_relabel (π : Law (Option A)) (ρ : Equiv.Perm A) :
    ∑ a, π.mass (Equiv.optionCongr ρ a) = 1 := by
  rw [Equiv.sum_comp (Equiv.optionCongr ρ) π.mass, π.total]

/-- The product law: `W_N(z,d) = Σ_a W_{N+1}(a·z, d)` (the new voter is
prepended; any fixed position would do). -/
theorem jointWeight_eq_sum_cons [DecidableEq A] (π : Law (Option A)) (c : A) {n : ℕ}
    (z : OrderedWord n A) (d : A) :
    jointWeight π c z d =
      ∑ a : Option A, jointWeight π c (Fin.cons a z : OrderedWord (n + 1) A) d := by
  unfold jointWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ _
  simp only [stateLikelihood_cons]
  by_cases h : ρ d = c
  · simp only [h, if_true]
    rw [← Finset.sum_mul, sum_mass_relabel, one_mul]
  · simp [h]

theorem sum_word_succ {n : ℕ} (F : OrderedWord (n + 1) A → ℝ) :
    ∑ y, F y = ∑ z : OrderedWord n A, ∑ a : Option A, F (Fin.cons a z) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Option A)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

omit [Fintype A] in
/-- The chosen label has maximal readable count; on the all-abstention word
every readable count is zero. -/
theorem labelCount_le_winnerOr (c : A) {n : ℕ} (z : OrderedWord n A) (d : A) :
    labelCount z (some d) ≤ labelCount z (some (winnerOr c z)) := by
  unfold winnerOr
  cases h : plurality z with
  | none =>
    have hall := (plurality_eq_none_iff z).1 h
    have h0 : labelCount z (some d) = 0 := by
      unfold labelCount
      simp [hall]
    simp [h0]
  | some a =>
    simpa only [Option.getD_some] using plurality_dominates_readable z a h d

/-- First-appearance plurality (with `c` on the all-abstention word) attains
`max_d W_N(z,d)` on every word. -/
theorem jointWeight_le_winnerOr [DecidableEq A] (π : Law (Option A)) (c : A)
    (hmode : ∀ b : A, π.mass (some b) ≤ π.mass (some c)) {n : ℕ}
    (z : OrderedWord n A) (d : A) :
    jointWeight π c z d ≤ jointWeight π c z (winnerOr c z) :=
  jointWeight_le_of_labelCount_le π c hmode z d _ (labelCount_le_winnerOr c z d)

theorem sum_perm_apply_eq [DecidableEq A] (c d : A) :
    (∑ ρ : Equiv.Perm A, if ρ d = c then (1 : ℝ) else 0) = fixCount c := by
  unfold fixCount
  rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap c d))
    (fun ρ : Equiv.Perm A => if ρ d = c then (1 : ℝ) else 0)]
  simp only [Equiv.coe_mulRight, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.swap_apply_right]

/-- `M · (M-1)! = M!`, by double counting the pairs `(ρ, d)` with `ρ d = c`. -/
theorem card_mul_fixCount [DecidableEq A] (c : A) :
    (Fintype.card A : ℝ) * fixCount c = (Fintype.card (Equiv.Perm A) : ℝ) := by
  have h1 : ∑ d : A, (∑ ρ : Equiv.Perm A, if ρ d = c then (1 : ℝ) else 0) =
      (Fintype.card A : ℝ) * fixCount c := by
    simp only [sum_perm_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← h1, Finset.sum_comm]
  have h2 : ∀ ρ : Equiv.Perm A, (∑ d : A, if ρ d = c then (1 : ℝ) else 0) = 1 := by
    intro ρ
    simp [Equiv.apply_eq_iff_eq_symm_apply]
  simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem fixCount_pos [DecidableEq A] (c : A) : 0 < fixCount c := by
  have hcount := card_mul_fixCount c
  have hM : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨c⟩
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm A) := by
    exact_mod_cast Fintype.card_pos
  by_contra h
  push_neg at h
  nlinarith

/-- On the all-abstention word every candidate has the same weight
`(M-1)! u^n`, i.e. normalized mass `u^n / M`. -/
theorem jointWeight_allAbstain [DecidableEq A] (π : Law (Option A)) (c : A) (n : ℕ)
    (d : A) :
    jointWeight π c (fun _ : Fin n => (none : Option A)) d =
      fixCount c * π.mass none ^ n := by
  unfold jointWeight stateLikelihood
  simp only [Equiv.optionCongr_apply, Option.map_none, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← sum_perm_apply_eq c d, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ρ _
  split_ifs <;> simp

theorem prob_plurality_none (π : Law (Option A)) (n : ℕ) :
    (iidWordLaw π n).prob (fun y => plurality y = none) = π.mass none ^ n := by
  classical
  have he : (fun y : OrderedWord n A => plurality y = none) =
      (fun y => ∀ i, y i = none) := by
    funext y
    exact propext (plurality_eq_none_iff y)
  rw [he, iidWordLaw, prob_pi_forall (fun _ : Fin n => π) (fun _ x => x = none)]
  have hs : π.prob (fun x => x = none) = π.mass none := by
    unfold Law.prob
    rw [Finset.sum_eq_single none]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  simp [hs]

/-- Label equivariance: in every relabelled state `ρ`, first-appearance
plurality names the designated correct label `ρ⁻¹ c` with probability `V_n`. -/
theorem stateAccuracy_eq_voteAccuracy [DecidableEq A] (π : Law (Option A)) (c : A)
    (ρ : Equiv.Perm A) (n : ℕ) :
    ∑ z : OrderedWord n A,
        (if plurality z = some (ρ.symm c) then stateLikelihood π ρ z else 0) =
      voteAccuracy π n c := by
  let e : OrderedWord n A ≃ OrderedWord n A :=
    Equiv.piCongrRight (fun _ : Fin n => Equiv.optionCongr ρ)
  let G : OrderedWord n A → ℝ := fun y =>
    if plurality y = some c then (iidWordLaw π n).mass y else 0
  have hpt : ∀ z : OrderedWord n A,
      (if plurality z = some (ρ.symm c) then stateLikelihood π ρ z else 0) = G (e z) := by
    intro z
    have hpl : plurality (e z) = Equiv.optionCongr ρ (plurality z) :=
      plurality_relabel z (Equiv.optionCongr ρ) rfl
    have hw : (iidWordLaw π n).mass (e z) = stateLikelihood π ρ z := rfl
    have hiff : plurality z = some (ρ.symm c) ↔
        Equiv.optionCongr ρ (plurality z) = some c := by
      rw [Equiv.optionCongr_apply]
      cases plurality z with
      | none => simp
      | some a => simp [Equiv.eq_symm_apply]
    simp only [G, hpl, hw]
    exact if_congr hiff rfl rfl
  rw [Finset.sum_congr rfl (fun z _ => hpt z), Equiv.sum_comp e G]
  unfold voteAccuracy Law.prob correctVote
  apply Finset.sum_congr rfl
  intro y _
  show (if plurality y = some c then (iidWordLaw π n).mass y else 0) = _
  congr

/-- `J_n` in unnormalized form:
`Σ_z W(z, winner z) = M! · V_n + (M-1)! · u^n`. -/
theorem sum_jointWeight_winnerOr [DecidableEq A] (π : Law (Option A)) (c : A) (n : ℕ) :
    ∑ z : OrderedWord n A, jointWeight π c z (winnerOr c z) =
      (Fintype.card (Equiv.Perm A) : ℝ) * voteAccuracy π n c +
        fixCount c * π.mass none ^ n := by
  unfold jointWeight
  rw [Finset.sum_comm]
  have hρ : ∀ ρ : Equiv.Perm A, (∑ z : OrderedWord n A,
      (if ρ (winnerOr c z) = c then stateLikelihood π ρ z else 0)) =
      voteAccuracy π n c + (if ρ c = c then (1 : ℝ) else 0) * π.mass none ^ n := by
    intro ρ
    let e : OrderedWord n A ≃ OrderedWord n A :=
      Equiv.piCongrRight (fun _ : Fin n => Equiv.optionCongr ρ)
    let w : OrderedWord n A → ℝ := (iidWordLaw π n).mass
    let G : OrderedWord n A → ℝ := fun y =>
      (if plurality y = some c then w y else 0) +
        (if ρ c = c then (if plurality y = none then w y else 0) else 0)
    have hpt : ∀ z : OrderedWord n A,
        (if ρ (winnerOr c z) = c then stateLikelihood π ρ z else 0) = G (e z) := by
      intro z
      have hpl : plurality (e z) = Equiv.optionCongr ρ (plurality z) :=
        plurality_relabel z (Equiv.optionCongr ρ) rfl
      have hw : w (e z) = stateLikelihood π ρ z := rfl
      by_cases hp : plurality z = none
      · rw [hp] at hpl
        simp only [G, hpl, hw, winnerOr, hp]
        simp
      · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hp
        rw [ha] at hpl
        simp only [G, hpl, hw, winnerOr, ha]
        simp
    rw [Finset.sum_congr rfl (fun z _ => hpt z), Equiv.sum_comp e G]
    simp only [G, Finset.sum_add_distrib]
    have hV : (∑ y : OrderedWord n A, if plurality y = some c then w y else 0) =
        voteAccuracy π n c := by
      unfold voteAccuracy Law.prob correctVote
      apply Finset.sum_congr rfl
      intro y _
      congr
    have hU : (∑ y : OrderedWord n A, if plurality y = none then w y else 0) =
        π.mass none ^ n := by
      rw [← prob_plurality_none π n]
      unfold Law.prob
      apply Finset.sum_congr rfl
      intro y _
      congr
    rw [hV]
    by_cases hc : ρ c = c
    · simp only [hc, if_true, one_mul, hU]
    · simp [hc]
  rw [Finset.sum_congr rfl (fun ρ _ => hρ ρ), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, fixCount, Finset.sum_mul]

/-- Doc B's identity `J_N = Σ_z max_d W_N(z,d) = V_N + u^N / M`, with the
`1/M!` normalization restored. -/
theorem normalized_J_eq [DecidableEq A] (π : Law (Option A)) (c : A) (n : ℕ) :
    (∑ z : OrderedWord n A, jointWeight π c z (winnerOr c z)) /
        (Fintype.card (Equiv.Perm A) : ℝ) =
      voteAccuracy π n c + π.mass none ^ n / (Fintype.card A : ℝ) := by
  rw [sum_jointWeight_winnerOr, ← card_mul_fixCount c]
  have hM : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨c⟩
  have hK := fixCount_pos c
  field_simp

/-- `J_N ≤ J_{N+1}`: max of a sum is at most the sum of maxima. -/
theorem sum_jointWeight_winnerOr_mono [DecidableEq A] (π : Law (Option A)) (c : A)
    (hmode : ∀ b : A, π.mass (some b) ≤ π.mass (some c)) (N : ℕ) :
    ∑ z : OrderedWord N A, jointWeight π c z (winnerOr c z) ≤
      ∑ y : OrderedWord (N + 1) A, jointWeight π c y (winnerOr c y) := by
  rw [sum_word_succ]
  apply Finset.sum_le_sum
  intro z _
  rw [jointWeight_eq_sum_cons π c z (winnerOr c z)]
  apply Finset.sum_le_sum
  intro a _
  exact jointWeight_le_winnerOr π c hmode _ _

end Symmetrization

/-! ### Doc B Theorem A3.4 -/

/-- **Doc B Theorem A3.4 (finite monotonicity for a correct mode).**  If the
correct readable label `c` is a weak sampling mode (ties allowed), then for
every `N ≥ 0`, with `u = π.mass none` and `M = |A|`,
`V_{N+1} - V_N ≥ u^N (1-u) / M`. -/
theorem voteAccuracy_succ_sub_ge {A : Type*} [Fintype A]
    (π : Law (Option A)) (c : A)
    (hmode : ∀ b : A, π.mass (some c) ≥ π.mass (some b)) (N : ℕ) :
    voteAccuracy π (N + 1) c - voteAccuracy π N c ≥
      π.mass none ^ N * (1 - π.mass none) / (Fintype.card A : ℝ) := by
  classical
  have hJ := sum_jointWeight_winnerOr_mono π c hmode N
  rw [sum_jointWeight_winnerOr, sum_jointWeight_winnerOr] at hJ
  have hcount := card_mul_fixCount c
  have hM : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨c⟩
  have hK := fixCount_pos c
  rw [ge_iff_le, div_le_iff₀ hM]
  rw [← hcount, pow_succ] at hJ
  have key : fixCount c * (π.mass none ^ N * (1 - π.mass none)) ≤
      fixCount c * ((voteAccuracy π (N + 1) c - voteAccuracy π N c) *
        (Fintype.card A : ℝ)) := by
    nlinarith
  exact le_of_mul_le_mul_left key hK

/-- The lower bound in (A3.5) is nonnegative. -/
theorem modalIncrement_nonneg {A : Type*} [Fintype A] (π : Law (Option A)) (N : ℕ) :
    0 ≤ π.mass none ^ N * (1 - π.mass none) / (Fintype.card A : ℝ) := by
  have hu0 : 0 ≤ π.mass none := π.nonneg none
  have hu1 : π.mass none ≤ 1 := by
    have h := Finset.single_le_sum (f := π.mass) (fun x _ => π.nonneg x)
      (Finset.mem_univ none)
    rwa [π.total] at h
  exact div_nonneg (mul_nonneg (pow_nonneg hu0 N) (sub_nonneg.2 hu1)) (Nat.cast_nonneg _)

/-- Accuracy of a correct weak mode is nondecreasing from one voter count to
the next. -/
theorem voteAccuracy_le_succ {A : Type*} [Fintype A]
    (π : Law (Option A)) (c : A)
    (hmode : ∀ b : A, π.mass (some c) ≥ π.mass (some b)) (N : ℕ) :
    voteAccuracy π N c ≤ voteAccuracy π (N + 1) c := by
  have h := voteAccuracy_succ_sub_ge π c hmode N
  have h0 := modalIncrement_nonneg π N
  linarith

/-- Accuracy of a correct weak mode is monotone in the number of voters. -/
theorem voteAccuracy_monotone {A : Type*} [Fintype A]
    (π : Law (Option A)) (c : A)
    (hmode : ∀ b : A, π.mass (some c) ≥ π.mass (some b)) :
    Monotone (fun N => voteAccuracy π N c) :=
  monotone_nat_of_le_succ (voteAccuracy_le_succ π c hmode)

/-- Sharpness: with a single readable label (`A = {c}`) the bound (A3.5)
holds with equality. -/
theorem voteAccuracy_succ_sub_eq_of_subsingleton {A : Type*} [Fintype A] [Subsingleton A]
    (π : Law (Option A)) (c : A) (N : ℕ) :
    voteAccuracy π (N + 1) c - voteAccuracy π N c =
      π.mass none ^ N * (1 - π.mass none) / (Fintype.card A : ℝ) := by
  have hcard : Fintype.card A = 1 :=
    Fintype.card_eq_one_iff.2 ⟨c, fun a => Subsingleton.elim a c⟩
  have htot : π.mass none + π.mass (some c) = 1 := by
    have h := π.total
    rw [Fintype.sum_option, Fintype.sum_subsingleton _ c] at h
    exact h
  have hu : 1 - π.mass (some c) = π.mass none := by linarith
  rw [sole_readable_accuracy π c (N + 1), sole_readable_accuracy π c N, hu, hcard]
  simp only [Nat.cast_one, div_one, pow_succ]
  ring

end SEKernel.Closeout.ModalMonotonicity

#print axioms SEKernel.Closeout.ModalMonotonicity.voteAccuracy_succ_sub_ge
#print axioms SEKernel.Closeout.ModalMonotonicity.voteAccuracy_le_succ
#print axioms SEKernel.Closeout.ModalMonotonicity.voteAccuracy_monotone
#print axioms SEKernel.Closeout.ModalMonotonicity.voteAccuracy_succ_sub_eq_of_subsingleton
#print axioms SEKernel.Closeout.ModalMonotonicity.modalIncrement_nonneg
#print axioms SEKernel.Closeout.ModalMonotonicity.jointWeight_le_of_labelCount_le
#print axioms SEKernel.Closeout.ModalMonotonicity.jointWeight_le_winnerOr
#print axioms SEKernel.Closeout.ModalMonotonicity.jointWeight_eq_sum_cons
#print axioms SEKernel.Closeout.ModalMonotonicity.jointWeight_allAbstain
#print axioms SEKernel.Closeout.ModalMonotonicity.stateAccuracy_eq_voteAccuracy
#print axioms SEKernel.Closeout.ModalMonotonicity.sum_jointWeight_winnerOr
#print axioms SEKernel.Closeout.ModalMonotonicity.normalized_J_eq
#print axioms SEKernel.Closeout.ModalMonotonicity.sum_jointWeight_winnerOr_mono
#print axioms SEKernel.Closeout.ModalMonotonicity.card_mul_fixCount
#print axioms SEKernel.Closeout.ModalMonotonicity.prod_pow_le_prod_pow_swap
