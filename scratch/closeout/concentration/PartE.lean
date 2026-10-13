import SEKernel.PluralityCountFormula

namespace SEKernel.Closeout.Concentration

open Finset SEKernel.FiniteProbability SEKernel.Epistemic

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

end SizeCounterexample

end SEKernel.Closeout.Concentration
