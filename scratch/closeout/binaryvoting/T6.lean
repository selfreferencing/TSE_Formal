import SEKernel.PluralityCountFormula
import SEKernel.EpistemicPayoff

namespace SEKernel.Closeout.BinaryVoting

open Finset
open scoped Nat
open SEKernel.FiniteProbability
open SEKernel.Epistemic

/-- Count profile with readable counts `x, y, z` on labels `0, 1, 2` and no abstention. -/
def prof3 (x y z : ℕ) : Option (Fin 3) → ℕ
  | none => 0
  | some i => ![x, y, z] i

/-- First-appearance tie weight of label `0` on the readable count vector `(x, y, z)`. -/
noncomputable def tieWeight3 (x y z : ℕ) : ℝ :=
  if 0 < x ∧ y ≤ x ∧ z ≤ x then
    1 / (1 + (if 0 < y ∧ x ≤ y ∧ z ≤ y then 1 else 0) +
      (if 0 < z ∧ x ≤ z ∧ y ≤ z then 1 else 0))
  else 0

theorem multinomial_prof3 (x y z : ℕ) :
    Nat.multinomial Finset.univ (prof3 x y z) = (x + y + z)! / (x ! * y ! * z !) := by
  rw [Nat.multinomial, Fintype.sum_option, Fintype.prod_option, Fin.sum_univ_three,
    Fin.prod_univ_three]
  simp [prof3, add_assoc, mul_assoc]

theorem mem_readableModes_prof3 (x y z : ℕ) (i : Fin 3) :
    i ∈ readableModes (prof3 x y z) ↔
      0 < ![x, y, z] i ∧ ∀ b, ![x, y, z] b ≤ ![x, y, z] i := by
  simp [readableModes, prof3]

theorem card_readableModes_prof3 (x y z : ℕ) :
    ((readableModes (prof3 x y z)).card : ℝ) =
      (if 0 < x ∧ y ≤ x ∧ z ≤ x then 1 else 0) + (if 0 < y ∧ x ≤ y ∧ z ≤ y then 1 else 0) +
        (if 0 < z ∧ x ≤ z ∧ y ≤ z then 1 else 0) := by
  classical
  have h : readableModes (prof3 x y z) =
      Finset.univ.filter (fun i : Fin 3 => 0 < ![x, y, z] i ∧ ∀ b, ![x, y, z] b ≤ ![x, y, z] i) := by
    ext i
    rw [mem_readableModes_prof3]
    simp
  rw [h, Finset.card_filter, Fin.sum_univ_three]
  push_cast
  simp [Fin.forall_fin_succ]


theorem tie_prof3 (x y z : ℕ) (inst : Decidable ((0 : Fin 3) ∈ readableModes (prof3 x y z))) :
    (if (0 : Fin 3) ∈ readableModes (prof3 x y z) then
        1 / ((readableModes (prof3 x y z)).card : ℝ) else 0) = tieWeight3 x y z := by
  rw [card_readableModes_prof3]
  unfold tieWeight3
  by_cases h : 0 < x ∧ y ≤ x ∧ z ≤ x
  · have hm : (0 : Fin 3) ∈ readableModes (prof3 x y z) := by
      rw [mem_readableModes_prof3]; simp [Fin.forall_fin_succ]; omega
    rw [if_pos hm, if_pos h, if_pos h]
  · have hm : (0 : Fin 3) ∉ readableModes (prof3 x y z) := by
      rw [mem_readableModes_prof3]; simp [Fin.forall_fin_succ]; omega
    rw [if_neg hm, if_neg h]

/-- Readable pairs `(x, y)` with `x + y ≤ N`; the third count is `N - x - y`. -/
def pairs3 (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun xy => xy.1 + xy.2 ≤ N)

theorem sum_validCountProfiles_three (N : ℕ) (F : (Option (Fin 3) → ℕ) → ℝ)
    (hF : ∀ c, c none ≠ 0 → F c = 0) :
    ∑ c ∈ validCountProfiles (Fin 3) N, F c =
      ∑ xy ∈ pairs3 N, F (prof3 xy.1 xy.2 (N - xy.1 - xy.2)) := by
  classical
  have hinj : Set.InjOn (fun xy : ℕ × ℕ => prof3 xy.1 xy.2 (N - xy.1 - xy.2))
      (pairs3 N : Set (ℕ × ℕ)) := by
    intro u _ v _ h
    have h0 := congrFun h (some 0)
    have h1 := congrFun h (some 1)
    simp [prof3] at h0 h1
    exact Prod.ext h0 h1
  rw [← Finset.sum_image hinj]
  symm
  apply Finset.sum_subset
  · intro c hc
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.1 hc
    have hle : xy.1 + xy.2 ≤ N := (Finset.mem_filter.1 hxy).2
    simp only [validCountProfiles, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
      and_true]
    rw [Fintype.sum_option, Fin.sum_univ_three]
    simp [prof3]
    omega
  · intro c hc hnot
    by_cases h0 : c none = 0
    · exfalso
      apply hnot
      have hsum : ∑ q, c q = N := by
        simpa [validCountProfiles, Finset.mem_piAntidiag] using hc
      rw [Fintype.sum_option, Fin.sum_univ_three, h0] at hsum
      refine Finset.mem_image.2 ⟨(c (some 0), c (some 1)), ?_, ?_⟩
      · simp only [pairs3, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · funext q
        cases q with
        | none => simp [prof3, h0]
        | some i =>
          fin_cases i
          · simp [prof3]
          · simp [prof3]
          · simp [prof3]; omega
    · exact hF c h0

/-- Doc B A3.1 on three readable labels with no abstention (label `0` correct). -/
theorem three_label_vote_formula (π : Law (Option (Fin 3))) (hnone : π.mass none = 0)
    (N : ℕ) :
    voteAccuracy π N 0 = ∑ xy ∈ pairs3 N,
      (((xy.1 + xy.2 + (N - xy.1 - xy.2))! / (xy.1 ! * xy.2 ! * (N - xy.1 - xy.2)!) : ℕ) : ℝ) *
        (π.mass (some 0) ^ xy.1 * π.mass (some 1) ^ xy.2 *
          π.mass (some 2) ^ (N - xy.1 - xy.2)) *
        tieWeight3 xy.1 xy.2 (N - xy.1 - xy.2) := by
  classical
  rw [plurality_multinomial_formula π 0, sum_validCountProfiles_three N]
  · apply Finset.sum_congr rfl
    intro xy _
    rw [multinomial_prof3, tie_prof3 _ _ _ _, Fintype.prod_option, Fin.prod_univ_three]
    simp [prof3, mul_assoc]
  · intro c hc
    rw [Fintype.prod_option, hnone, zero_pow hc, zero_mul]
    ring


theorem three_label_total (π : Law (Option (Fin 3))) (hnone : π.mass none = 0) :
    π.mass (some 0) + π.mass (some 1) + π.mass (some 2) = 1 := by
  have ht := π.total
  rw [Fintype.sum_option, Fin.sum_univ_three, hnone] at ht
  linarith

/-- Doc B A3.5: `V_2 = p` on three readable labels with no abstention. -/
theorem three_label_V2 (π : Law (Option (Fin 3))) (hnone : π.mass none = 0) :
    voteAccuracy π 2 0 = π.mass (some 0) := by
  have ht := three_label_total π hnone
  rw [three_label_vote_formula π hnone]
  simp [pairs3, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ, tieWeight3,
    Nat.factorial]
  norm_num
  linear_combination π.mass (some 0) * ht

/-- Doc B A3.5: `V_3 = p^3 + 3p^2(q+r) + 2pqr`. -/
theorem three_label_V3 (π : Law (Option (Fin 3))) (hnone : π.mass none = 0) :
    voteAccuracy π 3 0 = π.mass (some 0) ^ 3 +
      3 * π.mass (some 0) ^ 2 * (π.mass (some 1) + π.mass (some 2)) +
      2 * π.mass (some 0) * π.mass (some 1) * π.mass (some 2) := by
  rw [three_label_vote_formula π hnone]
  simp [pairs3, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ, tieWeight3,
    Nat.factorial]
  norm_num
  ring

/-- Doc B A3.5: `V_4 = p^4 + 4p^3(q+r) + 3p^2(q^2+r^2) + 12p^2qr`. -/
theorem three_label_V4 (π : Law (Option (Fin 3))) (hnone : π.mass none = 0) :
    voteAccuracy π 4 0 = π.mass (some 0) ^ 4 +
      4 * π.mass (some 0) ^ 3 * (π.mass (some 1) + π.mass (some 2)) +
      3 * π.mass (some 0) ^ 2 * (π.mass (some 1) ^ 2 + π.mass (some 2) ^ 2) +
      12 * π.mass (some 0) ^ 2 * π.mass (some 1) * π.mass (some 2) := by
  rw [three_label_vote_formula π hnone]
  simp [pairs3, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ, tieWeight3,
    Nat.factorial]
  norm_num
  ring


/-- Three readable labels with masses `p, q, r` on labels `0, 1, 2`; abstention mass zero. -/
noncomputable def threeLabelLaw (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hs : p + q + r = 1) : Law (Option (Fin 3)) where
  mass x := match x with
    | none => 0
    | some i => ![p, q, r] i
  nonneg x := by
    cases x with
    | none => exact le_refl 0
    | some i => fin_cases i <;> simp [hp, hq, hr]
  total := by simp [Fintype.sum_option, Fin.sum_univ_three]; linarith

/-- Doc B Counterexample A3.5: correct `3/8`, wrong `1/8`, wrong `1/2`. -/
noncomputable def nonmodalLawB : Law (Option (Fin 3)) :=
  threeLabelLaw (3/8) (1/8) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Doc A (A3.5): correct `2/5`, wrong `1/2`, wrong `1/10`. -/
noncomputable def nonmodalLawA : Law (Option (Fin 3)) :=
  threeLabelLaw (2/5) (1/2) (1/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Doc B A3.5 through the actual count formula: `V_2 = 3/8`, `V_3 = 93/256`,
`V_4 = 189/512`; accuracy falls then rises, with a wrong strict mode. -/
theorem nonmodal_B_values :
    nonmodalLawB.mass none = 0 ∧
      voteAccuracy nonmodalLawB 2 0 = 3 / 8 ∧
      voteAccuracy nonmodalLawB 3 0 = 93 / 256 ∧
      voteAccuracy nonmodalLawB 4 0 = 189 / 512 ∧
      voteAccuracy nonmodalLawB 3 0 < voteAccuracy nonmodalLawB 2 0 ∧
      voteAccuracy nonmodalLawB 3 0 < voteAccuracy nonmodalLawB 4 0 ∧
      nonmodalLawB.mass (some 0) < nonmodalLawB.mass (some 2) ∧
      nonmodalLawB.mass (some 1) < nonmodalLawB.mass (some 2) := by
  have h0 : nonmodalLawB.mass none = 0 := rfl
  have m0 : nonmodalLawB.mass (some 0) = 3 / 8 := rfl
  have m1 : nonmodalLawB.mass (some 1) = 1 / 8 := rfl
  have m2 : nonmodalLawB.mass (some 2) = 1 / 2 := rfl
  rw [three_label_V2 _ h0, three_label_V3 _ h0, three_label_V4 _ h0, m0, m1, m2]
  norm_num [h0]

/-- Doc A (A3.5) through the actual count formula: `V_2 = 2/5`, `V_3 = 49/125`,
`V_4 = 2/5`; accuracy falls then rises, with a wrong strict mode. -/
theorem nonmodal_A_values :
    nonmodalLawA.mass none = 0 ∧
      voteAccuracy nonmodalLawA 2 0 = 2 / 5 ∧
      voteAccuracy nonmodalLawA 3 0 = 49 / 125 ∧
      voteAccuracy nonmodalLawA 4 0 = 2 / 5 ∧
      voteAccuracy nonmodalLawA 3 0 < voteAccuracy nonmodalLawA 2 0 ∧
      voteAccuracy nonmodalLawA 3 0 < voteAccuracy nonmodalLawA 4 0 ∧
      nonmodalLawA.mass (some 0) < nonmodalLawA.mass (some 1) ∧
      nonmodalLawA.mass (some 2) < nonmodalLawA.mass (some 1) := by
  have h0 : nonmodalLawA.mass none = 0 := rfl
  have m0 : nonmodalLawA.mass (some 0) = 2 / 5 := rfl
  have m1 : nonmodalLawA.mass (some 1) = 1 / 2 := rfl
  have m2 : nonmodalLawA.mass (some 2) = 1 / 10 := rfl
  rw [three_label_V2 _ h0, three_label_V3 _ h0, three_label_V4 _ h0, m0, m1, m2]
  norm_num [h0]

end SEKernel.Closeout.BinaryVoting
