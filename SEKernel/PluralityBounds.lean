/-
Finite algebraic bounds for the actual ordered plurality experiment.
Doc B A3.2--A3.3.  No analytic concentration theorem is assumed.
The sample size convention is N ≥ 0; readable probabilities are explicit.
-/
import SEKernel.FiniteProbability
import SEKernel.FirstAppearancePlurality

namespace SEKernel.Epistemic

open Finset FiniteProbability
open scoped Classical

/-- The rational geometric coefficient for a higher and lower answer mass. -/
noncomputable def countTailCoefficient (higher lower : ℝ) : ℝ :=
  (higher - lower)^2 / (2*(higher+lower))

/-- Bernoulli's finite rational replacement for the geometric tail. -/
theorem geometric_mul_affine_le_one {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1)
    (N : ℕ) : (1-a)^N * (1+(N:ℝ)*a) ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp : 0 ≤ (1-a)^N := pow_nonneg (sub_nonneg.mpr ha') _
    have hstep : (1-a)*(1+((N+1:ℕ):ℝ)*a) ≤ 1+(N:ℝ)*a := by
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (N:ℝ)+1 by positivity) (sq_nonneg a)]
    calc
      (1-a)^(N+1)*(1+((N+1:ℕ):ℝ)*a) =
          (1-a)^N * ((1-a)*(1+((N+1:ℕ):ℝ)*a)) := by rw [pow_succ]; ring
      _ ≤ (1-a)^N * (1+(N:ℝ)*a) := mul_le_mul_of_nonneg_left hstep hp
      _ ≤ 1 := ih

theorem geometric_le_rational {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1)
    (N : ℕ) : (1-a)^N ≤ 1/(1+(N:ℝ)*a) := by
  apply (le_div_iff₀ (show 0 < 1+(N:ℝ)*a by positivity)).2
  exact geometric_mul_affine_le_one ha ha' N

theorem countTailCoefficient_bounds {higher lower : ℝ}
    (hl : 0 ≤ lower) (hgap : lower < higher) (hs : higher+lower ≤ 1) :
    0 < countTailCoefficient higher lower ∧ countTailCoefficient higher lower ≤ 1/2 := by
  have hh : 0 < higher := lt_of_le_of_lt hl hgap
  have hsum : 0 < higher+lower := by linarith
  unfold countTailCoefficient
  constructor
  · exact div_pos (sq_pos_of_pos (sub_pos.mpr hgap)) (by positivity)
  · apply (div_le_iff₀ (show 0 < 2*(higher+lower) by positivity)).2
    have hm := mul_nonneg hh.le hl
    have hsq := mul_nonneg hsum.le (sub_nonneg.mpr hs)
    nlinarith

/-- A nonnegative per-draw likelihood multiplier.  Equal labels are excluded
at its use: lower and higher denote two different actual readable labels. -/
noncomputable def countTilt {A : Type*} (lower higher : A) (r : ℝ)
    (a : Option A) : ℝ := by
  classical
  exact if a = some lower then r else if a = some higher then r⁻¹ else 1

theorem countTilt_nonneg {A : Type*} (lower higher : A) {r : ℝ} (hr : 0 < r)
    (a : Option A) : 0 ≤ countTilt lower higher r a := by
  classical
  unfold countTilt
  split_ifs <;> positivity

theorem countTilt_product {A : Type*} {N : ℕ} (z : OrderedWord N A)
    (lower higher : A) (hne : lower ≠ higher) (r : ℝ) :
    (∏ i, countTilt lower higher r (z i)) =
      r ^ labelCount z (some lower) * (r⁻¹) ^ labelCount z (some higher) := by
  classical
  have hp (a : Option A) : countTilt lower higher r a =
      (if a = some lower then r else 1) * (if a = some higher then r⁻¹ else 1) := by
    by_cases hl : a = some lower
    · subst a
      simp [countTilt, hne]
    · by_cases hh : a = some higher <;> simp [countTilt, hl, hh, Ne.symm hne]
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_ite, labelCount]

theorem countTilt_one_le_of_count_le {A : Type*} {N : ℕ}
    (z : OrderedWord N A) (lower higher : A) (hne : lower ≠ higher)
    {r : ℝ} (hr : 1 < r)
    (hc : labelCount z (some higher) ≤ labelCount z (some lower)) :
    1 ≤ ∏ i, countTilt lower higher r (z i) := by
  rw [countTilt_product z lower higher hne r, inv_pow, ← div_eq_mul_inv]
  exact (one_le_div (pow_pos (lt_trans zero_lt_one hr) _)).2
    (pow_le_pow_right₀ hr.le hc)

theorem expect_countTilt {A : Type*} [Fintype A]
    (π : Law (Option A)) (lower higher : A) (hne : lower ≠ higher) (r : ℝ) :
    π.expect (countTilt lower higher r) =
      π.mass (some lower)*r + π.mass (some higher)*r⁻¹ +
        1-π.mass (some higher)-π.mass (some lower) := by
  classical
  have hp : countTilt lower higher r = fun a =>
      1 + (r-1)*(if a = some lower then 1 else 0) +
        (r⁻¹-1)*(if a = some higher then 1 else 0) := by
    funext a
    by_cases hl : a = some lower
    · subst a; simp [countTilt, hne]
    · by_cases hh : a = some higher <;> simp [countTilt, hl, hh, Ne.symm hne]
  have hi (a : Option A) : π.expect (fun b => if b=a then 1 else 0) = π.mass a := by
    simp [Law.expect, Law1.mean, mul_ite]
  rw [hp, π.expect_add, π.expect_add, π.expect_const,
    π.expect_const_mul, π.expect_const_mul, hi, hi]
  ring

/-- The exact one-draw moment at the rational tilt; this is arithmetic,
not an assumed Chernoff or Hoeffding bound. -/
theorem rational_tilt_moment {higher lower : ℝ} (hs : higher+lower ≠ 0)
    (hh : higher ≠ 0) :
    lower*(2*higher/(higher+lower)) + higher*(2*higher/(higher+lower))⁻¹ +
      1-higher-lower = 1-countTailCoefficient higher lower := by
  unfold countTailCoefficient
  field_simp
  <;> ring

/-- Doc B A3.2 on the actual ordered IID word law. -/
theorem iid_count_geometric_bound {A : Type*} [Fintype A]
    (π : Law (Option A)) (lower higher : A) (hne : lower ≠ higher)
    (hgap : π.mass (some lower) < π.mass (some higher)) (N : ℕ) :
    (iidWordLaw π N).prob (fun z => labelCount z (some higher) ≤
      labelCount z (some lower)) ≤
      (1-countTailCoefficient (π.mass (some higher)) (π.mass (some lower)))^N := by
  classical
  let h := π.mass (some higher)
  let l := π.mass (some lower)
  let r := 2*h/(h+l)
  have hl : 0 ≤ l := π.nonneg _
  have hh : 0 < h := lt_of_le_of_lt hl hgap
  have hs : 0 < h+l := by linarith
  have hr : 1 < r := by dsimp [r]; apply (lt_div_iff₀ hs).2; linarith
  have hm : (iidWordLaw π N).expect (fun z => ∏ i, countTilt lower higher r (z i)) =
      (1-countTailCoefficient h l)^N := by
    unfold iidWordLaw
    rw [Law.expect_pi_prod]
    simp_rw [expect_countTilt π lower higher hne r]
    have he : l*r+h*r⁻¹+1-h-l = 1-countTailCoefficient h l :=
      rational_tilt_moment (ne_of_gt hs) (ne_of_gt hh)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simpa only [h, l] using congrArg (fun x : ℝ => x^N) he
  calc
    _ ≤ (iidWordLaw π N).expect (fun z => ∏ i, countTilt lower higher r (z i)) :=
      (iidWordLaw π N).prob_le_expect _
        (fun z => Finset.prod_nonneg fun i _ => countTilt_nonneg lower higher
          (lt_trans zero_lt_one hr) (z i))
        (fun z hz => countTilt_one_le_of_count_le z lower higher hne hr hz)
    _ = _ := hm

/-- The finite rational tail includes N=0 without an asymptotic theorem. -/
theorem iid_count_rational_bound {A : Type*} [Fintype A]
    (π : Law (Option A)) (lower higher : A) (hne : lower ≠ higher)
    (hgap : π.mass (some lower) < π.mass (some higher)) (N : ℕ) :
    (iidWordLaw π N).prob (fun z => labelCount z (some higher) ≤
      labelCount z (some lower)) ≤
      1/(1+(N:ℝ)*countTailCoefficient (π.mass (some higher)) (π.mass (some lower))) := by
  classical
  have hp : π.mass (some higher)+π.mass (some lower) ≤ 1 := by
    have ht := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({some higher, some lower} : Finset (Option A)) ⊆ Finset.univ by simp)
      (fun a _ _ => π.nonneg a)
    simpa [Ne.symm hne, π.total, add_comm] using ht
  have hc := countTailCoefficient_bounds (π.nonneg (some lower)) hgap hp
  exact (iid_count_geometric_bound π lower higher hne hgap N).trans
    (geometric_le_rational hc.1.le (by linarith) N)

/-- A readable winner dominates every readable label, even an absent label. -/
theorem readable_winner_dominates {A : Type*} {N : ℕ} (z : OrderedWord N A)
    (winner other : A) (hw : plurality z = some winner) :
    labelCount z (some other) ≤ labelCount z (some winner) := by
  classical
  by_cases hz : labelCount z (some other) = 0
  · simp [hz]
  · have hp : 0 < (Finset.univ.filter fun i => z i = some other).card :=
      Nat.pos_of_ne_zero hz
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
    have he := (Finset.mem_filter.mp hi).2
    simpa [he] using plurality_maximal_count z winner hw i (by simp [he])

/-- Wrong larger mode: the actual plurality success probability has the
geometric upper bound, with no assumption about conditional tie fairness. -/
theorem wrong_mode_geometric_bound {A : Type*} [Fintype A]
    (π : Law (Option A)) (correct wrong : A) (hne : correct ≠ wrong)
    (hgap : π.mass (some correct) < π.mass (some wrong)) (N : ℕ) :
    voteAccuracy π N correct ≤
      (1-countTailCoefficient (π.mass (some wrong)) (π.mass (some correct)))^N := by
  calc
    _ ≤ (iidWordLaw π N).prob (fun z => labelCount z (some wrong) ≤
        labelCount z (some correct)) :=
      (iidWordLaw π N).prob_mono (fun z hz => readable_winner_dominates z correct wrong hz)
    _ ≤ _ := iid_count_geometric_bound π correct wrong hne hgap N

theorem wrong_mode_rational_bound {A : Type*} [Fintype A]
    (π : Law (Option A)) (correct wrong : A) (hne : correct ≠ wrong)
    (hgap : π.mass (some correct) < π.mass (some wrong)) (N : ℕ) :
    voteAccuracy π N correct ≤
      1/(1+(N:ℝ)*countTailCoefficient (π.mass (some wrong)) (π.mass (some correct))) := by
  calc
    _ ≤ (iidWordLaw π N).prob (fun z => labelCount z (some wrong) ≤
        labelCount z (some correct)) :=
      (iidWordLaw π N).prob_mono (fun z hz => readable_winner_dominates z correct wrong hz)
    _ ≤ _ := iid_count_rational_bound π correct wrong hne hgap N

/-- A failed vote has a wrong label with at least the correct count.  The
nonempty wrong-label hypothesis handles the all-abstention and N=0 cases. -/
theorem failed_vote_count_witness {A : Type*} {N : ℕ} (z : OrderedWord N A)
    (correct : A) (hex : ∃ b : A, b ≠ correct) (hv : ¬ correctVote z correct) :
    ∃ b : {a : A // a ≠ correct}, labelCount z (some correct) ≤ labelCount z (some b.val) := by
  classical
  cases he : plurality z with
  | none =>
    obtain ⟨b, hb⟩ := hex
    refine ⟨⟨b,hb⟩, ?_⟩
    have hall := (plurality_eq_none_iff z).1 he
    simp [labelCount, hall]
  | some b =>
    have hb : b ≠ correct := by
      intro hb
      subst b
      exact hv he
    exact ⟨⟨b,hb⟩, readable_winner_dominates z b correct he⟩

/-- Doc B A3.3: the finite strict-correct-mode union bound.  Correct mass
positivity is explicit, and at least one wrong readable label is required. -/
theorem correct_mode_geometric_bound {A : Type*} [Fintype A]
    (π : Law (Option A)) (correct : A) (hex : ∃ b : A, b ≠ correct)
    (hp : 0 < π.mass (some correct))
    (hgap : ∀ b : {a : A // a ≠ correct}, π.mass (some b.val) < π.mass (some correct))
    (N : ℕ) :
    1-voteAccuracy π N correct ≤
      ∑ b : {a : A // a ≠ correct},
        (1-countTailCoefficient (π.mass (some correct)) (π.mass (some b.val)))^N := by
  classical
  unfold voteAccuracy
  rw [← (iidWordLaw π N).prob_compl]
  calc
    _ ≤ (iidWordLaw π N).prob (fun z => ∃ b : {a : A // a ≠ correct},
        labelCount z (some correct) ≤ labelCount z (some b.val)) :=
      (iidWordLaw π N).prob_mono (fun z hz => failed_vote_count_witness z correct hex hz)
    _ ≤ ∑ b : {a : A // a ≠ correct},
        (iidWordLaw π N).prob (fun z => labelCount z (some correct) ≤
          labelCount z (some b.val)) := (iidWordLaw π N).prob_exists_le _
    _ ≤ _ := Finset.sum_le_sum fun b _ => iid_count_geometric_bound π b.val correct b.property (hgap b) N

/-- A usable rational strict-mode bound without selecting an implicit minimum. -/
theorem correct_mode_rational_bound {A : Type*} [Fintype A]
    (π : Law (Option A)) (correct : A) (hex : ∃ b : A, b ≠ correct)
    (hp : 0 < π.mass (some correct))
    (hgap : ∀ b : {a : A // a ≠ correct}, π.mass (some b.val) < π.mass (some correct))
    (N : ℕ) :
    1-voteAccuracy π N correct ≤
      ∑ b : {a : A // a ≠ correct},
        1/(1+(N:ℝ)*countTailCoefficient (π.mass (some correct)) (π.mass (some b.val))) := by
  classical
  unfold voteAccuracy
  rw [← (iidWordLaw π N).prob_compl]
  calc
    _ ≤ (iidWordLaw π N).prob (fun z => ∃ b : {a : A // a ≠ correct},
        labelCount z (some correct) ≤ labelCount z (some b.val)) :=
      (iidWordLaw π N).prob_mono (fun z hz => failed_vote_count_witness z correct hex hz)
    _ ≤ ∑ b : {a : A // a ≠ correct},
        (iidWordLaw π N).prob (fun z => labelCount z (some correct) ≤
          labelCount z (some b.val)) := (iidWordLaw π N).prob_exists_le _
    _ ≤ _ := Finset.sum_le_sum fun b _ => iid_count_rational_bound π b.val correct b.property (hgap b) N

/-- The one-readable-label edge case is reach, not a vacuous strict-mode
argument.  Any subsequent convergence claim still needs positive mass. -/
theorem sole_readable_accuracy {A : Type*} [Fintype A] [Subsingleton A]
    (π : Law (Option A)) (correct : A) (N : ℕ) :
    voteAccuracy π N correct = 1-(1-π.mass (some correct))^N := by
  have he : (fun z : OrderedWord N A => correctVote z correct) =
      (fun z => reaches z N correct) := by
    funext z
    apply propext
    constructor
    · exact correctVote_reaches_full z correct
    · rintro ⟨i, hi, hz⟩
      cases hw : plurality z with
      | none =>
        have hall := (plurality_eq_none_iff z).1 hw
        have hbad := hall i
        rw [hz] at hbad
        contradiction
      | some a =>
        unfold correctVote
        simpa only [Subsingleton.elim a correct] using hw
  unfold voteAccuracy
  rw [he]
  exact reach_full_probability π N correct

/-- The common-coefficient form records an explicit positive lower bound
on all gaps; it does not silently invert a zero correct-answer mass. -/
theorem correct_mode_common_rational_bound {A : Type*} [Fintype A]
    (π : Law (Option A)) (correct : A) (hex : ∃ b : A, b ≠ correct)
    (hp : 0 < π.mass (some correct))
    (hgap : ∀ b : {a : A // a ≠ correct}, π.mass (some b.val) < π.mass (some correct))
    (a0 : ℝ) (ha0 : 0 < a0)
    (hmin : ∀ b : {a : A // a ≠ correct}, a0 ≤
      countTailCoefficient (π.mass (some correct)) (π.mass (some b.val))) (N : ℕ) :
    1-voteAccuracy π N correct ≤
      (Fintype.card {a : A // a ≠ correct} : ℝ)/(1+(N:ℝ)*a0) := by
  calc
    _ ≤ ∑ b : {a : A // a ≠ correct},
        1/(1+(N:ℝ)*countTailCoefficient (π.mass (some correct)) (π.mass (some b.val))) :=
      correct_mode_rational_bound π correct hex hp hgap N
    _ ≤ ∑ _b : {a : A // a ≠ correct}, 1/(1+(N:ℝ)*a0) := by
      apply Finset.sum_le_sum
      intro b _
      apply one_div_le_one_div_of_le (by positivity)
      exact add_le_add_right (mul_le_mul_of_nonneg_left (hmin b) (by positivity)) 1
    _ = _ := by simp [div_eq_mul_inv]

/-- Explicit finite strict-mode sample cutoff. -/
theorem correct_mode_cutoff {A : Type*} [Fintype A]
    (π : Law (Option A)) (correct : A) (hex : ∃ b : A, b ≠ correct)
    (hp : 0 < π.mass (some correct))
    (hgap : ∀ b : {a : A // a ≠ correct}, π.mass (some b.val) < π.mass (some correct))
    (a0 : ℝ) (ha0 : 0 < a0)
    (hmin : ∀ b : {a : A // a ≠ correct}, a0 ≤
      countTailCoefficient (π.mass (some correct)) (π.mass (some b.val)))
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : (Fintype.card {a : A // a ≠ correct} : ℝ)/(a0*ε) ≤ N) :
    1-ε ≤ voteAccuracy π N correct := by
  have hb := correct_mode_common_rational_bound π correct hex hp hgap a0 ha0 hmin N
  have hn := (div_le_iff₀ (mul_pos ha0 hε)).1 hN
  have hden : 0 < 1+(N:ℝ)*a0 := by positivity
  have hsmall : (Fintype.card {a : A // a ≠ correct} : ℝ)/(1+(N:ℝ)*a0) ≤ ε := by
    apply (div_le_iff₀ hden).2
    nlinarith
  linarith

end SEKernel.Epistemic
