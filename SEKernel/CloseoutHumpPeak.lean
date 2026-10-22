/-
The exact peak of the binary ten-voter / five-posted premium.
The peak is defined by nested real square roots; all numerical bounds are rational.
-/
import SEKernel.EpistemicPayoff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace SEKernel.Closeout.HumpPeak

open SEKernel.EpistemicPayoff

theorem hump10_hasDerivAt (p : ℝ) :
    HasDerivAt hump10 ((1 - p)^4 * (5 - 630 * p^4)) p := by
  have hq := (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
  have hpoly := (((hasDerivAt_const p (5 : ℝ)).add
    ((hasDerivAt_id p).const_mul 15)).add
    (((hasDerivAt_id p).pow 2).const_mul 35)).add
    (((hasDerivAt_id p).pow 3).const_mul 70)
  convert ((hasDerivAt_id p).mul (hq.pow 5)).mul hpoly using 1
  · funext x
    exact hump_forms_equal x
  · simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
    ring

/-- The positive fourth root of `1 / 126`. -/
noncomputable def humpPeak : ℝ := Real.sqrt (Real.sqrt (1 / 126 : ℝ))

theorem humpPeak_pos : 0 < humpPeak := by
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by norm_num))

theorem humpPeak_pow_four : humpPeak^4 = (1 / 126 : ℝ) := by
  have h₁ := Real.sq_sqrt (Real.sqrt_nonneg (1 / 126 : ℝ))
  have h₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 126)
  calc humpPeak^4 = (humpPeak^2)^2 := by ring
       _ = (1 / 126 : ℝ) := by rw [humpPeak, h₁, h₂]

/-- Rational enclosure, also used to certify the peak's value. -/
theorem humpPeak_tight_bounds :
    (2984745 / 10000000 : ℝ) < humpPeak ∧ humpPeak < 2984747 / 10000000 := by
  constructor
  · by_contra h
    have hp := pow_le_pow_left₀ humpPeak_pos.le (le_of_not_gt h) 4
    rw [humpPeak_pow_four] at hp
    norm_num at hp
  · by_contra h
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2984747 / 10000000)
      (le_of_not_gt h) 4
    rw [humpPeak_pow_four] at hp
    norm_num at hp

theorem humpPeak_bounds : (29 / 100 : ℝ) < humpPeak ∧ humpPeak < 3 / 10 := by
  obtain ⟨hl, hu⟩ := humpPeak_tight_bounds
  constructor <;> linarith

theorem hump10_strictMonoOn : StrictMonoOn hump10 (Set.Icc 0 humpPeak) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun x _ => (hump10_hasDerivAt x).continuousAt.continuousWithinAt)
  intro p hp
  rw [interior_Icc] at hp
  rw [(hump10_hasDerivAt p).deriv]
  have hpow : p^4 < humpPeak^4 := pow_lt_pow_left₀ hp.2 hp.1.le (by norm_num)
  rw [humpPeak_pow_four] at hpow
  have hq : 0 < 1 - p := by linarith [hp.2, humpPeak_bounds.2]
  exact mul_pos (pow_pos hq _) (by nlinarith)

theorem hump10_strictAntiOn : StrictAntiOn hump10 (Set.Icc humpPeak 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun x _ => (hump10_hasDerivAt x).continuousAt.continuousWithinAt)
  intro p hp
  rw [interior_Icc] at hp
  rw [(hump10_hasDerivAt p).deriv]
  have hpow : humpPeak^4 < p^4 :=
    pow_lt_pow_left₀ hp.1 humpPeak_pos.le (by norm_num)
  rw [humpPeak_pow_four] at hpow
  exact mul_neg_of_pos_of_neg (pow_pos (sub_pos.mpr hp.2) _) (by nlinarith)

theorem hump10_le_peak (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    hump10 p ≤ hump10 humpPeak := by
  rcases le_total p humpPeak with h | h
  · exact hump10_strictMonoOn.monotoneOn ⟨hp, h⟩ ⟨humpPeak_pos.le, le_rfl⟩ h
  · exact hump10_strictAntiOn.antitoneOn ⟨le_rfl, by linarith [humpPeak_bounds.2]⟩
      ⟨h, hp'⟩ h

theorem hump10_eq_peak_iff (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    hump10 p = hump10 humpPeak ↔ p = humpPeak := by
  constructor
  · intro he
    rcases lt_trichotomy p humpPeak with h | h | h
    · exact False.elim ((ne_of_lt (hump10_strictMonoOn ⟨hp, h.le⟩
        ⟨humpPeak_pos.le, le_rfl⟩ h)) he)
    · exact h
    · exact False.elim ((ne_of_gt (hump10_strictAntiOn
        ⟨le_rfl, by linarith [humpPeak_bounds.2]⟩ ⟨h.le, hp'⟩ h)) he.symm)
  · rintro rfl
    rfl

theorem hump10_peak_value :
    (7331 / 10000 : ℝ) < hump10 humpPeak ∧ hump10 humpPeak < 7332 / 10000 := by
  obtain ⟨hl, hu⟩ := humpPeak_tight_bounds
  have hp := humpPeak_pos.le
  have hql : (0 : ℝ) ≤ 1 - 2984747 / 10000000 := by norm_num
  have hqu : (0 : ℝ) ≤ 1 - humpPeak := by linarith
  have hl₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2984745 / 10000000) hl.le 2
  have hl₃ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2984745 / 10000000) hl.le 3
  have hu₂ := pow_le_pow_left₀ hp hu.le 2
  have hu₃ := pow_le_pow_left₀ hp hu.le 3
  have hfl : (5 + 15*(2984745/10000000) + 35*(2984745/10000000)^2 +
      70*(2984745/10000000)^3 : ℝ) ≤ 5 + 15*humpPeak + 35*humpPeak^2 + 70*humpPeak^3 := by
    nlinarith
  have hfu : 5 + 15*humpPeak + 35*humpPeak^2 + 70*humpPeak^3 ≤
      (5 + 15*(2984747/10000000) + 35*(2984747/10000000)^2 +
      70*(2984747/10000000)^3 : ℝ) := by nlinarith
  have hprodL := mul_le_mul hl.le
    (pow_le_pow_left₀ hql (by linarith : (1 - 2984747 / 10000000 : ℝ) ≤ 1 - humpPeak) 5)
    (pow_nonneg hql 5) hp
  have hprodU := mul_le_mul hu.le
    (pow_le_pow_left₀ hqu (by linarith : 1 - humpPeak ≤ (1 - 2984745 / 10000000 : ℝ)) 5)
    (pow_nonneg hqu 5) (by norm_num : (0 : ℝ) ≤ 2984747 / 10000000)
  have hL := mul_le_mul hprodL hfl (by norm_num)
    (mul_nonneg hp (pow_nonneg hqu 5))
  have hU := mul_le_mul hprodU hfu (by positivity)
    (by norm_num : (0 : ℝ) ≤ (2984747/10000000) * (1-2984745/10000000)^5)
  rw [hump_forms_equal]
  unfold hump10Factored
  constructor
  · exact lt_of_lt_of_le (by norm_num) hL
  · exact lt_of_le_of_lt hU (by norm_num)

end SEKernel.Closeout.HumpPeak
