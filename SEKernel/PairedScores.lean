/-
Finite IID paired-binary scores.  Codes 0,1,2 mean +1,-1,0 respectively.
The product law permits arbitrary within-board correlation of correctness;
different boards are separate product coordinates.  No large finite decision
procedure or unproved count-profile formula is used.
-/
import SEKernel.FiniteProbability

namespace SEKernel.PairedScores

open Finset FiniteProbability
open scoped Classical

def count {n : ℕ} (z : Fin n → Fin 3) (a : Fin 3) : ℕ :=
  (Finset.univ.filter fun i => z i=a).card

theorem count_eq_sum {n : ℕ} (z : Fin n → Fin 3) (a : Fin 3) :
    count z a=∑ i, if z i=a then 1 else 0 := by simp [count,Finset.sum_boole]

theorem count_two (x y a : Fin 3) :
    count ![x,y] a=(if x=a then 1 else 0)+(if y=a then 1 else 0) := by
  rw [count_eq_sum,Fin.sum_univ_two]
  simp

def difference (a : Fin 3) : ℤ := if a=0 then 1 else if a=1 then -1 else 0

theorem score_sum {n : ℕ} (z : Fin n → Fin 3) :
    (∑ i, difference (z i)) = (count z 0 : ℤ)-count z 1 := by
  have hp (a : Fin 3) : difference a =
      (if a=0 then (1:ℤ) else 0)-(if a=1 then 1 else 0) := by
    fin_cases a <;> norm_num [difference,Fin.ext_iff]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib]
  simp [count,Finset.sum_boole]

def flip {n : ℕ} (z : Fin n → Fin 3) : Fin n → Fin 3 :=
  fun i => Equiv.swap 0 1 (z i)

theorem flip_flip {n : ℕ} (z : Fin n → Fin 3) : flip (flip z)=z := by
  funext i; simp [flip]

def flipEquiv (n : ℕ) : (Fin n → Fin 3) ≃ (Fin n → Fin 3) where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

theorem count_flip {n : ℕ} (z : Fin n → Fin 3) (a : Fin 3) :
    count (flip z) a = count z (Equiv.swap 0 1 a) := by
  unfold count
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have ht := congrArg (Equiv.swap (0:Fin 3) 1) h
    simpa [flip] using ht
  · intro h
    simp only [flip]
    rw [h]; simp

@[simp] theorem count_flip_plus {n : ℕ} (z : Fin n → Fin 3) : count (flip z) 0=count z 1 := by
  rw [count_flip]; simp
@[simp] theorem count_flip_minus {n : ℕ} (z : Fin n → Fin 3) : count (flip z) 1=count z 0 := by
  rw [count_flip]; simp
@[simp] theorem count_flip_zero {n : ℕ} (z : Fin n → Fin 3) : count (flip z) 2=count z 2 := by
  rw [count_flip]; norm_num [Equiv.swap_apply_def,Fin.ext_iff]

def weight (a b c : ℝ) (j : Fin 3) : ℝ := if j=0 then a else if j=1 then b else c

def wordMass {n : ℕ} (a b c : ℝ) (z : Fin n → Fin 3) : ℝ := ∏ i, weight a b c (z i)

theorem wordMass_counts {n : ℕ} (a b c : ℝ) (z : Fin n → Fin 3) :
    wordMass a b c z = a^(count z 0)*b^(count z 1)*c^(count z 2) := by
  have hp (j : Fin 3) : weight a b c j =
      (if j=0 then a else 1)*(if j=1 then b else 1)*(if j=2 then c else 1) := by
    fin_cases j <;> simp [weight,Fin.ext_iff]
  unfold wordMass
  simp_rw [hp]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one,count]

theorem wordMass_total (a b c : ℝ) (n : ℕ) :
    (∑ z : Fin n → Fin 3, wordMass a b c z)=(a+b+c)^n := by
  unfold wordMass
  rw [← Fintype.prod_sum]
  have hsum : (∑ j : Fin 3, weight a b c j)=a+b+c := by
    rw [Fin.sum_univ_succ,Fin.sum_univ_two]
    change weight a b c 0+(weight a b c 1+weight a b c 2)=a+b+c
    norm_num [weight,Fin.ext_iff]
    ring
  simp only [hsum,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

noncomputable def pairedLaw (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) : Law (Fin 3) where
  mass := weight a b c
  nonneg j := by unfold weight; split_ifs <;> assumption
  total := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_two]
    change weight a b c 0+(weight a b c 1+weight a b c 2)=1
    norm_num [weight,Fin.ext_iff]
    linarith

noncomputable def sampleLaw (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) (n : ℕ) : Law (Fin n → Fin 3) :=
  Law.pi (fun _ => pairedLaw a b c ha hb hc htotal)

theorem sample_mass {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) {n : ℕ} (z : Fin n → Fin 3) :
    (sampleLaw a b c ha hb hc htotal n).mass z =
      a^(count z 0)*b^(count z 1)*c^(count z 2) := by
  have hp (j : Fin 3) : weight a b c j =
      (if j=0 then a else 1)*(if j=1 then b else 1)*(if j=2 then c else 1) := by
    fin_cases j <;> simp [weight,Fin.ext_iff]
  unfold sampleLaw Law.pi pairedLaw
  simp only
  simp_rw [hp]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one,count]

noncomputable def winProbability {n : ℕ} (L : Law (Fin n → Fin 3)) : ℝ :=
  L.prob (fun z => count z 1<count z 0)+
    (1/2)*L.prob (fun z => count z 0=count z 1)

theorem outcome_probability_total {n : ℕ} (L : Law (Fin n → Fin 3)) :
    L.prob (fun z => count z 1<count z 0)+
      L.prob (fun z => count z 0<count z 1)+
      L.prob (fun z => count z 0=count z 1)=1 := by
  classical
  unfold Law.prob
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← L.total]
  apply Finset.sum_congr rfl
  intro z _
  rcases lt_trichotomy (count z 0) (count z 1) with h | h | h <;>
    simp [h, Nat.ne_of_lt, Nat.ne_of_gt, Nat.not_lt_of_ge, le_of_lt]

/-- Pair the actual ordered word with its sign-reflected word. -/
theorem win_reflection_identity {n : ℕ} (L : Law (Fin n → Fin 3)) :
    winProbability L-1/2 = (1/2)*
      ∑ z, if count z 1<count z 0 then L.mass z-L.mass (flip z) else 0 := by
  classical
  have hneg : L.prob (fun z => count z 0<count z 1) =
      ∑ z, if count z 1<count z 0 then L.mass (flip z) else 0 := by
    unfold Law.prob
    calc
      _ = ∑ z, if count z 0<count z 1 then L.mass z else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases h : count z 0<count z 1 <;> simp [h]
      _ = ∑ z, if count (flip z) 0<count (flip z) 1 then L.mass (flip z) else 0 :=
        ((flipEquiv n).sum_comp (fun z => if count z 0<count z 1 then L.mass z else 0)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases h : count z 1<count z 0 <;> simp [h]
  have hsum : (∑ z, if count z 1<count z 0 then L.mass z-L.mass (flip z) else 0) =
      L.prob (fun z => count z 1<count z 0)-L.prob (fun z => count z 0<count z 1) := by
    rw [hneg, Law.prob, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> ring
  rw [hsum]
  unfold winProbability
  linarith [outcome_probability_total L]

theorem reflected_mass_order {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) (hba : b ≤ a) {n : ℕ} (z : Fin n → Fin 3)
    (hcount : count z 1 ≤ count z 0) :
    (sampleLaw a b c ha hb hc htotal n).mass (flip z) ≤
      (sampleLaw a b c ha hb hc htotal n).mass z := by
  rw [sample_mass, sample_mass, count_flip_plus, count_flip_minus, count_flip_zero]
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hcount
  rw [hd, pow_add, pow_add]
  have hp := pow_le_pow_left₀ hb hba d
  nlinarith [mul_nonneg (show 0 ≤ a^(count z 1)*b^(count z 1)*c^(count z 2) by positivity)
    (sub_nonneg.mpr hp)]

theorem iid_win_ge_half {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) (hba : b ≤ a) (n : ℕ) :
    1/2 ≤ winProbability (sampleLaw a b c ha hb hc htotal n) := by
  have h := win_reflection_identity (sampleLaw a b c ha hb hc htotal n)
  have hn : 0 ≤ ∑ z : Fin n → Fin 3,
      if count z 1<count z 0 then
        (sampleLaw a b c ha hb hc htotal n).mass z-
          (sampleLaw a b c ha hb hc htotal n).mass (flip z) else 0 := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs with hz
    · exact sub_nonneg.mpr (reflected_mass_order ha hb hc htotal hba z hz.le)
    · rfl
  linarith

theorem iid_win_gt_half {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) (hba : b < a) {n : ℕ} (hn : 0 < n) :
    1/2 < winProbability (sampleLaw a b c ha hb hc htotal n) := by
  have hid := win_reflection_identity (sampleLaw a b c ha hb hc htotal n)
  have hsum : 0 < ∑ z : Fin n → Fin 3,
      if count z 1<count z 0 then
        (sampleLaw a b c ha hb hc htotal n).mass z-
          (sampleLaw a b c ha hb hc htotal n).mass (flip z) else 0 := by
    apply Finset.sum_pos'
    · intro z _
      split_ifs with hz
      · exact sub_nonneg.mpr (reflected_mass_order ha hb hc htotal hba.le z hz.le)
      · rfl
    · refine ⟨fun _ => 0, Finset.mem_univ _, ?_⟩
      have hcounts : count (fun _ : Fin n => (0:Fin 3)) 0=n ∧
          count (fun _ : Fin n => (0:Fin 3)) 1=0 ∧
          count (fun _ : Fin n => (0:Fin 3)) 2=0 := by simp [count,Fin.ext_iff]
      rw [if_pos (by simpa [hcounts] using hn), sample_mass, sample_mass,
        count_flip_plus, count_flip_minus, count_flip_zero]
      simp only [hcounts, pow_zero, mul_one, one_mul]
      exact sub_pos.mpr (pow_lt_pow_left₀ hba hb (Nat.ne_of_gt hn))
  linarith

theorem iid_win_swap {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) (n : ℕ) :
    winProbability (sampleLaw a b c ha hb hc htotal n)+
      winProbability (sampleLaw b a c hb ha hc (by linarith) n)=1 := by
  classical
  have hm (z : Fin n → Fin 3) :
      (sampleLaw b a c hb ha hc (by linarith) n).mass (flip z)=
      (sampleLaw a b c ha hb hc htotal n).mass z := by
    rw [sample_mass, sample_mass, count_flip_plus, count_flip_minus, count_flip_zero]
    ring
  have hp : (sampleLaw b a c hb ha hc (by linarith) n).prob
      (fun z => count z 1<count z 0) =
      (sampleLaw a b c ha hb hc htotal n).prob (fun z => count z 0<count z 1) := by
    unfold Law.prob
    calc
      _ = ∑ z, if count z 1<count z 0 then
          (sampleLaw b a c hb ha hc (by linarith) n).mass z else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases h : count z 1<count z 0 <;> simp [h]
      _ = ∑ z, if count (flip z) 1<count (flip z) 0 then
          (sampleLaw b a c hb ha hc (by linarith) n).mass (flip z) else 0 :=
        ((flipEquiv n).sum_comp (fun z => if count z 1<count z 0 then
          (sampleLaw b a c hb ha hc (by linarith) n).mass z else 0)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases h : count z 0<count z 1 <;> simp [h,hm]
  have ht : (sampleLaw b a c hb ha hc (by linarith) n).prob
      (fun z => count z 0=count z 1) =
      (sampleLaw a b c ha hb hc htotal n).prob (fun z => count z 0=count z 1) := by
    unfold Law.prob
    calc
      _ = ∑ z, if count z 0=count z 1 then
          (sampleLaw b a c hb ha hc (by linarith) n).mass z else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases h : count z 0=count z 1 <;> simp [h]
      _ = ∑ z, if count (flip z) 0=count (flip z) 1 then
          (sampleLaw b a c hb ha hc (by linarith) n).mass (flip z) else 0 :=
        ((flipEquiv n).sum_comp (fun z => if count z 0=count z 1 then
          (sampleLaw b a c hb ha hc (by linarith) n).mass z else 0)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases h : count z 0=count z 1 <;> simp [h,hm,eq_comm]
  unfold winProbability
  rw [hp,ht]
  linarith [outcome_probability_total (sampleLaw a b c ha hb hc htotal n)]

/-- Doc A/B B2.1 exact sign, for n≥1, proved on the actual IID word law. -/
theorem iid_win_sign {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) {n : ℕ} (hn : 0 < n) :
    (1/2 < winProbability (sampleLaw a b c ha hb hc htotal n) ↔ b<a) ∧
    (winProbability (sampleLaw a b c ha hb hc htotal n)=1/2 ↔ a=b) ∧
    (winProbability (sampleLaw a b c ha hb hc htotal n)<1/2 ↔ a<b) := by
  have hswap := iid_win_swap ha hb hc htotal n
  rcases lt_trichotomy a b with hab | hab | hab
  · have hlt := iid_win_gt_half hb ha hc (by linarith) hab hn
    have hcur : winProbability (sampleLaw a b c ha hb hc htotal n)<1/2 := by linarith
    constructor
    · constructor <;> intro h <;> linarith
    constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> assumption
  · subst b
    have heq : winProbability (sampleLaw a a c ha ha hc htotal n)=1/2 := by linarith
    simp [heq]
  · have hgt := iid_win_gt_half ha hb hc htotal hab hn
    constructor
    · constructor <;> intro h <;> assumption
    constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith

noncomputable def lossFactor {n : ℕ} (z : Fin n → Fin 3) : ℝ :=
  if count z 0<count z 1 then 1 else if count z 0=count z 1 then 1/2 else 0

theorem lossFactor_nonneg {n : ℕ} (z : Fin n → Fin 3) : 0 ≤ lossFactor z := by
  unfold lossFactor; split_ifs <;> norm_num

theorem lossFactor_reflect {n : ℕ} (z : Fin n → Fin 3) : lossFactor z+lossFactor (flip z)=1 := by
  unfold lossFactor
  simp only [count_flip_plus,count_flip_minus]
  rcases lt_trichotomy (count z 0) (count z 1) with h | h | h <;>
    simp [h, Nat.ne_of_lt, Nat.ne_of_gt, Nat.not_lt_of_ge, le_of_lt]
  <;> norm_num

theorem win_error_sum {n : ℕ} (L : Law (Fin n → Fin 3)) :
    1-winProbability L=∑ z, L.mass z*lossFactor z := by
  have hid : (∑ z, L.mass z*lossFactor z) =
      L.prob (fun z => count z 0<count z 1)+(1/2)*L.prob (fun z => count z 0=count z 1) := by
    unfold lossFactor Law.prob
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rcases lt_trichotomy (count z 0) (count z 1) with h | h | h <;>
      simp [h, Nat.ne_of_lt, Nat.ne_of_gt, Nat.not_lt_of_ge, le_of_lt]
    <;> ring
  rw [hid]
  unfold winProbability
  linarith [outcome_probability_total L]

/-- Fair-coin error and the nonpositive-score event differ only at ties. -/
theorem error_le_nonpositive_le_twice_error {n : ℕ} (L : Law (Fin n → Fin 3)) :
    1-winProbability L ≤ L.prob (fun z => count z 0≤count z 1) ∧
    L.prob (fun z => count z 0≤count z 1) ≤ 2*(1-winProbability L) := by
  have herror : L.expect lossFactor=1-winProbability L := (win_error_sum L).symm
  constructor
  · rw [← herror]
    rw [← L.expect_indicator (fun z => count z 0≤count z 1)]
    apply L.expect_mono
    intro z
    unfold lossFactor
    rcases lt_trichotomy (count z 0) (count z 1) with h | h | h <;>
      simp [h,le_of_lt,not_le_of_gt,Nat.not_lt_of_ge,Nat.ne_of_lt,Nat.ne_of_gt] <;> norm_num
  · have h := L.prob_le_expect (fun z => count z 0≤count z 1)
      (Z:=fun z => 2*lossFactor z) (fun z => mul_nonneg (by norm_num) (lossFactor_nonneg z))
      (by
        intro z hz
        rcases lt_or_eq_of_le hz with h | h <;> simp [lossFactor,h])
    simpa only [L.expect_const_mul,herror] using h

/-- The square-root product mass dominates the original mass on loss and
tie words, including b=0; no inverse of b is taken. -/
theorem loss_mass_geometric_mean {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hba : b ≤ a) {n : ℕ} (z : Fin n → Fin 3)
    (hcount : count z 0 ≤ count z 1) :
    wordMass a b c z ≤ wordMass (Real.sqrt (a*b)) (Real.sqrt (a*b)) c z := by
  let g := Real.sqrt (a*b)
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have hg2 : g^2=a*b := Real.sq_sqrt (mul_nonneg ha hb)
  have hbg : b≤g := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hba)]
  rw [wordMass_counts,wordMass_counts]
  change a^(count z 0)*b^(count z 1)*c^(count z 2) ≤
    g^(count z 0)*g^(count z 1)*c^(count z 2)
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hcount
  rw [hd,pow_add,pow_add]
  have hfac : a^(count z 0)*b^(count z 0)=g^(count z 0)*g^(count z 0) := by
    rw [← mul_pow,← mul_pow,← pow_two,hg2]
  calc
    a^(count z 0)*(b^(count z 0)*b^d)*c^(count z 2) =
      (a^(count z 0)*b^(count z 0))*b^d*c^(count z 2) := by ring
    _ ≤ (a^(count z 0)*b^(count z 0))*g^d*c^(count z 2) := by
      gcongr
    _ = _ := by rw [hfac]; ring

/-- Doc A B2.2, equation (B2.3), sharper finite error bound, proved directly on IID words.
The half factor comes from the reflected square-root mass, including ties. -/
theorem iid_sharp_error_bound {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) (hba : b<a) (n : ℕ) :
    1-winProbability (sampleLaw a b c ha hb hc htotal n) ≤
      (1/2)*(1-(a+b)+2*Real.sqrt (a*b))^n := by
  let g := Real.sqrt (a*b)
  let F : (Fin n → Fin 3) → ℝ := wordMass g g c
  have hreflect (z : Fin n → Fin 3) : F (flip z)=F z := by
    dsimp only [F]
    rw [wordMass_counts,wordMass_counts,count_flip_plus,count_flip_minus,count_flip_zero]
    ring
  have hsum : (∑ z, F z*lossFactor z) = (1/2)*(∑ z, F z) := by
    have hr : (∑ z, F (flip z)*lossFactor (flip z))=(∑ z, F z*lossFactor z) :=
      (flipEquiv n).sum_comp (fun z => F z*lossFactor z)
    have hp : (∑ z, F z*lossFactor z)+(∑ z, F (flip z)*lossFactor (flip z))=∑ z,F z := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      rw [hreflect,← mul_add,lossFactor_reflect,mul_one]
    linarith
  rw [win_error_sum]
  calc
    _ ≤ ∑ z, F z*lossFactor z := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : count z 0≤count z 1
      · apply mul_le_mul_of_nonneg_right _ (lossFactor_nonneg z)
        change wordMass a b c z≤wordMass g g c z
        exact loss_mass_geometric_mean ha hb hc hba.le z hz
      · simp [lossFactor,not_lt_of_ge (by omega : count z 1≤count z 0),
          show count z 0≠count z 1 by omega]
    _ = (1/2)*(g+g+c)^n := by rw [hsum,wordMass_total]
    _ = _ := by congr 2; dsimp [g]; linarith

theorem sqrt_base_le_rational {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htotal : a+b+c=1) (hba : b<a) :
    1-(a+b)+2*Real.sqrt (a*b) ≤ 1-(a-b)^2/(2*(a+b)) := by
  have hs : 0<a+b := by linarith
  have hg2 := Real.sq_sqrt (mul_nonneg ha hb)
  have hsq := sq_nonneg (a+b-2*Real.sqrt (a*b))
  have hbnd : (a-b)^2/(2*(a+b))≤a+b-2*Real.sqrt (a*b) := by
    apply (div_le_iff₀ (show 0<2*(a+b) by positivity)).2
    nlinarith
  linarith

/-- The rational half-geometric bound is valid with positive disagreement,
which follows here from the explicit positive paired mean a-b. -/
theorem iid_sharp_rational_error_bound {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) (hba : b<a) (n : ℕ) :
    1-winProbability (sampleLaw a b c ha hb hc htotal n) ≤
      (1/2)*(1-(a-b)^2/(2*(a+b)))^n := by
  apply (iid_sharp_error_bound ha hb hc htotal hba n).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply pow_le_pow_left₀ _ (sqrt_base_le_rational ha hb htotal hba)
  have hg := Real.sqrt_nonneg (a*b)
  linarith

/-- Doc B B2.4's nonpositive-score probability, in addition to the sharper
fair-coin error bound.  Positivity of a-b keeps the denominator meaningful. -/
theorem iid_nonpositive_rational_bound {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (htotal : a+b+c=1) (hba : b<a) (n : ℕ) :
    (sampleLaw a b c ha hb hc htotal n).prob (fun z => count z 0≤count z 1) ≤
      (1-(a-b)^2/(2*(a+b)))^n := by
  have h := (error_le_nonpositive_le_twice_error (sampleLaw a b c ha hb hc htotal n)).2
  have hbnd := iid_sharp_rational_error_bound ha hb hc htotal hba n
  linarith

theorem sum_twoWords (F : (Fin 2 → Fin 3) → ℝ) :
    (∑ z, F z)=∑ x : Fin 3, ∑ y : Fin 3, F ![x,y] := by
  have h := (finTwoArrowEquiv (Fin 3)).symm.sum_comp F
  simpa only [Fintype.sum_prod_type,finTwoArrowEquiv] using h.symm

/-- The two-board count formula is proved before evaluating its exact
counterexamples.  Its nine ordered outcomes are a small finite sum. -/
theorem iid_win_two {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) :
    winProbability (sampleLaw a b c ha hb hc htotal 2)=
      1/2+(a-b)*(1-(a+b)/2) := by
  have h := win_error_sum (sampleLaw a b c ha hb hc htotal 2)
  rw [sum_twoWords] at h
  simp_rw [sample_mass] at h
  generalize hQ : winProbability (sampleLaw a b c ha hb hc htotal 2)=Q at h ⊢
  simp only [Fin.sum_univ_three] at h
  norm_num [lossFactor,count_two] at h
  norm_num [Fin.ext_iff] at h
  have hC : c=1-a-b := by linarith
  rw [hC] at h
  nlinarith

theorem paired_moments {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) :
    (pairedLaw a b c ha hb hc htotal).expect (fun j => (difference j : ℝ))=a-b ∧
    (pairedLaw a b c ha hb hc htotal).variance (fun j => (difference j : ℝ))=
      a+b-(a-b)^2 := by
  have hm : (pairedLaw a b c ha hb hc htotal).expect (fun j => (difference j : ℝ))=a-b := by
    change (∑ j : Fin 3, weight a b c j*(difference j : ℝ))=a-b
    rw [Fin.sum_univ_three]
    norm_num [weight,difference,Fin.ext_iff]
    ring
  constructor
  · exact hm
  · rw [Law.variance_eq,hm]
    have hs : (pairedLaw a b c ha hb hc htotal).expect (fun j => (difference j : ℝ)^2)=a+b := by
      change (∑ j : Fin 3, weight a b c j*(difference j : ℝ)^2)=a+b
      rw [Fin.sum_univ_three]
      norm_num [weight,difference,Fin.ext_iff]
    rw [hs]

theorem iid_paired_average_moments {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htotal : a+b+c=1) {n : ℕ} (hn : 0<n) :
    (sampleLaw a b c ha hb hc htotal n).expect
      (fun z => (∑ i, (difference (z i) : ℝ))/n)=a-b ∧
    (sampleLaw a b c ha hb hc htotal n).variance
      (fun z => (∑ i, (difference (z i) : ℝ))/n)=(a+b-(a-b)^2)/n := by
  have h := Law.iid_average hn (pairedLaw a b c ha hb hc htotal) (fun j => (difference j : ℝ))
  have hm := paired_moments ha hb hc htotal
  simpa only [sampleLaw,hm.1,hm.2] using h

noncomputable def gapCounterexampleLow : Law (Fin 2 → Fin 3) :=
  sampleLaw (1/10) 0 (9/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2
noncomputable def gapCounterexampleHigh : Law (Fin 2 → Fin 3) :=
  sampleLaw (111/200) (89/200) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2

theorem larger_gap_fewer_iid_wins :
    winProbability gapCounterexampleLow=119/200 ∧
    winProbability gapCounterexampleHigh=111/200 ∧
    (1/10:ℝ)<111/200-89/200 ∧ (111/200:ℝ)<119/200 := by
  unfold gapCounterexampleLow gapCounterexampleHigh
  rw [iid_win_two,iid_win_two]
  norm_num

noncomputable def equalVarianceLow : Law (Fin 2 → Fin 3) :=
  sampleLaw (181/200) (1/200) (9/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2
noncomputable def equalVarianceHigh : Law (Fin 2 → Fin 3) :=
  sampleLaw (4809/5000) (109/5000) (41/2500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2

/-- Doc A B6.1's equal single-board variance witness.  The reliability
values are evaluated through the proved two-board counting formula. -/
theorem equal_variance_larger_gap_fewer_iid_wins :
    winProbability equalVarianceLow=1981/2000 ∧
    winProbability equalVarianceHigh=244427/250000 ∧
    (91/100:ℝ)-(9/10)^2=1/10 ∧
    (2459/2500:ℝ)-(47/50)^2=1/10 ∧
    (9/10:ℝ)<47/50 ∧ (244427/250000:ℝ)<1981/2000 := by
  unfold equalVarianceLow equalVarianceHigh
  rw [iid_win_two,iid_win_two]
  norm_num

end SEKernel.PairedScores
