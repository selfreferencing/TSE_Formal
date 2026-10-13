import SEKernel.FiniteProbability
import SEKernel.MutationBaseline
import SEKernel.FirstAppearancePlurality

/-! Finite copy counts and actual correlated-answer laws. No side-branch import. -/
namespace SEKernel.CorrelatedAnswers
open FiniteProbability
open scoped BigOperators Classical
noncomputable section

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- The Bernoulli correctness observable. -/
def bitValue (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem bernoulli_bit_mean (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (MutationBaseline.bernoulli p hp hp').expect bitValue = p := by
  exact MutationBaseline.bernoulli_mean p hp hp'

@[simp] theorem bernoulli_bit_variance (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (MutationBaseline.bernoulli p hp hp').variance bitValue = p*(1-p) := by
  rw [Law.variance_eq, bernoulli_bit_mean]
  have h : (fun b => bitValue b ^ 2) = bitValue := by funext b; cases b <;> norm_num [bitValue]
  rw [h, bernoulli_bit_mean]
  ring

/-- A real copy count is convenient for the finite-sum identities. Natural copy
multiplicities are coerced into this definition in `natural_copies_bound`. -/
def effectiveCopies (k : ι → ℝ) : ℝ := (∑ i, k i)^2 / ∑ i, k i^2

/-- Exact all-pairs square identity, including the diagonal zero terms. -/
theorem pair_square_identity (k : ι → ℝ) :
    (∑ i, ∑ j, (k i-k j)^2) =
      2*((Fintype.card ι : ℝ)*(∑ i, k i^2)-(∑ i, k i)^2) := by
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_mul]
  rw [← Finset.mul_sum]
  ring

/-- Cauchy bound with an explicit positive square sum. -/
theorem effectiveCopies_le (k : ι → ℝ) (hs : 0 < ∑ i, k i^2) :
    effectiveCopies k ≤ Fintype.card ι := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) => sq_nonneg (k i-k j)))
  rw [pair_square_identity] at h
  apply (div_le_iff₀ hs).2
  nlinarith

/-- Equality holds precisely for balanced multiplicities; no strictness is lost. -/
theorem effectiveCopies_eq_iff (k : ι → ℝ) (hs : 0 < ∑ i, k i^2) :
    effectiveCopies k = Fintype.card ι ↔ ∀ i j, k i = k j := by
  constructor
  · intro h
    have hid := pair_square_identity k
    have hz : (∑ i, ∑ j, (k i-k j)^2) = 0 := by
      dsimp [effectiveCopies] at h
      nlinarith [show (∑ i, k i)^2 = (Fintype.card ι : ℝ)*∑ i, k i^2 by
        exact (div_eq_iff (ne_of_gt hs)).1 h]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg (k i-k j)))).1 hz
    intro i j
    have hi := hall i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (k i-k j))).1 hi
    have hsq := hj j (Finset.mem_univ j)
    nlinarith [sq_nonneg (k i-k j)]
  · intro h
    have hz : (∑ i, ∑ j, (k i-k j)^2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [h i j, sub_self]
      norm_num
    have hid := pair_square_identity k
    apply (div_eq_iff (ne_of_gt hs)).2
    nlinarith

/-- Natural positive clone multiplicities, including the balanced equality case. -/
theorem natural_copies_bound {L : ℕ} (hL : 0 < L) (k : Fin L → ℕ)
    (hk : ∀ i, 0 < k i) :
    effectiveCopies (fun i => (k i : ℝ)) ≤ L ∧
      (effectiveCopies (fun i => (k i : ℝ)) = L ↔ ∀ i j, k i = k j) := by
  have hs : 0 < ∑ i, (k i : ℝ)^2 := by
    let i : Fin L := ⟨0,hL⟩
    have hi : 0 < (k i : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hk i)
    exact hi.trans_le (Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i))
  constructor
  · simpa using effectiveCopies_le (fun i => (k i : ℝ)) hs
  · simpa only [Fintype.card_fin, Nat.cast_inj] using effectiveCopies_eq_iff (fun i => (k i : ℝ)) hs

/-- Actual independently sampled lineage indicators with deterministic cloning. -/
def cloneLaw (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : Law (ι → Bool) :=
  Law.pi (fun _ => MutationBaseline.bernoulli p hp hp')

def cloneAverage (k : ι → ℝ) (z : ι → Bool) : ℝ :=
  (∑ i, k i * bitValue (z i)) / ∑ i, k i

theorem clone_mean (k : ι → ℝ) (hn : (∑ i, k i) ≠ 0)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (cloneLaw (ι := ι) p hp hp').expect (cloneAverage k) = p := by
  unfold cloneAverage cloneLaw
  simp only [div_eq_mul_inv]
  rw [Law.expect_mul_const, Law.expect_sum]
  simp only [Law.expect_pi_coord, Law.expect_const_mul, bernoulli_bit_mean,
    ← Finset.sum_mul]
  field_simp

theorem clone_variance (k : ι → ℝ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (cloneLaw (ι := ι) p hp hp').variance (cloneAverage k) =
      p*(1-p)*(∑ i, k i^2)/(∑ i, k i)^2 := by
  unfold cloneAverage cloneLaw
  simp only [div_eq_mul_inv, mul_comm (∑ _, _) ((∑ i, k i)⁻¹)]
  rw [Law.variance_const_mul, Law.variance_pi_sum _ (fun i a => k i * bitValue a)]
  simp_rw [Law.variance_const_mul, bernoulli_bit_variance]
  rw [← Finset.sum_mul]
  ring

theorem clone_chebyshev (k : ι → ℝ) (hn : (∑ i, k i) ≠ 0)
    (hs : (∑ i, k i^2) ≠ 0) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    (cloneLaw (ι := ι) p hp hp').prob (fun z => ε ≤ |cloneAverage k z-p|) ≤
      p*(1-p)/(effectiveCopies k * ε^2) := by
  have h := (cloneLaw (ι := ι) p hp hp').chebyshev (cloneAverage k) hε
  rw [clone_mean k hn, clone_variance] at h
  convert h using 1 <;> unfold effectiveCopies
  field_simp

/-- Covariance of two finite observables; this symmetry uses the same actual law. -/
theorem covariance_symm (L : Law Ω) (X Y : Ω → ℝ) :
    L.covariance X Y = L.covariance Y X := by
  unfold Law.covariance
  congr 1
  funext ω
  ring

theorem covariance_self (L : Law Ω) (X : Ω → ℝ) : L.covariance X X = L.variance X := by
  simp only [Law.covariance, Law.variance, Law1.variance, Law.expect, Law1.mean, pow_two]

theorem variance_sum_covariance (L : Law Ω) (X : ι → Ω → ℝ) :
    L.variance (fun ω => ∑ i, X i ω) = ∑ i, ∑ j, L.covariance (X i) (X j) := by
  have hpoint : (fun ω => ((∑ i, X i ω)-L.expect (fun ω => ∑ i, X i ω))^2) =
      (fun ω => ∑ i, ∑ j, (X i ω-L.expect (X i))*(X j ω-L.expect (X j))) := by
    funext ω
    rw [L.expect_sum, ← Finset.sum_sub_distrib, pow_two, Finset.sum_mul_sum]
  change L.expect _ = _
  rw [hpoint, L.expect_sum]
  simp_rw [L.expect_sum]
  rfl

/-- A Bernoulli-valued observable has this variance under any finite law. -/
theorem binary_variance (L : Law Ω) (X : Ω → ℝ)
    (hX : ∀ ω, X ω=0 ∨ X ω=1) (p : ℝ) (hm : L.expect X=p) :
    L.variance X = p*(1-p) := by
  have hx : (fun ω => X ω^2) = X := by
    funext ω; rcases hX ω with h | h <;> simp [h]
  rw [L.variance_eq, hx, hm]
  ring

/-- The upper-triangle correlation sum, with every pair appearing once. -/
def correlationSum {n : ℕ} (L : Law Ω) (X : Fin n → Ω → ℝ) (p : ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then L.covariance (X i) (X j)/(p*(1-p)) else 0

theorem covariance_off_diagonal {n : ℕ} (L : Law Ω) (X : Fin n → Ω → ℝ) :
    (∑ i, ∑ j, if i=j then 0 else L.covariance (X i) (X j)) =
      2*(∑ i, ∑ j, if i < j then L.covariance (X i) (X j) else 0) := by
  have hpoint (i j : Fin n) : (if i=j then 0 else L.covariance (X i) (X j)) =
      (if i < j then L.covariance (X i) (X j) else 0)+
        (if j < i then L.covariance (X j) (X i) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, covariance_symm]
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then L.covariance (X j) (X i) else 0)]
  ring

/-- Exact finite variance with partial correlations. Positivity is explicit and
no independence is inferred from the second moments. -/
theorem correlated_variance {n : ℕ} (hn : 0<n) (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hp : 0<p) (hp' : p<1)
    (hX : ∀ i ω, X i ω=0 ∨ X i ω=1) (hm : ∀ i, L.expect (X i)=p) :
    L.variance (fun ω => (∑ i, X i ω)/(n : ℝ)) =
      p*(1-p)/(n : ℝ)^2*((n : ℝ)+2*correlationSum L X p) := by
  have hdiag : ∀ i, L.covariance (X i) (X i)=p*(1-p) := by
    intro i; rw [covariance_self, binary_variance L (X i) (hX i) p (hm i)]
  have hsplit : (∑ i, ∑ j, L.covariance (X i) (X j)) =
      (n : ℝ)*(p*(1-p))+(∑ i, ∑ j, if i=j then 0 else L.covariance (X i) (X j)) := by
    have hpoint (i j : Fin n) : L.covariance (X i) (X j) =
        (if i=j then p*(1-p) else 0)+(if i=j then 0 else L.covariance (X i) (X j)) := by
      by_cases h : i=j <;> simp [h, hdiag]
    calc
      _ = ∑ i, ∑ j, ((if i=j then p*(1-p) else 0)+
        (if i=j then 0 else L.covariance (X i) (X j))) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hpoint i j
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
  have hcorr : (∑ i, ∑ j, if i < j then L.covariance (X i) (X j) else 0) =
      p*(1-p)*correlationSum L X p := by
    unfold correlationSum
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; apply Finset.sum_congr rfl
    intro j _; split_ifs <;> field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hp')] <;> ring
  simp only [div_eq_mul_inv, mul_comm (∑ _, _) ((n : ℝ)⁻¹)]
  rw [L.variance_const_mul, variance_sum_covariance, hsplit, covariance_off_diagonal, hcorr]
  ring

def correlatedEffectiveSize {n : ℕ} (L : Law Ω) (X : Fin n → Ω → ℝ) (p : ℝ) : ℝ :=
  (n : ℝ)^2/((n : ℝ)+2*correlationSum L X p)

theorem correlated_effective_identity {n : ℕ} (hn : 0<n) (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hp : 0<p) (hp' : p<1)
    (hX : ∀ i ω, X i ω=0 ∨ X i ω=1) (hm : ∀ i, L.expect (X i)=p)
    (hbr : 0<(n : ℝ)+2*correlationSum L X p) :
    L.variance (fun ω => (∑ i, X i ω)/(n : ℝ)) =
      p*(1-p)/correlatedEffectiveSize L X p := by
  rw [correlated_variance hn L X p hp hp' hX hm]
  unfold correlatedEffectiveSize
  field_simp


/-- Equal pair correlations give the exchangeable effective-size denominator. -/
theorem exchangeable_effective_size {n : ℕ} (hn : 0<n) (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p ρ : ℝ)
    (hρ : ∀ i j, i≠j → L.covariance (X i) (X j)/(p*(1-p))=ρ)
    (hbr : 0<(n : ℝ)+2*correlationSum L X p) :
    correlatedEffectiveSize L X p = (n : ℝ)/(1+((n : ℝ)-1)*ρ) := by
  have hoff := covariance_off_diagonal L X
  have hcount : (∑ i : Fin n, ∑ j : Fin n, if i=j then (0 : ℝ) else ρ) =
      (n : ℝ)*((n : ℝ)-1)*ρ := by
    have hp (i j : Fin n) : (if i=j then (0 : ℝ) else ρ) = ρ-(if i=j then ρ else 0) := by
      by_cases h : i=j <;> simp [h]
    simp_rw [hp, Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Finset.sum_ite_eq,Finset.mem_univ,if_true]
    ring
  have hcor : 2*correlationSum L X p = (n : ℝ)*((n : ℝ)-1)*ρ := by
    have hpoint (i j : Fin n) :
        (if i=j then 0 else L.covariance (X i) (X j))/(p*(1-p)) =
          if i=j then 0 else ρ := by
      by_cases h : i=j
      · simp [h]
      · simp [h, hρ i j h]
    have hh : (∑ i, ∑ j, if i=j then 0 else L.covariance (X i) (X j))/(p*(1-p)) =
        ∑ i : Fin n, ∑ j : Fin n, if i=j then (0 : ℝ) else ρ := by
      simp_rw [Finset.sum_div, hpoint]
    rw [hoff] at hh
    have hd : (∑ i, ∑ j, if i < j then L.covariance (X i) (X j) else 0)/(p*(1-p)) =
        correlationSum L X p := by
      unfold correlationSum
      simp_rw [Finset.sum_div, ite_div, zero_div]
    rw [mul_div_assoc, hd, hcount] at hh
    exact hh
  have hnR : (n : ℝ)≠0 := by positivity
  unfold correlatedEffectiveSize
  rw [hcor]
  field_simp <;> ring

/-- Uniform four-point hidden outcomes, used for higher-order witnesses. -/
def fourLaw : Law (Fin 4) where
  mass _ := 1/4
  nonneg _ := by norm_num
  total := by norm_num

def evenPattern (s : Fin 4) (i : Fin 3) : Bool :=
  if s.val=0 then false else if s.val=1 then (if i.val=0 then false else true) else
    if s.val=2 then (if i.val=1 then false else true) else (if i.val=2 then false else true)

def oddPattern (s : Fin 4) (i : Fin 3) : Bool := !(evenPattern s i)

def majorityCorrect (z : Fin 3 → Bool) : Prop :=
  2≤(if z 0 then (1 : ℕ) else 0)+(if z 1 then 1 else 0)+(if z 2 then 1 else 0)

theorem even_pair_data (i : Fin 3) :
    fourLaw.expect (fun s => bitValue (evenPattern s i))=1/2 ∧
      fourLaw.variance (fun s => bitValue (evenPattern s i))=1/4 := by
  fin_cases i <;> norm_num [Law.expect,Law1.mean,Law.variance,Law1.variance,
    fourLaw,evenPattern,bitValue,Fin.sum_univ_succ]

theorem odd_pair_data (i : Fin 3) :
    fourLaw.expect (fun s => bitValue (oddPattern s i))=1/2 ∧
      fourLaw.variance (fun s => bitValue (oddPattern s i))=1/4 := by
  fin_cases i <;> norm_num [Law.expect,Law1.mean,Law.variance,Law1.variance,
    fourLaw,oddPattern,evenPattern,bitValue,Fin.sum_univ_succ]

/-- The complete binary pair tables coincide and are independent in both worlds. -/
theorem same_independent_pairs (i j : Fin 3) (hij : i≠j) (a b : Bool) :
    fourLaw.prob (fun s => evenPattern s i=a ∧ evenPattern s j=b)=1/4 ∧
      fourLaw.prob (fun s => oddPattern s i=a ∧ oddPattern s j=b)=1/4 := by
  fin_cases i <;> fin_cases j <;> cases a <;> cases b <;>
    first | exact False.elim (hij rfl) |
      norm_num [Law.prob,fourLaw,evenPattern,oddPattern,Fin.sum_univ_succ]

theorem pair_covariances_zero (i j : Fin 3) (hij : i≠j) :
    fourLaw.covariance (fun s => bitValue (evenPattern s i)) (fun s => bitValue (evenPattern s j))=0 ∧
      fourLaw.covariance (fun s => bitValue (oddPattern s i)) (fun s => bitValue (oddPattern s j))=0 := by
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) |
      norm_num [Law.covariance,Law.expect,Law1.mean,fourLaw,evenPattern,oddPattern,bitValue,
        Fin.sum_univ_succ]

/-- Doc B D.4: same complete pair data, majority probabilities 3/4 and 1/4. -/
theorem majority_accuracy_not_pairwise :
    fourLaw.prob (fun s => majorityCorrect (evenPattern s))=3/4 ∧
      fourLaw.prob (fun s => majorityCorrect (oddPattern s))=1/4 := by
  norm_num [Law.prob,fourLaw,majorityCorrect,evenPattern,oddPattern,Fin.sum_univ_succ]

theorem pairwise_effective_size_three :
    correlatedEffectiveSize fourLaw (fun i s => bitValue (evenPattern s i)) (1/2)=3 ∧
      correlatedEffectiveSize fourLaw (fun i s => bitValue (oddPattern s i)) (1/2)=3 := by
  norm_num [correlatedEffectiveSize,correlationSum,Law.covariance,Law.expect,Law1.mean,
    bitValue,evenPattern,oddPattern,fourLaw,Fin.sum_univ_succ]

/-- A concrete least-candidate rule, proved directly from the existing plurality. -/
theorem plurality_at_first_candidate {N : ℕ} {A : Type*}
    (z : Epistemic.OrderedWord N A) (i : Fin N)
    (hi : i∈Epistemic.candidatePositions z)
    (hfirst : ∀ j∈Epistemic.candidatePositions z, i≤j) : Epistemic.plurality z=z i := by
  classical
  have hn : (Epistemic.candidatePositions z).Nonempty := ⟨i,hi⟩
  have he : (Epistemic.candidatePositions z).min' hn=i :=
    le_antisymm ((Epistemic.candidatePositions z).min'_le i hi)
      (hfirst _ ((Epistemic.candidatePositions z).min'_mem hn))
  unfold Epistemic.plurality
  rw [dif_pos hn,he]

def duplicateWrong : Epistemic.OrderedWord 3 (Fin 3) := fun i => if i.val=0 then some 0 else some 1
def splitWrong : Epistemic.OrderedWord 3 (Fin 3) := fun i => some i

/-- Referee G4: the identical correctness pattern (1,0,0) has different winners. -/
theorem correctness_pattern_does_not_determine_plurality :
    (∀ i, duplicateWrong i=some 0 ↔ splitWrong i=some 0) ∧
      Epistemic.plurality duplicateWrong=some 1 ∧ Epistemic.plurality splitWrong=some 0 := by
  constructor
  · intro i; fin_cases i <;> norm_num [duplicateWrong,splitWrong,Fin.ext_iff]
  constructor
  · have hc : (1 : Fin 3)∈Epistemic.candidatePositions duplicateWrong := by
      simp only [Epistemic.candidatePositions,Finset.mem_filter,Finset.mem_univ,true_and,
        Epistemic.labelCount_eq_sum,Fin.forall_fin_succ,Fin.sum_univ_succ,
        duplicateWrong,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Option.some_ne_none,not_false_eq_true]
      norm_num [Fin.ext_iff,Matrix.cons_val_succ,Matrix.cons_val_zero] <;> simp
    have hf : ∀ j∈Epistemic.candidatePositions duplicateWrong, (1 : Fin 3)≤j := by
      intro j hj
      fin_cases j <;> simp only [Epistemic.candidatePositions,Finset.mem_filter,
        Finset.mem_univ,true_and,Epistemic.labelCount_eq_sum,Fin.forall_fin_succ,
        Fin.sum_univ_succ,duplicateWrong,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Option.some_ne_none,not_false_eq_true] at hj <;>
          (first | exact False.elim (by simpa using hj) | norm_num [Fin.le_def])
    simpa [duplicateWrong] using plurality_at_first_candidate duplicateWrong 1 hc hf
  · have hc : (0 : Fin 3)∈Epistemic.candidatePositions splitWrong := by
      simp only [Epistemic.candidatePositions,Finset.mem_filter,Finset.mem_univ,true_and,
        Epistemic.labelCount_eq_sum,Fin.forall_fin_succ,Fin.sum_univ_succ,
        splitWrong,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Option.some_ne_none,not_false_eq_true]
      norm_num [Fin.ext_iff,Matrix.cons_val_succ,Matrix.cons_val_zero] <;> simp
    simpa [splitWrong] using plurality_at_first_candidate splitWrong 0 hc (fun j _ => Fin.zero_le j)

/-- Two worlds with the same observation law and rule have the same output law.
Different truth designations are disjoint success events in that common law. -/
theorem two_world_success_sum {A : Type*} [Fintype A] (L : Law Ω)
    (rule : Ω → Law A) (a b : A) (hab : a≠b) :
    (L.bind rule).prob (fun x => x=a)+(L.bind rule).prob (fun x => x=b) ≤ 1 := by
  classical
  have ha : (L.bind rule).prob (fun x => x=a)=(L.bind rule).mass a := by simp [Law.prob]
  have hb : (L.bind rule).prob (fun x => x=b)=(L.bind rule).mass b := by simp [Law.prob]
  rw [ha,hb]
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({a,b} : Finset A) ⊆ Finset.univ from Finset.subset_univ _)
    (fun x _ _ => (L.bind rule).nonneg x)
  simpa [hab,(L.bind rule).total] using hs

theorem two_world_nonidentification {A : Type*} [Fintype A] (L : Law Ω)
    (rule : Ω → Law A) (a b : A) (hab : a≠b) :
    (L.bind rule).prob (fun x => x=a)≤1/2 ∨ (L.bind rule).prob (fun x => x=b)≤1/2 := by
  have h := two_world_success_sum L rule a b hab
  by_cases ha : (L.bind rule).prob (fun x => x=a)≤1/2
  · exact Or.inl ha
  · right; linarith

/-- Empirical answer frequencies under the actual separate-coordinate IID law. -/
def empiricalFrequency {A : Type*} {N : ℕ} (z : Fin N → A) (a : A) : ℝ :=
  (∑ i, if z i=a then (1 : ℝ) else 0)/N

theorem indicator_mean {A : Type*} [Fintype A] (π : Law A) (a : A) :
    π.expect (fun x => if x=a then (1 : ℝ) else 0)=π.mass a := by
  classical
  simp [Law.expect,Law1.mean]

theorem empirical_moments {A : Type*} [Fintype A] {N : ℕ} (hN : 0<N)
    (π : Law A) (a : A) :
    (Law.pi (fun _ : Fin N => π)).expect (fun z => empiricalFrequency z a)=π.mass a ∧
      (Law.pi (fun _ : Fin N => π)).variance (fun z => empiricalFrequency z a)=
        π.mass a*(1-π.mass a)/N := by
  classical
  have hm := indicator_mean π a
  have hv := binary_variance π (fun x => if x=a then (1 : ℝ) else 0)
    (fun x => by by_cases hx : x=a <;> simp [hx]) (π.mass a) hm
  simpa only [empiricalFrequency,hm,hv] using
    Law.iid_average hN π (fun x => if x=a then (1 : ℝ) else 0)

theorem empirical_squared_error {A : Type*} [Fintype A] {N : ℕ} (hN : 0<N) (π : Law A) :
    (Law.pi (fun _ : Fin N => π)).expect (fun z => ∑ a, (empiricalFrequency z a-π.mass a)^2)=
      (1-∑ a, π.mass a^2)/N := by
  classical
  rw [Law.expect_sum]
  have hterm (a : A) : (Law.pi (fun _ : Fin N => π)).expect
      (fun z => (empiricalFrequency z a-π.mass a)^2)=π.mass a*(1-π.mass a)/N := by
    have hm := empirical_moments hN π a
    calc
      _ = (Law.pi (fun _ : Fin N => π)).variance (fun z => empiricalFrequency z a) := by
        change _ = (Law.pi (fun _ : Fin N => π)).expect
          (fun z => (empiricalFrequency z a-(Law.pi (fun _ : Fin N => π)).expect
            (fun z => empiricalFrequency z a))^2)
        rw [hm.1]
      _ = _ := hm.2
  simp_rw [hterm, ← Finset.sum_div]
  congr 1
  have hp (a : A) : π.mass a*(1-π.mass a)=π.mass a-π.mass a^2 := by ring
  simp_rw [hp,Finset.sum_sub_distrib,π.total]

theorem empirical_concentration {A : Type*} [Fintype A] {N : ℕ} (hN : 0<N)
    (π : Law A) {ε : ℝ} (hε : 0<ε) :
    (Law.pi (fun _ : Fin N => π)).prob (fun z => ∃ a, ε≤|empiricalFrequency z a-π.mass a|) ≤
      (1-∑ a, π.mass a^2)/((N : ℝ)*ε^2) := by
  classical
  let P := Law.pi (fun _ : Fin N => π)
  calc
    _ ≤ ∑ a, P.prob (fun z => ε≤|empiricalFrequency z a-π.mass a|) := P.prob_exists_le _
    _ ≤ ∑ a, (π.mass a*(1-π.mass a)/N)/ε^2 := by
      apply Finset.sum_le_sum
      intro a _
      have hm := empirical_moments hN π a
      have hh := P.chebyshev (fun z => empiricalFrequency z a) hε
      rw [hm.1,hm.2] at hh
      exact hh
    _ = _ := by
      simp_rw [div_div, ← Finset.sum_div]
      congr 1
      have hp (a : A) : π.mass a*(1-π.mass a)=π.mass a-π.mass a^2 := by ring
      simp_rw [hp,Finset.sum_sub_distrib,π.total]

theorem empirical_concentration_simple {A : Type*} [Fintype A] {N : ℕ} (hN : 0<N)
    (π : Law A) {ε : ℝ} (hε : 0<ε) :
    (Law.pi (fun _ : Fin N => π)).prob (fun z => ∃ a, ε≤|empiricalFrequency z a-π.mass a|) ≤
      1/((N : ℝ)*ε^2) := by
  have h := empirical_concentration hN π hε
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs : 0≤∑ a, π.mass a^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  linarith


/-- The partial-correlation mean is p, with no independence assumption. -/
theorem correlated_mean {n : ℕ} (hn : 0<n) (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hm : ∀ i, L.expect (X i)=p) :
    L.expect (fun ω => (∑ i, X i ω)/(n : ℝ))=p := by
  simp only [div_eq_mul_inv]
  rw [L.expect_mul_const,L.expect_sum]
  simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem correlated_chebyshev {n : ℕ} (hn : 0<n) (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hp : 0<p) (hp' : p<1)
    (hX : ∀ i ω, X i ω=0 ∨ X i ω=1) (hm : ∀ i, L.expect (X i)=p)
    (hbr : 0<(n : ℝ)+2*correlationSum L X p) {ε : ℝ} (hε : 0<ε) :
    L.prob (fun ω => ε≤|(∑ i, X i ω)/(n : ℝ)-p|) ≤
      p*(1-p)/(correlatedEffectiveSize L X p*ε^2) := by
  have h := L.chebyshev (fun ω => (∑ i, X i ω)/(n : ℝ)) hε
  rw [correlated_mean hn L X p hm, correlated_effective_identity hn L X p hp hp' hX hm hbr,
    div_div] at h
  exact h

theorem correlatedEffectiveSize_le_sample_iff {n : ℕ} (hn : 0<n) (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hbr : 0<(n : ℝ)+2*correlationSum L X p) :
    correlatedEffectiveSize L X p≤n ↔ 0≤correlationSum L X p := by
  unfold correlatedEffectiveSize
  rw [div_le_iff₀ hbr]
  have hnR : 0<(n : ℝ) := by positivity
  constructor <;> intro h <;> nlinarith

/-- Correct plurality on an abstention-free binary word requires at least half
of its entries to carry the correct label, even with first-appearance ties. -/
theorem binary_vote_requires_half {N : ℕ} (hN : 0<N) (z : Fin N → Bool)
    (hz : Epistemic.plurality (fun i => some (z i))=some true) :
    1/2≤empiricalFrequency z true := by
  classical
  have hd := Epistemic.plurality_dominates_readable (fun i => some (z i)) true hz false
  have hsum : Epistemic.labelCount (fun i => some (z i)) (some true)+
      Epistemic.labelCount (fun i => some (z i)) (some false)=N := by
    rw [Epistemic.labelCount_eq_sum,Epistemic.labelCount_eq_sum,← Finset.sum_add_distrib]
    have hpoint (i : Fin N) :
        (if some (z i)=some true then (1 : ℕ) else 0)+
        (if some (z i)=some false then (1 : ℕ) else 0)=1 := by
      cases z i <;> norm_num
    simp_rw [hpoint]
    simp
  have hval : empiricalFrequency z true=
      (Epistemic.labelCount (fun i => some (z i)) (some true) : ℝ)/N := by
    unfold empiricalFrequency
    congr 1
    rw [Epistemic.labelCount_eq_sum,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : z i=true <;> simp [h]
  have hdR : (N : ℝ)≤2*(Epistemic.labelCount (fun i => some (z i)) (some true) : ℝ) := by
    exact_mod_cast (show N≤2*Epistemic.labelCount (fun i => some (z i)) (some true) by omega)
  rw [hval]
  apply (le_div_iff₀ (show 0<(N : ℝ) by positivity)).2
  linarith

/-- Doc A D3's 8/N wrong-mode bound on the actual independent binary-word law. -/
theorem biased_binary_accuracy_bound {N : ℕ} (hN : 0<N) :
    (Law.pi (fun _ : Fin N => MutationBaseline.bernoulli (1/3) (by norm_num) (by norm_num))).prob
      (fun z => Epistemic.plurality (fun i => some (z i))=some true) ≤ 8/(N : ℝ) := by
  let π := MutationBaseline.bernoulli (1/3) (by norm_num) (by norm_num)
  let P := Law.pi (fun _ : Fin N => π)
  have hm := empirical_moments hN π true
  have he : P.prob (fun z => Epistemic.plurality (fun i => some (z i))=some true) ≤
      P.prob (fun z => (1:ℝ)/6≤|empiricalFrequency z true-1/3|) := by
    apply P.prob_mono
    intro z hz
    have hh := binary_vote_requires_half hN z hz
    have ha := le_abs_self (empiricalFrequency z true-1/3)
    linarith
  have hc := P.chebyshev (fun z => empiricalFrequency z true) (show (0:ℝ)<1/6 by norm_num)
  have hmean : P.expect (fun z => empiricalFrequency z true)=1/3 := hm.1
  have hvar : P.variance (fun z => empiricalFrequency z true)=((1:ℝ)/3*(1-1/3))/N := hm.2
  rw [hmean,hvar] at hc
  have halg : (((1:ℝ)/3*(1-1/3))/N)/(1/6)^2=8/(N : ℝ) := by ring
  rw [halg] at hc
  exact he.trans hc

theorem biased_binary_accuracy_min_bound {N : ℕ} (hN : 0<N) :
    (Law.pi (fun _ : Fin N => MutationBaseline.bernoulli (1/3) (by norm_num) (by norm_num))).prob
      (fun z => Epistemic.plurality (fun i => some (z i))=some true) ≤ min 1 (8/(N : ℝ)) :=
  le_min (Law.prob_le_one _ _) (biased_binary_accuracy_bound hN)

/-- Finite covariance is bilinear under deterministic scaling. -/
theorem covariance_const_mul (L : Law Ω) (a b : ℝ) (X Y : Ω → ℝ) :
    L.covariance (fun ω => a*X ω) (fun ω => b*Y ω)=a*b*L.covariance X Y := by
  unfold Law.covariance
  simp only [L.expect_const_mul]
  calc
    _ = L.expect (fun ω => (a*b)*((X ω-L.expect X)*(Y ω-L.expect Y))) := by
      congr 1
      funext ω
      ring
    _ = _ := L.expect_const_mul (a*b) _

/-- Actual variance of a weighted sum, with each unordered pair counted once. -/
theorem weighted_variance_upper_triangle {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (w : Fin n → ℝ) :
    L.variance (fun ω => ∑ i, w i*X i ω)=
      (∑ i, (w i)^2*L.variance (X i))+
        2*(∑ i, ∑ j, if i<j then w i*w j*L.covariance (X i) (X j) else 0) := by
  let Y := fun i ω => w i*X i ω
  have hsplit : (∑ i, ∑ j, L.covariance (Y i) (Y j)) =
      (∑ i, L.covariance (Y i) (Y i))+
        (∑ i, ∑ j, if i=j then 0 else L.covariance (Y i) (Y j)) := by
    have hpoint (i j : Fin n) : L.covariance (Y i) (Y j)=
        (if i=j then L.covariance (Y i) (Y i) else 0)+
          (if i=j then 0 else L.covariance (Y i) (Y j)) := by
      by_cases h : i=j <;> simp [h]
    calc
      _ = ∑ i, ∑ j, ((if i=j then L.covariance (Y i) (Y i) else 0)+
          (if i=j then 0 else L.covariance (Y i) (Y j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hpoint i j
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',
        Finset.sum_ite_eq,Finset.mem_univ,if_true]
  change L.variance (fun ω => ∑ i, Y i ω)=_
  rw [variance_sum_covariance,hsplit,covariance_off_diagonal]
  simp only [Y,covariance_self,Law.variance_const_mul,covariance_const_mul]

/-- For normalized weights this is the reciprocal variance-effective sample size. -/
def weightedCorrelationBracket {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (w : Fin n → ℝ) : ℝ :=
  (∑ i, (w i)^2)+2*(∑ i, ∑ j,
    if i<j then w i*w j*(L.covariance (X i) (X j)/(p*(1-p))) else 0)

/-- Normalized deterministic weights preserve the common Bernoulli mean. -/
theorem normalized_weighted_mean {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (w : Fin n → ℝ)
    (hsum : ∑ i, w i=1) (hm : ∀ i, L.expect (X i)=p) :
    L.expect (fun ω => ∑ i, w i*X i ω)=p := by
  rw [L.expect_sum]
  simp_rw [L.expect_const_mul,hm]
  rw [← Finset.sum_mul,hsum,one_mul]

/-- Exact Bernoulli weighted-correlation variance; independence is not assumed. -/
theorem weighted_correlated_variance {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hp : 0<p) (hp' : p<1)
    (hX : ∀ i ω, X i ω=0 ∨ X i ω=1) (hm : ∀ i, L.expect (X i)=p)
    (w : Fin n → ℝ) :
    L.variance (fun ω => ∑ i, w i*X i ω)=
      p*(1-p)*weightedCorrelationBracket L X p w := by
  rw [weighted_variance_upper_triangle]
  simp_rw [binary_variance L _ (hX _) p (hm _)]
  have hdiag : (∑ i, (w i)^2*(p*(1-p)))=p*(1-p)*(∑ i, (w i)^2) := by
    rw [← Finset.sum_mul]
    ring
  have hoff : (∑ i, ∑ j, if i<j then w i*w j*L.covariance (X i) (X j) else 0)=
      p*(1-p)*(∑ i, ∑ j,
        if i<j then w i*w j*(L.covariance (X i) (X j)/(p*(1-p))) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> field_simp [ne_of_gt hp,ne_of_gt (sub_pos.mpr hp')] <;> ring
  rw [hdiag,hoff]
  unfold weightedCorrelationBracket
  ring

/-- This reciprocal has a variance interpretation only for a positive bracket. -/
def weightedEffectiveSize {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (w : Fin n → ℝ) : ℝ :=
  1/weightedCorrelationBracket L X p w

/-- A normalized weighted average has variance p(1-p)/effective size. The
nonnegative, sum-one weights and the positive bracket are explicit. -/
theorem weighted_effective_identity {n : ℕ} (L : Law Ω)
    (X : Fin n → Ω → ℝ) (p : ℝ) (hp : 0<p) (hp' : p<1)
    (hX : ∀ i ω, X i ω=0 ∨ X i ω=1) (hm : ∀ i, L.expect (X i)=p)
    (w : Fin n → ℝ) (hw : ∀ i, 0≤w i) (hsum : ∑ i, w i=1)
    (hbr : 0<weightedCorrelationBracket L X p w) :
    L.variance (fun ω => ∑ i, w i*X i ω)=p*(1-p)/weightedEffectiveSize L X p w := by
  rw [weighted_correlated_variance L X p hp hp' hX hm]
  unfold weightedEffectiveSize
  field_simp


/-- Mean squared distribution-estimation error is at most one over sample size. -/
theorem empirical_squared_error_le {A : Type*} [Fintype A] {N : ℕ} (hN : 0<N) (π : Law A) :
    (Law.pi (fun _ : Fin N => π)).expect (fun z => ∑ a, (empiricalFrequency z a-π.mass a)^2)≤1/(N : ℝ) := by
  rw [empirical_squared_error hN π]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs : 0≤∑ a, π.mass a^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  linarith

end
end SEKernel.CorrelatedAnswers
