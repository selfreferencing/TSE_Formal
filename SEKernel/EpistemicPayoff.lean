/-
Finite epistemic payoff accounting.  The three comparator cells use the full
ordered comparator; a response kernel may use a smaller observation.  Fixed
cell parameters and conditional means are deliberately separate objects.
Doc B A2, A5, A7, A8; Doc A A2, A5, A7, A8, with the referee corrections.
-/
import SEKernel.FiniteProbability
import SEKernel.FirstAppearancePlurality

namespace SEKernel.EpistemicPayoff

open Finset
open FiniteProbability

inductive Cell where
  | keep | post | absent
  deriving DecidableEq, Fintype

/-- A full comparator success has priority over posted reach. -/
noncomputable def cellOf (vote reach : Prop) : Cell := by
  classical
  exact if vote then .keep else if reach then .post else .absent

/-- A response is a finite output law at each complete comparison state. -/
abbrev ResponseKernel (Ω A : Type*) [Fintype Ω] [Fintype A] :=
  Kernel Ω (Option A)

noncomputable def correctness {Ω A : Type*} [Fintype Ω] [Fintype A]
    (K : ResponseKernel Ω A) (right : A) (ω : Ω) : ℝ :=
  (K ω).mass (some right)

/-- A response kernel supplies a genuine correctness probability at each state. -/
theorem correctness_bounds {Ω A : Type*} [Fintype Ω] [Fintype A]
    (K : ResponseKernel Ω A) (right : A) (ω : Ω) :
    0 ≤ correctness K right ω ∧ correctness K right ω ≤ 1 := by
  exact ⟨(K ω).nonneg (some right),
    Law1.coord_le_one (K ω).nonneg (K ω).total (some right)⟩

theorem cellOf_keep_iff (vote reach : Prop) : cellOf vote reach = .keep ↔ vote := by
  classical
  by_cases hv : vote <;> by_cases hr : reach <;> simp [cellOf, hv, hr]

/-- The abstract fixed-cell model.  No claim of prefix realizability is built in. -/
structure CellModel where
  weight : Cell → ℝ
  nonneg : ∀ c, 0 ≤ weight c
  total : ∑ c, weight c = 1

noncomputable def CellModel.accuracy (M : CellModel) (κ : Cell → ℝ) : ℝ :=
  ∑ c, M.weight c * κ c

noncomputable def CellModel.premium (M : CellModel) (κ : Cell → ℝ) : ℝ :=
  M.accuracy κ - M.weight .keep

theorem sum_cells (f : Cell → ℝ) :
    ∑ c, f c = f .keep + f .post + f .absent := by
  classical
  have hu : (Finset.univ : Finset Cell) = {.keep, .post, .absent} := by
    ext c
    cases c <;> simp
  rw [hu]
  simp [add_assoc]

theorem CellModel.weight_sum (M : CellModel) :
    M.weight .keep + M.weight .post + M.weight .absent = 1 := by
  rw [← sum_cells]; exact M.total

theorem premium_identity (M : CellModel) (κ : Cell → ℝ) :
    M.premium κ = M.weight .post * κ .post + M.weight .absent * κ .absent -
      M.weight .keep * (1 - κ .keep) := by
  unfold CellModel.premium CellModel.accuracy
  rw [sum_cells]
  ring

theorem premium_bounds (M : CellModel) (κ : Cell → ℝ)
    (hκ : ∀ c, 0 ≤ κ c ∧ κ c ≤ 1) :
    -M.weight .keep * (1 - κ .keep) ≤ M.premium κ ∧
      M.premium κ ≤ 1 - M.weight .keep := by
  rw [premium_identity]
  have hp := mul_nonneg (M.nonneg .post) (hκ .post).1
  have hn := mul_nonneg (M.nonneg .absent) (hκ .absent).1
  have hk := mul_nonneg (M.nonneg .keep) (sub_nonneg.mpr (hκ .keep).2)
  have hp' := mul_le_mul_of_nonneg_left (hκ .post).2 (M.nonneg .post)
  have hn' := mul_le_mul_of_nonneg_left (hκ .absent).2 (M.nonneg .absent)
  have ht := M.weight_sum
  constructor <;> nlinarith

theorem premium_pos_iff (M : CellModel) (κ : Cell → ℝ) :
    0 < M.premium κ ↔ M.weight .keep * (1 - κ .keep) <
      M.weight .post * κ .post + M.weight .absent * κ .absent := by
  rw [premium_identity]
  constructor <;> intro h <;> linarith

/-- The extra order hypothesis is essential: this is not a universal ceiling. -/
theorem premium_le_post_rate (M : CellModel) (κ : Cell → ℝ)
    (hκ : ∀ c, 0 ≤ κ c ∧ κ c ≤ 1) (horder : κ .absent ≤ κ .post) :
    M.premium κ ≤ κ .post := by
  rw [premium_identity]
  have h := M.weight_sum
  have h₁ := mul_le_mul_of_nonneg_left horder (M.nonneg .absent)
  have h₂ := mul_nonneg (M.nonneg .keep) ((hκ .post).1)
  have h₃ := mul_nonneg (M.nonneg .keep) (sub_nonneg.mpr (hκ .keep).2)
  have ht := congrArg (fun x : ℝ => x * κ .post) h
  nlinarith [ht]

theorem premium_transfer_identity (M : CellModel) (κ κhat : Cell → ℝ) :
    M.premium κ - M.premium κhat =
      ∑ c, M.weight c * (κ c - κhat c) := by
  unfold CellModel.premium CellModel.accuracy
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- The weighted form is valid for every null-cell convention. -/
theorem premium_transfer_bound (M : CellModel) (κ κhat : Cell → ℝ) :
    |M.premium κ - M.premium κhat| ≤
      ∑ c, M.weight c * |κ c - κhat c| := by
  rw [premium_transfer_identity]
  calc
    |∑ c, M.weight c * (κ c - κhat c)| ≤
        ∑ c, |M.weight c * (κ c - κhat c)| := abs_sum_le_sum_abs _ _
    _ = ∑ c, M.weight c * |κ c - κhat c| := by
      apply sum_congr rfl
      intro c _
      rw [abs_mul, abs_of_nonneg (M.nonneg c)]

theorem premium_transfer_uniform (M : CellModel) (κ κhat : Cell → ℝ)
    (ε : ℝ) (hε : ∀ c, |κ c - κhat c| ≤ ε) :
    |M.premium κ - M.premium κhat| ≤ ε := by
  calc
    _ ≤ ∑ c, M.weight c * |κ c - κhat c| := premium_transfer_bound M κ κhat
    _ ≤ ∑ c, M.weight c * ε := sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left (hε c) (M.nonneg c)
    _ = ε := by rw [← sum_mul, M.total, one_mul]

theorem premium_coarse_identity (M : CellModel) (κ : Cell → ℝ) :
    M.premium κ = -(1 - κ .keep) +
      (1 - κ .keep + κ .post) * M.weight .post +
      (1 - κ .keep + κ .absent) * M.weight .absent := by
  rw [premium_identity]
  have ht := M.weight_sum
  have hm := congrArg (fun x : ℝ => (1 - κ .keep) * x) ht
  nlinarith [hm]

section Partition
variable {Ω C : Type*} [Fintype Ω] [Fintype C]

noncomputable def cellMass (L : Law Ω) (cell : Ω → C) (c : C) : ℝ :=
  L.prob (fun ω => cell ω = c)

noncomputable def responseMass (L : Law Ω) (cell : Ω → C) (w : Ω → ℝ) (c : C) : ℝ := by
  classical
  exact L.expect (fun ω => if cell ω = c then w ω else 0)

/-- The null-cell default is explicit and has no effect on weighted accounting. -/
noncomputable def conditionalRate (L : Law Ω) (cell : Ω → C)
    (w : Ω → ℝ) (default : C → ℝ) (c : C) : ℝ := by
  classical
  exact if cellMass L cell c = 0 then default c else
    responseMass L cell w c / cellMass L cell c

theorem responseMass_bounds (L : Law Ω) (cell : Ω → C) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) (c : C) :
    0 ≤ responseMass L cell w c ∧ responseMass L cell w c ≤ cellMass L cell c := by
  classical
  unfold responseMass cellMass Law.expect Law.prob Law1.mean
  constructor
  · apply sum_nonneg
    intro ω _
    dsimp only
    by_cases hc : cell ω = c
    · simpa only [hc, ↓reduceIte] using mul_nonneg (L.nonneg ω) (hw ω).1
    · simp [hc]

  · apply sum_le_sum
    intro ω _
    dsimp only
    by_cases hc : cell ω = c
    · simpa only [hc, ↓reduceIte, mul_one] using
        mul_le_mul_of_nonneg_left (hw ω).2 (L.nonneg ω)
    · simp [hc]

/-- The default's range is needed only on null cells; it is an explicit input. -/
theorem conditionalRate_bounds (L : Law Ω) (cell : Ω → C) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) (default : C → ℝ)
    (hdefault : ∀ c, 0 ≤ default c ∧ default c ≤ 1) (c : C) :
    0 ≤ conditionalRate L cell w default c ∧ conditionalRate L cell w default c ≤ 1 := by
  classical
  by_cases hc : cellMass L cell c = 0
  · simpa only [conditionalRate, hc, ↓reduceIte] using hdefault c
  · have hm : 0 < cellMass L cell c :=
      lt_of_le_of_ne (L.prob_nonneg _) (Ne.symm hc)
    have hb := responseMass_bounds L cell w hw c
    simp only [conditionalRate, hc, ↓reduceIte]
    exact ⟨div_nonneg hb.1 hm.le, (div_le_one hm).2 hb.2⟩

theorem mass_mul_conditional (L : Law Ω) (cell : Ω → C) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) (default : C → ℝ) (c : C) :
    cellMass L cell c * conditionalRate L cell w default c =
      responseMass L cell w c := by
  classical
  unfold conditionalRate
  split_ifs with h
  · have hb := responseMass_bounds L cell w hw c
    rw [h]; simp; linarith
  · field_simp

theorem partition_expectation (L : Law Ω) (cell : Ω → C) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) (default : C → ℝ) :
    L.expect w = ∑ c, cellMass L cell c * conditionalRate L cell w default c := by
  classical
  simp_rw [mass_mul_conditional L cell w hw default]
  unfold responseMass Law.expect Law1.mean
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp [← mul_sum]

end Partition

section RealizedPayoff

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

/-- The actual cell law is the finite pushforward of the experiment law. -/
noncomputable def CellModel.ofLaw (L : Law Ω) (cell : Ω → Cell) : CellModel where
  weight := cellMass L cell
  nonneg c := L.prob_nonneg _
  total := (L.map cell).total

/-- A law-derived cell model has the original response's expectation. -/
theorem CellModel.ofLaw_accuracy (L : Law Ω) (cell : Ω → Cell) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) (default : Cell → ℝ) :
    (CellModel.ofLaw L cell).accuracy (conditionalRate L cell w default) = L.expect w := by
  exact (partition_expectation L cell w hw default).symm

/-- Actual comparator cells on the complete experiment state. -/
noncomputable def comparatorModel (L : Law Ω) (vote reach : Ω → Prop) : CellModel :=
  CellModel.ofLaw L (fun ω => cellOf (vote ω) (reach ω))

/-- Conditional correctness of an actual finite response kernel on the cells.
Null-cell defaults are supplied separately and disappear from weighted identities. -/
noncomputable def responseRates (L : Law Ω) (vote reach : Ω → Prop)
    (K : ResponseKernel Ω A) (right : A) (default : Cell → ℝ) : Cell → ℝ :=
  conditionalRate L (fun ω => cellOf (vote ω) (reach ω)) (correctness K right) default

theorem responseRates_bounds (L : Law Ω) (vote reach : Ω → Prop)
    (K : ResponseKernel Ω A) (right : A) (default : Cell → ℝ)
    (hdefault : ∀ c, 0 ≤ default c ∧ default c ≤ 1) (c : Cell) :
    0 ≤ responseRates L vote reach K right default c ∧
      responseRates L vote reach K right default c ≤ 1 :=
  conditionalRate_bounds L _ _ (correctness_bounds K right) default hdefault c

theorem comparatorModel_keep (L : Law Ω) (vote reach : Ω → Prop) :
    (comparatorModel L vote reach).weight .keep = L.prob vote := by
  change L.prob (fun ω => cellOf (vote ω) (reach ω) = .keep) = L.prob vote
  apply congrArg L.prob
  funext ω
  exact propext (cellOf_keep_iff (vote ω) (reach ω))

/-- Conditional-cell accounting for an actual law and response kernel.
No independence between voting, reach, and response is required. -/
theorem response_conditional_cell_identity (L : Law Ω) (vote reach : Ω → Prop)
    (K : ResponseKernel Ω A) (right : A) (default : Cell → ℝ) :
    L.expect (correctness K right) = ∑ c,
      L.prob (fun ω => cellOf (vote ω) (reach ω) = c) *
        responseRates L vote reach K right default c :=
  partition_expectation L _ _ (correctness_bounds K right) default

theorem response_accuracy_eq_expect (L : Law Ω) (vote reach : Ω → Prop)
    (K : ResponseKernel Ω A) (right : A) (default : Cell → ℝ) :
    (comparatorModel L vote reach).accuracy (responseRates L vote reach K right default) =
      L.expect (correctness K right) :=
  CellModel.ofLaw_accuracy L _ _ (correctness_bounds K right) default

/-- The abstract premium on the law-derived cells is exactly the operational
expectation of correctness minus the comparator's probability of success. -/
theorem response_premium_eq (L : Law Ω) (vote reach : Ω → Prop)
    (K : ResponseKernel Ω A) (right : A) (default : Cell → ℝ) :
    (comparatorModel L vote reach).premium (responseRates L vote reach K right default) =
      L.expect (correctness K right) - L.prob vote := by
  unfold CellModel.premium
  rw [response_accuracy_eq_expect, comparatorModel_keep]

/-- The three-cell premium identity specialized to the actual response law. -/
theorem response_premium_identity (L : Law Ω) (vote reach : Ω → Prop)
    (K : ResponseKernel Ω A) (right : A) (default : Cell → ℝ) :
    L.expect (correctness K right) - L.prob vote =
      (comparatorModel L vote reach).weight .post * responseRates L vote reach K right default .post +
      (comparatorModel L vote reach).weight .absent * responseRates L vote reach K right default .absent -
      L.prob vote * (1 - responseRates L vote reach K right default .keep) := by
  rw [← response_premium_eq L vote reach K right default, premium_identity,
    comparatorModel_keep]

/-- Operational premium bounds with an explicit [0,1] null-cell default. -/
theorem response_premium_bounds (L : Law Ω) (vote reach : Ω → Prop)
    (K : ResponseKernel Ω A) (right : A) (default : Cell → ℝ)
    (hdefault : ∀ c, 0 ≤ default c ∧ default c ≤ 1) :
    -L.prob vote * (1 - responseRates L vote reach K right default .keep) ≤
        L.expect (correctness K right) - L.prob vote ∧
      L.expect (correctness K right) - L.prob vote ≤ 1 - L.prob vote := by
  have hb := premium_bounds (comparatorModel L vote reach)
    (responseRates L vote reach K right default)
    (responseRates_bounds L vote reach K right default hdefault)
  rw [response_premium_eq, comparatorModel_keep] at hb
  exact hb

/-- The actual IID ordered-word comparator and prefix reach instantiate the
finite response-law bridge, including empty words and empty prefixes. -/
theorem ordered_response_premium_eq (π : Law (Option A)) (N k : ℕ) (right : A)
    (K : ResponseKernel (Epistemic.OrderedWord N A) A) (default : Cell → ℝ) :
    (comparatorModel (Epistemic.iidWordLaw π N)
      (fun z => Epistemic.correctVote z right) (fun z => Epistemic.reaches z k right)).premium
        (responseRates (Epistemic.iidWordLaw π N)
          (fun z => Epistemic.correctVote z right) (fun z => Epistemic.reaches z k right)
          K right default) =
      (Epistemic.iidWordLaw π N).expect (correctness K right) - Epistemic.voteAccuracy π N right :=
  response_premium_eq _ _ _ K right default

end RealizedPayoff

/-! Finite polynomial hump.  These algebraic statements are separate from the
ordered-sampling counting theorem; no counting theorem is assumed implicitly. -/

def hump10 (p : ℝ) : ℝ :=
  5*p*(1-p)^9 + 35*p^2*(1-p)^8 + 110*p^3*(1-p)^7 +
  205*p^4*(1-p)^6 + 125*p^5*(1-p)^5

def hump10Factored (p : ℝ) : ℝ :=
  p*(1-p)^5*(5+15*p+35*p^2+70*p^3)

theorem hump_forms_equal (p : ℝ) : hump10 p = hump10Factored p := by
  unfold hump10 hump10Factored
  ring

theorem hump_endpoints : hump10 0 = 0 ∧ hump10 1 = 0 := by
  norm_num [hump10]

theorem hump_positive {p : ℝ} (hp : 0 < p) (hp' : p < 1) : 0 < hump10 p := by
  rw [hump_forms_equal]
  unfold hump10Factored
  have hq : 0 < 1 - p := by linarith
  positivity

def reachPolynomial (k : ℕ) (p : ℝ) : ℝ := 1 - (1-p)^k
def binaryVote9 (p : ℝ) : ℝ :=
  126*p^5*(1-p)^4 + 84*p^6*(1-p)^3 + 36*p^7*(1-p)^2 + 9*p^8*(1-p) + p^9

theorem hump_reach_vote_polynomial (p : ℝ) :
    hump10 p = reachPolynomial 5 p - binaryVote9 p := by
  unfold hump10 reachPolynomial binaryVote9
  ring

def mixedRecognizer (k : ℕ) (p uptake : ℝ) : ℝ :=
  p^k + uptake * (1 - p^k - (1-p)^k)

theorem mixed_recognizer_threshold (k : ℕ) (p uptake vote : ℝ)
    (hmixed : 0 < 1 - p^k - (1-p)^k) :
    0 < mixedRecognizer k p uptake - vote ↔
      (vote - p^k) / (1 - p^k - (1-p)^k) < uptake := by
  rw [div_lt_iff₀ hmixed]
  unfold mixedRecognizer
  constructor <;> intro h <;> nlinarith

theorem mixed_recognizer_two (p uptake : ℝ) :
    mixedRecognizer 2 p uptake - (3*p^2 - 2*p^3) =
      2*p*(1-p)*(uptake-p) := by
  unfold mixedRecognizer
  ring

theorem recognizer_threshold (reach vote response : ℝ) (hr : 0 < reach) :
    0 < response * reach - vote ↔ vote / reach < response := by
  rw [div_lt_iff₀ hr]
  constructor <;> intro h <;> nlinarith

theorem small_hump_peak (p response : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hr : 0 < response) :
    3*response*p*(1-p)^2 ≤ 4*response/9 ∧
      (3*response*p*(1-p)^2 = 4*response/9 ↔ p = 1/3) := by
  have hid : 4/27 - p*(1-p)^2 = (3*p-1)^2*(4-3*p)/27 := by ring
  have hpos : 0 < 4-3*p := by linarith
  have hsq := sq_nonneg (3*p-1)
  have hb : 0 ≤ (3*p-1)^2*(4-3*p) := mul_nonneg hsq hpos.le
  constructor
  · nlinarith
  · constructor
    · intro heq
      have hz : (3*p-1)^2*(4-3*p) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · nlinarith [sq_eq_zero_iff.mp hz]
      · linarith
    · intro heq; subst p; ring

/-! Advocacy: these are conditional accounting identities, with no causal labels. -/
def advocateGain (mass plain changed : Cell → ℝ) : ℝ :=
  ∑ c, mass c * (changed c - plain c)

theorem advocate_ceiling (mass plain changed : Cell → ℝ)
    (hm : ∀ c, 0 ≤ mass c) (ha : ∀ c, changed c ≤ 1) :
    advocateGain mass plain changed ≤ ∑ c, mass c * (1-plain c) := by
  apply sum_le_sum
  intro c _
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (ha c) _) (hm c)

/-- The aggregate outside-rescue hypothesis is weaker than cellwise loss. -/
theorem advocate_rescue_ceiling (mass plain changed : Cell → ℝ)
    (hm : 0 ≤ mass .post) (ha : changed .post ≤ 1)
    (houtside : mass .keep * (changed .keep-plain .keep) +
      mass .absent * (changed .absent-plain .absent) ≤ 0) :
    advocateGain mass plain changed ≤ mass .post*(1-plain .post) := by
  unfold advocateGain
  rw [sum_cells]
  have h := mul_le_mul_of_nonneg_left (sub_le_sub_right ha (plain .post)) hm
  linarith

theorem nomination_identity (h uptake other baseline : ℝ) :
    h*uptake + (1-h)*other - baseline =
      h*(uptake-other) + (other-baseline) := by ring

theorem nomination_same_baseline (h uptake baseline : ℝ) :
    h*uptake + (1-h)*baseline - baseline = h*(uptake-baseline) := by ring

/-- The coupled stratum identity compares the same observed strata. -/
theorem coupled_nomination_identity {Z : Type*} [Fintype Z]
    (mass changed plain : Z → ℝ) :
    (∑ z, mass z*changed z) - (∑ z, mass z*plain z) =
      ∑ z, mass z*(changed z-plain z) := by
  simp [mul_sub, sum_sub_distrib]

theorem advocate_break_even (trigger share gain cost : ℝ)
    (ht : 0 < trigger) (hgc : 0 < gain+cost) :
    0 < trigger*(share*gain-(1-share)*cost) ↔ cost/(gain+cost) < share := by
  rw [mul_pos_iff_of_pos_left ht, div_lt_iff₀ hgc]
  constructor <;> intro h <;> nlinarith

theorem four_decider_polynomial (f : ℝ) :
    f^4 + 4*f^3*(1-f) + 3*f^2*(1-f)^2 = 3*f^2-2*f^3 := by ring

theorem correlated_uptake_differs :
    (1/4 : ℝ) ≠ 3*(1/4)^2 - 2*(1/4)^3 := by norm_num

theorem absent_rescue_ceiling_counterexample :
    advocateGain (fun c => if c = .absent then 1 else 0)
      (fun _ => 0) (fun _ => 1) = 1 := by
  rw [advocateGain, sum_cells]
  have hk : Cell.keep ≠ Cell.absent := by intro h; cases h
  have hp : Cell.post ≠ Cell.absent := by intro h; cases h
  simp [hk, hp]

end SEKernel.EpistemicPayoff
