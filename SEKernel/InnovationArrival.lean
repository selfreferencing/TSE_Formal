import SEKernel.FiniteProbability
import SEKernel.MutationBaseline

/-! Finite first-arrival laws. Conditional hazards are stated given the entire
preceding absence event. Appearance and later survival are separate events. -/
namespace SEKernel.InnovationArrival
open FiniteProbability
open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- No occurrence in the first `t` trials. -/
def avoids (hit : ℕ → Ω → Prop) (t : ℕ) (ω : Ω) : Prop :=
  ∀ j, j<t → ¬hit j ω

theorem avoids_zero (hit : ℕ → Ω → Prop) (ω : Ω) : avoids hit 0 ω := by
  intro j hj; omega

theorem avoids_succ (hit : ℕ → Ω → Prop) (t : ℕ) (ω : Ω) :
    avoids hit (t+1) ω ↔ avoids hit t ω ∧ ¬hit t ω := by
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h t (by omega)⟩
  · rintro ⟨h,ht⟩ j hj
    by_cases hlt : j<t
    · exact h j hlt
    · have : j=t := by omega
      simpa [this] using ht

/-- The conditional creation probability; only positive absence cells are used. -/
def conditionalCreation (L : Law Ω) (hit : ℕ → Ω → Prop) (t : ℕ) : ℝ :=
  by
    classical
    exact L.conditionalMean (fun ω => if hit t ω then 1 else 0) (avoids hit t)

theorem absence_partition (L : Law Ω) (hit : ℕ → Ω → Prop) (t : ℕ) :
    L.prob (avoids hit (t+1)) + L.prob (fun ω => avoids hit t ω ∧ hit t ω) =
      L.prob (avoids hit t) := by
  classical
  simp only [Law.prob, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : avoids hit t ω <;> by_cases hh : hit t ω <;>
    simp [avoids_succ,ha,hh]

theorem first_creation_mass (L : Law Ω) (hit : ℕ → Ω → Prop) (t : ℕ) :
    L.prob (avoids hit t)*conditionalCreation L hit t =
      L.prob (fun ω => avoids hit t ω ∧ hit t ω) := by
  classical
  unfold conditionalCreation
  rw [L.prob_mul_conditionalMean]
  unfold Law.cellExpect Law.expect Law1.mean Law.prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : avoids hit t ω <;> by_cases hh : hit t ω <;> simp [ha,hh]

/-- Conditional probability at least `u` gives an upper bound on absence. -/
theorem absence_le_of_conditional_lower (L : Law Ω) (hit : ℕ → Ω → Prop)
    (u : ℝ) (hu : 0≤u) (hu' : u≤1) (T : ℕ)
    (hh : ∀ t<T, 0<L.prob (avoids hit t) → u≤conditionalCreation L hit t) :
    L.prob (avoids hit T) ≤ (1-u)^T := by
  induction T with
  | zero => simp [Law.prob,avoids,L.total]
  | succ T ih =>
    have hprev : L.prob (avoids hit T) ≤ (1-u)^T := ih (fun t ht => hh t (by omega))
    have hp := L.prob_nonneg (avoids hit T)
    have hnew := L.prob_nonneg (avoids hit (T+1))
    have hpart := absence_partition L hit T
    have hmass := first_creation_mass L hit T
    have hlow : u*L.prob (avoids hit T) ≤ L.prob (fun ω => avoids hit T ω ∧ hit T ω) := by
      by_cases hz : L.prob (avoids hit T)=0
      · rw [hz,mul_zero]; exact L.prob_nonneg _
      · have hc := hh T (by omega) (lt_of_le_of_ne hp (Ne.symm hz))
        nlinarith
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_right hprev (sub_nonneg.mpr hu')
    nlinarith

/-- Conditional probability at most `u` gives a lower bound on absence. -/
theorem absence_ge_of_conditional_upper (L : Law Ω) (hit : ℕ → Ω → Prop)
    (u : ℝ) (hu : 0≤u) (hu' : u≤1) (T : ℕ)
    (hh : ∀ t<T, 0<L.prob (avoids hit t) → conditionalCreation L hit t≤u) :
    (1-u)^T ≤ L.prob (avoids hit T) := by
  induction T with
  | zero => simp [Law.prob,avoids,L.total]
  | succ T ih =>
    have hprev : (1-u)^T ≤ L.prob (avoids hit T) := ih (fun t ht => hh t (by omega))
    have hp := L.prob_nonneg (avoids hit T)
    have hpart := absence_partition L hit T
    have hmass := first_creation_mass L hit T
    have hupp : L.prob (fun ω => avoids hit T ω ∧ hit T ω) ≤ u*L.prob (avoids hit T) := by
      by_cases hz : L.prob (avoids hit T)=0
      · have hm := L.prob_mono (E := fun ω => avoids hit T ω ∧ hit T ω)
          (F := avoids hit T) (fun _ h => h.1)
        simpa [hz] using hm
      · have hc := hh T (by omega) (lt_of_le_of_ne hp (Ne.symm hz))
        nlinarith
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_right hprev (sub_nonneg.mpr hu')
    nlinarith

/-- Exact conditional hazard suffices; independence is unnecessary here. -/
theorem absence_eq_of_conditional (L : Law Ω) (hit : ℕ → Ω → Prop)
    (u : ℝ) (hu : 0≤u) (hu' : u≤1) (M T : ℕ)
    (hh : ∀ t<M*T, 0<L.prob (avoids hit t) → conditionalCreation L hit t=u) :
    L.prob (avoids hit (M*T)) = (1-u)^(M*T) := by
  apply le_antisymm
  · exact absence_le_of_conditional_lower L hit u hu hu' _ (fun t ht hp => (hh t ht hp).ge)
  · exact absence_ge_of_conditional_upper L hit u hu hu' _ (fun t ht hp => (hh t ht hp).le)

theorem one_sub_pow_le_mul (u : ℝ) (hu : 0≤u) (hu' : u≤1) (n : ℕ) :
    1-(1-u)^n ≤ (n : ℝ)*u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hp : (1-u)^n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hu') (by linarith)
    nlinarith

/-- First arrival by the horizon is bounded above by the number of trials times
an upper bound on conditional creation. It does not assert establishment. -/
theorem appearance_le_trials_mul (L : Law Ω) (hit : ℕ → Ω → Prop)
    (u : ℝ) (hu : 0≤u) (hu' : u≤1) (M T : ℕ)
    (hh : ∀ t<M*T, 0<L.prob (avoids hit t) → conditionalCreation L hit t≤u) :
    L.prob (fun ω => ¬avoids hit (M*T) ω) ≤ (M*T : ℕ)*u := by
  rw [L.prob_compl]
  have hs := absence_ge_of_conditional_upper L hit u hu hu' (M*T) hh
  have hb := one_sub_pow_le_mul u hu hu' (M*T)
  linarith

/-- Actual independently sampled mutation indicators, one per offspring and time. -/
def mutationTrials (u : ℝ) (hu : 0≤u) (hu' : u≤1) (M T : ℕ) : Law (Fin (M*T) → Bool) :=
  Law.pi (fun _ => MutationBaseline.bernoulli u hu hu')

theorem independent_no_appearance (u : ℝ) (hu : 0≤u) (hu' : u≤1) (M T : ℕ) :
    (mutationTrials u hu hu' M T).prob (fun z => ∀ j, z j=false) = (1-u)^(M*T) := by
  classical
  have h : (fun z : Fin (M*T) → Bool => if (∀ j, z j=false) then (1 : ℝ) else 0) =
      (fun z => ∏ j, if z j=false then (1 : ℝ) else 0) := by
    funext z
    simp only [Fintype.prod_boole]
    by_cases hz : ∀ j : Fin (M*T), z j=false <;> simp [hz]
  rw [← Law.expect_indicator, h]
  unfold mutationTrials
  rw [Law.expect_pi_prod _ (fun _ b => if b=false then (1 : ℝ) else 0)]
  simp [Law.expect, Law1.mean, MutationBaseline.bernoulli]

theorem independent_appearance (u : ℝ) (hu : 0≤u) (hu' : u≤1) (M T : ℕ) :
    (mutationTrials u hu hu' M T).prob (fun z => ¬∀ j, z j=false) = 1-(1-u)^(M*T) := by
  rw [Law.prob_compl, independent_no_appearance]

theorem independent_appearance_le (u : ℝ) (hu : 0≤u) (hu' : u≤1) (M T : ℕ) :
    (mutationTrials u hu hu' M T).prob (fun z => ¬∀ j, z j=false) ≤ (M*T : ℕ)*u := by
  rw [independent_appearance]
  exact one_sub_pow_le_mul u hu hu' _

/-- A present-at-horizon event must imply some earlier arrival. -/
theorem presence_le_appearance (L : Law Ω) (hit : ℕ → Ω → Prop) (t : ℕ)
    (present : Ω → Prop) (h : ∀ ω, present ω → ¬avoids hit t ω) :
    L.prob present ≤ L.prob (fun ω => ¬avoids hit t ω) := L.prob_mono h

/-- Zero-support preservation for the existing mutation-free replicator operator. -/
theorem selection_zero {G : Type*} [Fintype G] (x f : G → ℝ) (g : G) (hg : x g=0) :
    Law1.step x f g=0 := by simp [Law1.step,hg]

def selectionIter {G : Type*} [Fintype G] (x f : G → ℝ) : ℕ → G → ℝ
  | 0 => x
  | t+1 => Law1.step (selectionIter x f t) f

theorem selectionIter_zero {G : Type*} [Fintype G] (x f : G → ℝ) (g : G)
    (hg : x g=0) (t : ℕ) : selectionIter x f t g=0 := by
  induction t with
  | zero => exact hg
  | succ t ih => exact selection_zero _ _ _ ih

end
end SEKernel.InnovationArrival
