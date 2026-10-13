/-
First-label counting for a uniformly shuffled fixed ordered word.
The proof retains original position identities: swapping two active original
positions is a bijection of the permutation sample space. No conditional
uniformity or multinomial enumeration is assumed.
-/
import SEKernel.FirstAppearancePlurality

namespace SEKernel.Epistemic

open Finset
open SEKernel.FiniteProbability

/-- Explicit uniform law on a finite nonempty sample space. -/
noncomputable def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Law Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hc : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc

theorem uniformLaw_prob_equiv {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (e : Ω ≃ Ω) (E : Ω → Prop) :
    (uniformLaw Ω).prob (fun ω => E (e ω)) = (uniformLaw Ω).prob E := by
  classical
  unfold Law.prob uniformLaw
  exact e.sum_comp (fun ω => if E ω then (Fintype.card Ω : ℝ)⁻¹ else 0)

/-- Original position with smallest shuffled rank among active positions. -/
noncomputable def firstActive {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (π : Equiv.Perm (Fin N)) : Fin N :=
  π.symm ((S.image π).min' (hS.image π))

theorem firstActive_mem {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (π : Equiv.Perm (Fin N)) : firstActive S hS π ∈ S := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp ((S.image π).min'_mem (hS.image π))
  unfold firstActive
  rw [← he]
  simpa using hi

theorem firstActive_min {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (hi : i ∈ S) :
    π (firstActive S hS π) ≤ π i := by
  classical
  simp only [firstActive, Equiv.apply_symm_apply]
  exact (S.image π).min'_le (π i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem firstActive_eq_of_min {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (hi : i ∈ S)
    (hmin : ∀ j ∈ S, π i ≤ π j) : firstActive S hS π = i := by
  apply π.injective
  exact le_antisymm (firstActive_min S hS π i hi)
    (hmin _ (firstActive_mem S hS π))

theorem swap_mem_active {N : ℕ} (S : Finset (Fin N)) (i j : Fin N)
    (hi : i ∈ S) (hj : j ∈ S) (k : Fin N) :
    Equiv.swap i j k ∈ S ↔ k ∈ S := by
  classical
  by_cases hki : k = i
  · subst k
    simp [hi, hj]
  · by_cases hkj : k = j
    · subst k
      simp [hi, hj]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- Swapping active original identities swaps the selected original identity. -/
theorem firstActive_swap {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (i j : Fin N) (hi : i ∈ S) (hj : j ∈ S) (π : Equiv.Perm (Fin N)) :
    firstActive S hS ((Equiv.swap i j).trans π) =
      Equiv.swap i j (firstActive S hS π) := by
  apply firstActive_eq_of_min
  · exact (swap_mem_active S i j hi hj _).2 (firstActive_mem S hS π)
  · intro k hk
    simpa using firstActive_min S hS π (Equiv.swap i j k)
      ((swap_mem_active S i j hi hj k).2 hk)

/-- A permutation-sample-space bijection, retaining each original position. -/
noncomputable def swapOriginalPositions {N : ℕ} (i j : Fin N) :
    Equiv.Perm (Equiv.Perm (Fin N)) where
  toFun π := (Equiv.swap i j).trans π
  invFun π := (Equiv.swap i j).trans π
  left_inv π := by ext k; simp
  right_inv π := by ext k; simp

theorem firstActive_atom_equal {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (i j : Fin N) (hi : i ∈ S) (hj : j ∈ S) :
    (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => firstActive S hS π = i) =
      (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => firstActive S hS π = j) := by
  classical
  calc
    _ = (uniformLaw (Equiv.Perm (Fin N))).prob
        (fun π => firstActive S hS (swapOriginalPositions i j π) = i) :=
      (uniformLaw_prob_equiv (swapOriginalPositions i j) _).symm
    _ = _ := by
      congr 1
      funext π
      apply propext
      change firstActive S hS ((Equiv.swap i j).trans π) = i ↔ _
      rw [firstActive_swap S hS i j hi hj π]
      have he : Equiv.swap i j (firstActive S hS π) = Equiv.swap i j j ↔
          firstActive S hS π = j := (Equiv.swap i j).injective.eq_iff
      simpa only [Equiv.swap_apply_right] using he

/-- Finite pushforward probabilities sum over every output in a selected set. -/
theorem prob_mem_eq_sum {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    [DecidableEq Λ] (L : Law Ω) (f : Ω → Λ) (S : Finset Λ) :
    L.prob (fun ω => f ω ∈ S) = ∑ i ∈ S, L.prob (fun ω => f ω = i) := by
  classical
  unfold Law.prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hf : f ω ∈ S
  · simp only [hf, ↓reduceIte]
    rw [Finset.sum_eq_single (f ω)]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · exact fun hn => (hn hf).elim
  · simp only [hf, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hne : f ω ≠ i := fun he => hf (he ▸ hi)
    simp [hne]

/-- Every active original position is first with probability 1 / |S|. -/
theorem firstActive_uniform {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (i : Fin N) (hi : i ∈ S) :
    (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => firstActive S hS π = i) =
      1 / (S.card : ℝ) := by
  classical
  let L := uniformLaw (Equiv.Perm (Fin N))
  have htotal : (∑ j ∈ S, L.prob (fun π => firstActive S hS π = j)) = 1 := by
    rw [← prob_mem_eq_sum]
    have he : (fun π => firstActive S hS π ∈ S) = (fun _ => True) := by
      funext π
      exact propext ⟨fun _ => trivial, fun _ => firstActive_mem S hS π⟩
    rw [he, L.prob_true]
  have hequal : (∑ j ∈ S, L.prob (fun π => firstActive S hS π = j)) =
      (S.card : ℝ) * L.prob (fun π => firstActive S hS π = i) := by
    calc
      _ = ∑ _j ∈ S, L.prob (fun π => firstActive S hS π = i) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact firstActive_atom_equal S hS j i hj hi
      _ = _ := by simp
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hS.card_pos)
  apply (eq_div_iff hc).2
  rw [hequal] at htotal
  simpa only [mul_comm] using htotal

/-- First-active-label counting for a uniformly shuffled fixed labelled word. -/
theorem firstActive_label_probability {N : ℕ} {A : Type*} [DecidableEq A]
    (z : Fin N → A) (S : Finset (Fin N)) (hS : S.Nonempty) (a : A) :
    (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => z (firstActive S hS π) = a) =
      ((S.filter (fun i => z i = a)).card : ℝ) / (S.card : ℝ) := by
  classical
  have he : (fun π => z (firstActive S hS π) = a) =
      (fun π => firstActive S hS π ∈ S.filter (fun i => z i = a)) := by
    funext π
    apply propext
    simp only [Finset.mem_filter, firstActive_mem, true_and]
  rw [he, prob_mem_eq_sum]
  calc
    _ = ∑ _i ∈ S.filter (fun i => z i = a), (1 / (S.card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact firstActive_uniform S hS i (Finset.mem_filter.mp hi).1
    _ = _ := by simp [div_eq_mul_inv]

/-- Original positions bearing a label in T. -/
def activePositions {N : ℕ} {A : Type*} [DecidableEq A]
    (z : Fin N → A) (T : Finset A) : Finset (Fin N) :=
  Finset.univ.filter fun i => z i ∈ T

/-- The shuffled word, with π recording original-position to new-position ranks. -/
def shuffledWord {N : ℕ} {A : Type*} (z : Fin N → A) (π : Equiv.Perm (Fin N)) : Fin N → A :=
  fun k => z (π.symm k)

/-- The first T-labelled entry of the actual shuffled word. -/
noncomputable def firstTLabel {N : ℕ} {A : Type*} [DecidableEq A]
    (z : Fin N → A) (T : Finset A) (hT : (activePositions z T).Nonempty)
    (π : Equiv.Perm (Fin N)) : A := z (firstActive (activePositions z T) hT π)

theorem firstTLabel_semantics {N : ℕ} {A : Type*} [DecidableEq A]
    (z : Fin N → A) (T : Finset A) (hT : (activePositions z T).Nonempty)
    (π : Equiv.Perm (Fin N)) :
    ∃ k : Fin N, shuffledWord z π k = firstTLabel z T hT π ∧
      shuffledWord z π k ∈ T ∧
      ∀ j, shuffledWord z π j ∈ T → k ≤ j := by
  let i := firstActive (activePositions z T) hT π
  refine ⟨π i, ?_, ?_, ?_⟩
  · simp [shuffledWord, firstTLabel, i]
  · simp only [shuffledWord, Equiv.symm_apply_apply]
    exact (Finset.mem_filter.mp (firstActive_mem (activePositions z T) hT π)).2
  · intro j hj
    have hm : π.symm j ∈ activePositions z T := by
      simp only [activePositions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj
    simpa [i] using firstActive_min (activePositions z T) hT π (π.symm j) hm

/-- The requested u_a/L counting formula under the uniform permutation law. -/
theorem firstTLabel_probability {N : ℕ} {A : Type*} [DecidableEq A]
    (z : Fin N → A) (T : Finset A) (hT : (activePositions z T).Nonempty)
    (a : A) (ha : a ∈ T) :
    (uniformLaw (Equiv.Perm (Fin N))).prob (fun π => firstTLabel z T hT π = a) =
      ((Finset.univ.filter (fun i => z i = a)).card : ℝ) /
        ((activePositions z T).card : ℝ) := by
  classical
  unfold firstTLabel
  rw [firstActive_label_probability]
  have hf : (activePositions z T).filter (fun i => z i = a) =
      Finset.univ.filter (fun i => z i = a) := by
    ext i
    simp only [activePositions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_right_of_imp (fun hi => hi ▸ ha)
  rw [hf]

/-- Shuffling changes positions while retaining every original label count. -/
theorem shuffledWord_labelCount {N : ℕ} {A : Type*} [DecidableEq A]
    (z : OrderedWord N A) (π : Equiv.Perm (Fin N)) (a : Option A) :
    labelCount (shuffledWord z π) a = labelCount z a := by
  rw [labelCount_eq_sum, labelCount_eq_sum]
  exact π.symm.sum_comp (fun i => if z i = a then 1 else 0)

end SEKernel.Epistemic
