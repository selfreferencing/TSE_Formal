/-
Count-profile combinatorics for actual finite words. The multinomial cardinal
is obtained from positional permutations and their label-preserving stabilizer.
-/
import SEKernel.FirstTiedLabelCounting
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Choose.Multinomial

namespace SEKernel.Epistemic

open Finset
open scoped Nat

/-- Number of occurrences of a symbol, including an abstention symbol if present. -/
noncomputable def wordCount {N : ℕ} {B : Type*} (z : Fin N → B) (b : B) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => z i = b).card

/-- Actual count vector of a finite ordered word. -/
noncomputable def countProfile {N : ℕ} {B : Type*} (z : Fin N → B) : B → ℕ :=
  wordCount z

/-- The finite fiber of an actual count vector. -/
noncomputable def countFiber {N : ℕ} {B : Type*} [Fintype B] (c : B → ℕ) :
    Finset (Fin N → B) := by
  classical
  exact Finset.univ.filter fun z => countProfile z = c

theorem wordCount_eq_labelCount {N : ℕ} {A : Type*} (z : OrderedWord N A) (a : Option A) :
    wordCount z a = labelCount z a := by
  classical
  unfold wordCount labelCount
  congr 1
  ext i
  simp

theorem wordCount_eq_card_subtype {N : ℕ} {B : Type*} (z : Fin N → B) (b : B) :
    wordCount z b = Nat.card {i : Fin N // z i = b} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem sum_wordCount {N : ℕ} {B : Type*} [Fintype B] (z : Fin N → B) :
    ∑ b, wordCount z b = N := by
  classical
  simpa [wordCount] using
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ z)

theorem wordCount_comp_equiv {N : ℕ} {B : Type*} (z : Fin N → B)
    (π : Equiv.Perm (Fin N)) (b : B) : wordCount (z ∘ π) b = wordCount z b := by
  classical
  rw [wordCount_eq_card_subtype, wordCount_eq_card_subtype]
  exact Nat.card_congr (Equiv.subtypeEquiv π fun i => Iff.rfl)

/-- Equal count vectors are connected by a positional permutation preserving all labels. -/
theorem exists_perm_of_countProfile_eq {N : ℕ} {B : Type*}
    (z w : Fin N → B) (h : countProfile z = countProfile w) :
    ∃ π : Equiv.Perm (Fin N), z ∘ π = w := by
  classical
  let e : ∀ b, {i : Fin N // w i = b} ≃ {i : Fin N // z i = b} := fun b =>
    Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      rw [← wordCount_eq_card_subtype w b, ← wordCount_eq_card_subtype z b]
      exact (congrFun h b).symm)
  exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩

/-- Positional permutation orbits are precisely actual count-profile fibers. -/
theorem mem_count_orbit_iff {N : ℕ} {B : Type*} (z w : Fin N → B) :
    w ∈ MulAction.orbit (Equiv.Perm (Fin N))ᵈᵐᵃ z ↔ countProfile w = countProfile z := by
  classical
  constructor
  · rintro ⟨π, rfl⟩
    funext b
    exact wordCount_comp_equiv z (DomMulAct.mk.symm π) b
  · intro h
    obtain ⟨π, hπ⟩ := exists_perm_of_countProfile_eq z w h.symm
    exact ⟨DomMulAct.mk π, hπ⟩

/-- A count profile and its label-preserving positional permutations partition all permutations. -/
theorem countFiber_card_mul_factorials {N : ℕ} {B : Type*} [Fintype B]
    (z : Fin N → B) :
    (countFiber (countProfile z) (N := N)).card * ∏ b, (wordCount z b)! = N ! := by
  classical
  letI : Fintype (Equiv.Perm (Fin N))ᵈᵐᵃ :=
    Fintype.ofEquiv (Equiv.Perm (Fin N)) DomMulAct.mk
  letI : Fintype (MulAction.stabilizer (Equiv.Perm (Fin N))ᵈᵐᵃ z) := Fintype.ofFinite _
  have ho : Fintype.card (MulAction.orbit (Equiv.Perm (Fin N))ᵈᵐᵃ z) =
      (countFiber (countProfile z) (N := N)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, countFiber,
      mem_count_orbit_iff]
  have hs : Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin N))ᵈᵐᵃ z) =
      ∏ b, (wordCount z b)! := by
    calc
      _ = Fintype.card {π : Equiv.Perm (Fin N) // z ∘ π = z} :=
        Fintype.card_congr (Equiv.subtypeEquiv DomMulAct.mk.symm fun _ =>
          DomMulAct.mem_stabilizer_iff)
      _ = _ := by
        rw [DomMulAct.stabilizer_card]
        apply Finset.prod_congr rfl
        intro b _
        rw [wordCount_eq_card_subtype, Nat.card_eq_fintype_card]
  have hg := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (Equiv.Perm (Fin N))ᵈᵐᵃ z
  rw [ho, hs] at hg
  simpa only [Fintype.card_congr DomMulAct.mk.symm, Fintype.card_perm,
    Fintype.card_fin] using hg

/-- The number of actual ordered words with a fixed realized profile is multinomial. -/
theorem countFiber_card {N : ℕ} {B : Type*} [Fintype B] (z : Fin N → B) :
    (countFiber (countProfile z) (N := N)).card = Nat.multinomial Finset.univ (countProfile z) := by
  classical
  apply Nat.eq_of_mul_eq_mul_right (Finset.prod_pos fun b _ => Nat.factorial_pos _)
  rw [countFiber_card_mul_factorials]
  simpa only [countProfile, sum_wordCount, mul_comm] using
    (Nat.multinomial_spec Finset.univ (countProfile z)).symm

/-- Every nonnegative integer vector summing to the word length is realized by a word. -/
theorem exists_word_of_sum_counts {N : ℕ} {B : Type*} [Fintype B]
    (c : B → ℕ) (hc : ∑ b, c b = N) : ∃ z : Fin N → B, countProfile z = c := by
  classical
  let e : Fin N ≃ (Σ b, Fin (c b)) := Fintype.equivOfCardEq (by simp [hc])
  refine ⟨fun i => (e i).1, ?_⟩
  funext b
  rw [countProfile, wordCount_eq_card_subtype]
  let eb : {i : Fin N // (e i).1 = b} ≃ Fin (c b) :=
    (Equiv.subtypeEquiv e fun i => Iff.rfl).trans (Equiv.sigmaSubtype (β := fun b => Fin (c b)) b)
  exact (Nat.card_congr eb).trans (Nat.card_fin _)

/-- Shuffling positions leaves the whole count profile unchanged. -/
theorem shuffledWord_countProfile {N : ℕ} {B : Type*}
    (z : Fin N → B) (π : Equiv.Perm (Fin N)) :
    countProfile (shuffledWord z π) = countProfile z := by
  funext b
  exact wordCount_comp_equiv z π.symm b

end SEKernel.Epistemic
