/-
Close-out pass for the Chile extension's selection layer (Doc A/B, Part B).

This module derives the tied conditional survivor COUNTS of the three
implemented tie kernels of `SEKernel.NoisySelection` (uniform slot
permutation, protected incumbents, uniform genotype permutation), closes the
`T_A` input of `topS_master` / `implemented_topS_master`, instantiates the
pooled master formula for each implemented law, realizes the 1/8 and
-47/30000 arithmetic facts on concrete rosters, score laws and the actual
sort, and proves the identical-outcome incumbent mutation floor.

Every survivor set below is produced by the actual deterministic
lexicographic sort `lexSurvivors`; no survivor set is supplied by hypothesis.
-/
import SEKernel.NoisySelection
import SEKernel.MutationBaseline
import SEKernel.ScorePooling
import SEKernel.PairedScores

namespace SEKernel.Closeout.Selection

open Finset SEKernel.FiniteProbability SEKernel.NoisySelection
open scoped Classical

/-! ## 1. Structure of the actual sort -/

section ActualSort

/-- Every retained slot strictly precedes every discarded slot in the
lexicographic record order used by the implementation. -/
theorem lexSurvivors_cross {P S : ℕ} (hSP : S ≤ P) (score : Fin P → ℝ)
    (key : Fin P → ℤ) {i j : Fin P} (hi : i ∈ (lexSurvivors hSP score key).val)
    (hj : j ∉ (lexSurvivors hSP score key).val) :
    rankRecord score key i < rankRecord score key j := by
  have hi' : i ∈ (rankingList score key).take S := by simpa [lexSurvivors] using hi
  have hj' : j ∉ (rankingList score key).take S := by simpa [lexSurvivors] using hj
  have hjdrop : j ∈ (rankingList score key).drop S := by
    have hall := rankingList_mem score key j
    rw [← List.take_append_drop S (rankingList score key), List.mem_append] at hall
    exact hall.resolve_left hj'
  have hpair := rankingList_lexicographic score key
  rw [← List.take_append_drop S (rankingList score key), List.pairwise_append] at hpair
  have hrel := hpair.2.2 i hi' j hjdrop
  have hne : i ≠ j := fun h => hj (h ▸ hi)
  exact lt_of_le_of_ne hrel (fun h => hne (rankRecord_injective score key h))

/-- Two equal-size sets that each strictly precede their complements in one
linear order coincide. -/
theorem cross_set_unique {ι α : Type*} [LinearOrder α] (rec : ι → α)
    (B C : Finset ι) (hcard : B.card = C.card)
    (hB : ∀ i ∈ B, ∀ j ∉ B, rec i < rec j)
    (hC : ∀ i ∈ C, ∀ j ∉ C, rec i < rec j) : B = C := by
  apply Finset.eq_of_subset_of_card_le _ hcard.ge
  intro i hi
  by_contra hiC
  have hex : ∃ j ∈ C, j ∉ B := by
    by_contra hno
    have hsub : C ⊆ B := by
      intro j hj
      by_contra hjB
      exact hno ⟨j, hj, hjB⟩
    have heq := Finset.eq_of_subset_of_card_le hsub hcard.le
    exact hiC (heq ▸ hi)
  obtain ⟨j, hjC, hjB⟩ := hex
  exact lt_asymm (hB i hi j hjB) (hC j hjC i hiC)

/-- Linear-order form of `higher_target_count`: a target block that strictly
precedes its complement keeps exactly `min |B| |target|` slots of `B`. -/
theorem cross_target_count {ι α : Type*} [LinearOrder α] (rec : ι → α)
    (target B : Finset ι) (htop : ∀ i ∈ B, ∀ j ∉ B, rec i < rec j)
    (hstrict : ∀ i ∈ target, ∀ j ∉ target, rec i < rec j) :
    (B ∩ target).card = min B.card target.card := by
  have hle : (B ∩ target).card ≤ min B.card target.card :=
    le_min (Finset.card_le_card Finset.inter_subset_left)
      (Finset.card_le_card Finset.inter_subset_right)
  apply le_antisymm hle
  by_contra hn
  have hlt : (B ∩ target).card < min B.card target.card := lt_of_not_ge hn
  have hmiss : ∃ i ∈ target, i ∉ B := by
    by_contra hno
    have hsub : target ⊆ B := by
      intro i hi
      by_contra h
      exact hno ⟨i, hi, h⟩
    rw [Finset.inter_eq_right.mpr hsub] at hlt
    omega
  have hout : ∃ j ∈ B, j ∉ target := by
    by_contra hno
    have hsub : B ⊆ target := by
      intro i hi
      by_contra h
      exact hno ⟨i, hi, h⟩
    rw [Finset.inter_eq_left.mpr hsub] at hlt
    omega
  obtain ⟨i, hi, hiB⟩ := hmiss
  obtain ⟨j, hj, hjt⟩ := hout
  exact lt_asymm (htop j hj i hiB) (hstrict i hi j hjt)

theorem rankRecord_lt_of_score {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ)
    {i j : Fin P} (h : score j < score i) :
    rankRecord score key i < rankRecord score key j := by
  unfold rankRecord
  rw [Prod.Lex.toLex_lt_toLex]
  left
  simpa using h

theorem rankRecord_lt_of_key {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ)
    {i j : Fin P} (hs : score i = score j) (hk : key i < key j) :
    rankRecord score key i < rankRecord score key j := by
  unfold rankRecord
  rw [Prod.Lex.toLex_lt_toLex]
  right
  refine ⟨by simp [hs], ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  left
  exact hk

theorem rankRecord_const_lt_of_key {P : ℕ} (c : ℝ) (key : Fin P → ℤ)
    {i j : Fin P} (hk : key i < key j) :
    rankRecord (fun _ => c) key i < rankRecord (fun _ => c) key j :=
  rankRecord_lt_of_key _ key (i := i) (j := j) rfl hk

/-- With a constant score, the record order is the (key, slot) order, for
every value of the constant. -/
theorem rankRecord_const_lt_iff {P : ℕ} (c c' : ℝ) (key : Fin P → ℤ) (i j : Fin P) :
    rankRecord (fun _ => c) key i < rankRecord (fun _ => c) key j ↔
      rankRecord (fun _ => c') key i < rankRecord (fun _ => c') key j := by
  unfold rankRecord
  simp only [Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or]

/-- A tied selection does not depend on the common tied score value. -/
theorem lexSurvivors_const {P S : ℕ} (hSP : S ≤ P) (c c' : ℝ) (key : Fin P → ℤ) :
    (lexSurvivors hSP (fun _ => c) key).val = (lexSurvivors hSP (fun _ => c') key).val := by
  apply cross_set_unique (rankRecord (fun _ => c) key)
  · rw [(lexSurvivors hSP _ key).property, (lexSurvivors hSP _ key).property]
  · intro i hi j hj
    exact lexSurvivors_cross hSP _ key hi hj
  · intro i hi j hj
    exact (rankRecord_const_lt_iff c' c key i j).1 (lexSurvivors_cross hSP _ key hi hj)

/-- If every copy of `g` strictly precedes every other slot in record order,
the actual sort keeps `min S K` copies of `g`. -/
theorem count_of_precedes {P S : ℕ} {G : Type*} (hSP : S ≤ P)
    (score : Fin P → ℝ) (key : Fin P → ℤ) (roster : Fin P → G) (g : G)
    (hprec : ∀ i j, roster i = g → roster j ≠ g →
      rankRecord score key i < rankRecord score key j) :
    survivorCount roster (lexSurvivors hSP score key) g =
      min S (Finset.univ.filter fun i => roster i = g).card := by
  have h := cross_target_count (rankRecord score key)
    (Finset.univ.filter fun i => roster i = g) (lexSurvivors hSP score key).val
    (fun i hi j hj => lexSurvivors_cross hSP score key hi hj)
    (fun i hi j hj => hprec i j (by simpa using hi) (by simpa using hj))
  rw [(lexSurvivors hSP score key).property] at h
  simpa only [survivorCount, Finset.inter_filter, Finset.inter_univ] using h

/-- If every other slot strictly precedes every copy of `g`, the actual sort
keeps `S - (P - K)` copies of `g` (natural subtraction). -/
theorem count_of_follows {P S : ℕ} {G : Type*} (hSP : S ≤ P)
    (score : Fin P → ℝ) (key : Fin P → ℤ) (roster : Fin P → G) (g : G)
    (hfol : ∀ i j, roster i ≠ g → roster j = g →
      rankRecord score key i < rankRecord score key j) :
    survivorCount roster (lexSurvivors hSP score key) g =
      S - (P - (Finset.univ.filter fun i => roster i = g).card) := by
  set B := (lexSurvivors hSP score key).val
  have h := cross_target_count (rankRecord score key)
    (Finset.univ.filter fun i => roster i ≠ g) B
    (fun i hi j hj => lexSurvivors_cross hSP score key hi hj)
    (fun i hi j hj => hfol i j (by simpa using hi) (by simpa using hj))
  have hB : B.card = S := (lexSurvivors hSP score key).property
  have hboth := Finset.card_filter_add_card_filter_not (s := B) (fun i => roster i = g)
  have hpop := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin P => roster i = g)
  have h' : (B.filter (fun i => roster i ≠ g)).card =
      min S (Finset.univ.filter fun i => roster i ≠ g).card := by
    simpa only [Finset.inter_filter, Finset.inter_univ, hB] using h
  simp only [Finset.card_univ, Fintype.card_fin] at hpop
  change (B.filter (fun i => roster i = g)).card = _
  simp only [ne_eq] at h' hboth hpop
  omega

end ActualSort

/-! ## 2. Tied conditional counts of the three implemented key kernels -/

section TieKernels

theorem pointLaw_expect {Ω : Type*} [Fintype Ω] (ω : Ω) (f : Ω → ℝ) :
    (pointLaw ω).expect f = f ω := by
  simp [pointLaw, Law.expect, Law1.mean]

/-- The key of `slotTieSelectionLaw`. -/
def slotKey {P : ℕ} (π : Equiv.Perm (Fin P)) (i : Fin P) : ℤ := ((π i : ℕ) : ℤ)

theorem slotTieSelectionLaw_eq {P S : ℕ} (hSP : S ≤ P) (score : Fin P → ℝ) :
    slotTieSelectionLaw hSP score =
      tieSelectionLaw hSP score slotKey (uniformLaw (Equiv.Perm (Fin P))) := rfl

/-- The key of `incumbentSelectionLaw`: more evaluations rank first. -/
def incumbentKey {P : ℕ} (evaluations : Fin P → ℕ) (i : Fin P) : ℤ :=
  -(evaluations i : ℤ)

theorem incumbentSelectionLaw_eq {P S : ℕ} (hSP : S ≤ P) (score : Fin P → ℝ)
    (evaluations : Fin P → ℕ) :
    incumbentSelectionLaw hSP score evaluations =
      tieSelectionLaw hSP score (fun _ : Unit => incumbentKey evaluations) (pointLaw ()) :=
  rfl

/-- The key of `genotypeTieSelectionLaw`: all copies inherit their genotype's rank. -/
noncomputable def genotypeKey {P : ℕ} {G : Type*} [Fintype G] (roster : Fin P → G)
    (π : Equiv.Perm (Fin (Fintype.card G))) (i : Fin P) : ℤ :=
  ((π (Fintype.equivFin G (roster i)) : ℕ) : ℤ)

theorem genotypeTieSelectionLaw_eq {P S : ℕ} {G : Type*} [Fintype G] (hSP : S ≤ P)
    (score : Fin P → ℝ) (roster : Fin P → G) :
    genotypeTieSelectionLaw hSP score roster =
      tieSelectionLaw hSP score (genotypeKey roster)
        (uniformLaw (Equiv.Perm (Fin (Fintype.card G)))) := rfl

/-- Under a complete score tie and slot permutation `π`, the actual sort keeps
exactly the slots whose permuted index is below `S`. -/
theorem slot_tied_survivors {P S : ℕ} (hSP : S ≤ P) (c : ℝ) (π : Equiv.Perm (Fin P)) :
    (lexSurvivors hSP (fun _ => c) (slotKey π)).val =
      Finset.univ.filter (fun i => ((π i : ℕ)) < S) := by
  apply cross_set_unique (rankRecord (fun _ => c) (slotKey π))
  · rw [(lexSurvivors hSP _ _).property]
    have h1 : (Finset.univ.filter fun i : Fin P => ((π i : ℕ)) < S).card =
        (Finset.univ.filter fun k : Fin P => (k : ℕ) < S).card := by
      simp only [Finset.card_filter]
      exact Equiv.sum_comp π (fun k : Fin P => if (k : ℕ) < S then 1 else 0)
    rw [h1, Fin.card_filter_val_lt, Nat.min_eq_right hSP]
  · intro i hi j hj
    exact lexSurvivors_cross hSP _ _ hi hj
  · intro i hi j hj
    apply rankRecord_const_lt_of_key _ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi hj
    unfold slotKey
    exact_mod_cast lt_of_lt_of_le hi hj

/-- **List-order ties (the referee's fourth kernel).** With a constant tie key,
a complete tie keeps exactly the first `S` list positions, so `T_A` is the
number of copies of `g` among slots `0..S-1`. -/
theorem listOrder_tied_survivors {P S : ℕ} (hSP : S ≤ P) (c : ℝ) (k : ℤ) :
    (lexSurvivors hSP (fun _ => c) (fun _ => k)).val =
      Finset.univ.filter (fun i : Fin P => (i : ℕ) < S) := by
  apply cross_set_unique (rankRecord (fun _ => c) (fun _ => k))
  · rw [(lexSurvivors hSP _ _).property, Fin.card_filter_val_lt, Nat.min_eq_right hSP]
  · intro i hi j hj
    exact lexSurvivors_cross hSP _ _ hi hj
  · intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi hj
    unfold rankRecord
    rw [Prod.Lex.toLex_lt_toLex]
    right
    refine ⟨rfl, ?_⟩
    rw [Prod.Lex.toLex_lt_toLex]
    right
    exact ⟨rfl, Fin.lt_def.mpr (lt_of_lt_of_le hi hj)⟩

theorem listOrder_tied_count {P S : ℕ} {G : Type*} (hSP : S ≤ P) (c : ℝ) (k : ℤ)
    (roster : Fin P → G) (g : G) :
    survivorCount roster (lexSurvivors hSP (fun _ => c) (fun _ => k)) g =
      (Finset.univ.filter (fun i : Fin P => (i : ℕ) < S ∧ roster i = g)).card := by
  unfold survivorCount
  rw [listOrder_tied_survivors, Finset.filter_filter]

/-- Each coordinate of a uniform random permutation is uniform. -/
theorem uniform_perm_coord {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (φ : ι → ℝ) (i : ι) :
    (uniformLaw (Equiv.Perm ι)).expect (fun π => φ (π i)) =
      (∑ k, φ k) / Fintype.card ι := by
  have hswap : ∀ j, (∑ π : Equiv.Perm ι, φ (π j)) = ∑ π : Equiv.Perm ι, φ (π i) := by
    intro j
    have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap i j))
      (fun π : Equiv.Perm ι => φ (π i))
    simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h
  have htot : (Fintype.card ι : ℝ) * (∑ π : Equiv.Perm ι, φ (π i)) =
      (Fintype.card (Equiv.Perm ι) : ℝ) * ∑ k, φ k := by
    calc (Fintype.card ι : ℝ) * (∑ π : Equiv.Perm ι, φ (π i))
        = ∑ j : ι, ∑ π : Equiv.Perm ι, φ (π j) := by
          rw [Finset.sum_congr rfl (fun j _ => hswap j)]
          simp
      _ = ∑ π : Equiv.Perm ι, ∑ j, φ (π j) := Finset.sum_comm
      _ = ∑ π : Equiv.Perm ι, ∑ k, φ k := by
          apply Finset.sum_congr rfl
          intro π _
          exact Equiv.sum_comp π φ
      _ = _ := by simp
  rw [uniform_expect]
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  linear_combination htot

/-- **Uniform slot ties (T_A = S x).** Conditional on a complete tie, the
expected number of retained copies of `g` under the uniform slot-permutation
kernel is `S * (K / P)`. -/
theorem slot_tied_count {P S : ℕ} {G : Type*} (hSP : S ≤ P) (hP : 0 < P) (c : ℝ)
    (roster : Fin P → G) (g : G) :
    (uniformLaw (Equiv.Perm (Fin P))).expect
      (fun π => (survivorCount roster (lexSurvivors hSP (fun _ => c) (slotKey π)) g : ℝ)) =
      (S : ℝ) * (((Finset.univ.filter fun i => roster i = g).card : ℝ) / P) := by
  have hcount : ∀ π : Equiv.Perm (Fin P),
      (survivorCount roster (lexSurvivors hSP (fun _ => c) (slotKey π)) g : ℝ) =
        ∑ i, (if roster i = g then (1:ℝ) else 0) *
          (if ((π i : ℕ)) < S then 1 else 0) := by
    intro π
    unfold survivorCount
    rw [slot_tied_survivors, Finset.filter_filter, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    by_cases h1 : roster i = g <;> by_cases h2 : ((π i : ℕ)) < S <;> simp [h1, h2]
  simp_rw [hcount]
  rw [Law.expect_sum]
  simp_rw [Law.expect_const_mul]
  haveI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  have hcoord : ∀ i : Fin P, (uniformLaw (Equiv.Perm (Fin P))).expect
      (fun π => if ((π i : ℕ)) < S then (1:ℝ) else 0) = (S : ℝ) / P := by
    intro i
    rw [uniform_perm_coord (fun k : Fin P => if (k : ℕ) < S then (1:ℝ) else 0) i]
    rw [Finset.sum_boole, Fin.card_filter_val_lt, Nat.min_eq_right hSP]
    simp
  simp_rw [hcoord]
  rw [← Finset.sum_mul, Finset.sum_boole]
  ring

/-- **Protected incumbent A (T_A = H).** If every copy of `g` has strictly
more evaluations than every other slot, a complete tie keeps `min S K`. -/
theorem incumbent_tied_count_A {P S : ℕ} {G : Type*} (hSP : S ≤ P) (c : ℝ)
    (evaluations : Fin P → ℕ) (roster : Fin P → G) (g : G)
    (hinc : ∀ i j, roster i = g → roster j ≠ g → evaluations j < evaluations i) :
    survivorCount roster (lexSurvivors hSP (fun _ => c) (incumbentKey evaluations)) g =
      min S (Finset.univ.filter fun i => roster i = g).card :=
  count_of_precedes hSP _ _ roster g (fun i j hi hj =>
    rankRecord_const_lt_of_key _ _ (by
      have := hinc i j hi hj
      unfold incumbentKey
      omega))

/-- **Protected incumbent B (T_A = L).** If every other slot has strictly
more evaluations than every copy of `g`, a complete tie keeps `S - (P - K)`. -/
theorem incumbent_tied_count_B {P S : ℕ} {G : Type*} (hSP : S ≤ P) (c : ℝ)
    (evaluations : Fin P → ℕ) (roster : Fin P → G) (g : G)
    (hinc : ∀ i j, roster i ≠ g → roster j = g → evaluations j < evaluations i) :
    survivorCount roster (lexSurvivors hSP (fun _ => c) (incumbentKey evaluations)) g =
      S - (P - (Finset.univ.filter fun i => roster i = g).card) :=
  count_of_follows hSP _ _ roster g (fun i j hi hj =>
    rankRecord_const_lt_of_key _ _ (by
      have := hinc i j hi hj
      unfold incumbentKey
      omega))

/-- **Fair genotype-block coin (T_A = (H+L)/2).** With exactly two genotypes
present, a complete tie under the uniform genotype-permutation kernel keeps
`(min S K + (S - (P - K)))/2` copies of `g` in expectation. -/
theorem genotype_tied_count {P S : ℕ} {G : Type*} [Fintype G] (hSP : S ≤ P) (c : ℝ)
    (roster : Fin P → G) (g h : G) (hgh : g ≠ h)
    (hbin : ∀ i, roster i = g ∨ roster i = h) :
    (uniformLaw (Equiv.Perm (Fin (Fintype.card G)))).expect
      (fun π => (survivorCount roster
        (lexSurvivors hSP (fun _ => c) (genotypeKey roster π)) g : ℝ)) =
      (((min S (Finset.univ.filter fun i => roster i = g).card : ℕ) : ℝ) +
        ((S - (P - (Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ)) / 2 := by
  set U := uniformLaw (Equiv.Perm (Fin (Fintype.card G)))
  set a := Fintype.equivFin G g
  set b := Fintype.equivFin G h
  have hab : a ≠ b := fun he => hgh ((Fintype.equivFin G).injective he)
  have hsym : U.expect (fun π => if π b < π a then (1:ℝ) else 0) =
      U.expect (fun π => if π a < π b then (1:ℝ) else 0) := by
    have := expect_equiv U (Equiv.mulRight (Equiv.swap a b)) (fun _ => rfl)
      (fun π => if π a < π b then (1:ℝ) else 0)
    simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] using this
  have hsum : U.expect (fun π => if π a < π b then (1:ℝ) else 0) +
      U.expect (fun π => if π b < π a then (1:ℝ) else 0) = 1 := by
    rw [← Law.expect_add]
    have hfun : (fun π : Equiv.Perm (Fin (Fintype.card G)) =>
        (if π a < π b then (1:ℝ) else 0) + (if π b < π a then 1 else 0)) = fun _ => 1 := by
      funext π
      have hne : π a ≠ π b := fun he => hab (π.injective he)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · simp [hlt, not_lt_of_gt hlt]
      · simp [hlt, not_lt_of_gt hlt]
    rw [hfun, Law.expect_const]
  have hkey : ∀ π i, roster i = g → genotypeKey roster π i = ((π a : ℕ) : ℤ) := by
    intro π i hi
    simp [genotypeKey, hi, a]
  have hkey' : ∀ π i, roster i ≠ g → genotypeKey roster π i = ((π b : ℕ) : ℤ) := by
    intro π i hi
    have : roster i = h := (hbin i).resolve_left hi
    simp [genotypeKey, this, b]
  have hcount : ∀ π : Equiv.Perm (Fin (Fintype.card G)),
      (survivorCount roster (lexSurvivors hSP (fun _ => c) (genotypeKey roster π)) g : ℝ) =
        ((min S (Finset.univ.filter fun i => roster i = g).card : ℕ) : ℝ) *
            (if π a < π b then 1 else 0) +
          ((S - (P - (Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) *
            (if π b < π a then 1 else 0) := by
    intro π
    have hne : π a ≠ π b := fun he => hab (π.injective he)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [count_of_precedes hSP _ _ roster g (fun i j hi hj =>
        rankRecord_const_lt_of_key _ _ (by
          rw [hkey π i hi, hkey' π j hj]
          exact_mod_cast hlt))]
      simp [hlt, not_lt_of_gt hlt]
    · rw [count_of_follows hSP _ _ roster g (fun i j hi hj =>
        rankRecord_const_lt_of_key _ _ (by
          rw [hkey' π i hi, hkey π j hj]
          exact_mod_cast hlt))]
      simp [hlt, not_lt_of_gt hlt]
  simp_rw [hcount]
  rw [Law.expect_add, Law.expect_const_mul, Law.expect_const_mul]
  have hhalf : U.expect (fun π => if π a < π b then (1:ℝ) else 0) = 1/2 := by linarith
  have hhalf' : U.expect (fun π => if π b < π a then (1:ℝ) else 0) = 1/2 := by linarith
  rw [hhalf, hhalf']
  ring

end TieKernels

/-! ## 3. The pooled master formula for the actual implemented laws -/

section Master

/-- Pooled genotype scores: every copy of `g` carries `sA`, every other slot `sB`. -/
noncomputable def pooledScore {P : ℕ} {G : Type*} (roster : Fin P → G) (g : G)
    (sA sB : ℝ) : Fin P → ℝ :=
  fun i => if roster i = g then sA else sB

/-- The number of copies of `g` in the current roster. -/
noncomputable def blockSize {P : ℕ} {G : Type*} (roster : Fin P → G) (g : G) : ℕ :=
  (Finset.univ.filter fun i => roster i = g).card

/-- The tied conditional expected COUNT of a key kernel (the referee's `T_A`):
the expected number of retained copies of `g` when all scores tie. By
`lexSurvivors_const` the tied value is immaterial; zero is used. -/
noncomputable def tiedCount {P S : ℕ} {G K : Type*} [Fintype K] (hSP : S ≤ P)
    (keys : K → Fin P → ℤ) (KL : Law K) (roster : Fin P → G) (g : G) : ℝ :=
  KL.expect (fun k =>
    (survivorCount roster (lexSurvivors hSP (fun _ => (0:ℝ)) (keys k)) g : ℝ))

theorem survivorCount_const {P S : ℕ} {G : Type*} (hSP : S ≤ P) (c c' : ℝ)
    (key : Fin P → ℤ) (roster : Fin P → G) (g : G) :
    survivorCount roster (lexSurvivors hSP (fun _ => c) key) g =
      survivorCount roster (lexSurvivors hSP (fun _ => c') key) g := by
  unfold survivorCount
  rw [lexSurvivors_const hSP c c' key]

theorem pooledScore_tie {P : ℕ} {G : Type*} (roster : Fin P → G) (g : G) (s : ℝ) :
    pooledScore roster g s s = fun _ => s := by
  funext i
  unfold pooledScore
  split_ifs <;> rfl

theorem pooled_count_ahead' {P S : ℕ} {G : Type*} (hSP : S ≤ P) (roster : Fin P → G)
    (g : G) {sA sB : ℝ} (h : sB < sA) (key : Fin P → ℤ) :
    survivorCount roster (lexSurvivors hSP (pooledScore roster g sA sB) key) g =
      min S (blockSize roster g) :=
  count_of_precedes hSP _ key roster g (fun i j hi hj =>
    rankRecord_lt_of_score _ key (by simp [pooledScore, hi, hj, h]))

theorem pooled_count_behind' {P S : ℕ} {G : Type*} (hSP : S ≤ P) (roster : Fin P → G)
    (g : G) {sA sB : ℝ} (h : sA < sB) (key : Fin P → ℤ) :
    survivorCount roster (lexSurvivors hSP (pooledScore roster g sA sB) key) g =
      S - (P - blockSize roster g) :=
  count_of_follows hSP _ key roster g (fun i j hi hj =>
    rankRecord_lt_of_score _ key (by simp [pooledScore, hi, hj, h]))

/-- The conditional expected count given the two pooled scores, for any key
kernel: `H` if `g` is ahead, `L` if behind, the kernel's tied count if tied. -/
theorem conditional_count {P S : ℕ} {G K : Type*} [Fintype K] (hSP : S ≤ P)
    (roster : Fin P → G) (g : G) (sA sB : ℝ) (keys : K → Fin P → ℤ) (KL : Law K) :
    (tieSelectionLaw hSP (pooledScore roster g sA sB) keys KL).expect
        (fun A => (survivorCount roster A g : ℝ)) =
      if sB < sA then ((min S (blockSize roster g) : ℕ) : ℝ)
      else if sA < sB then ((S - (P - blockSize roster g) : ℕ) : ℝ)
      else tiedCount hSP keys KL roster g := by
  unfold tieSelectionLaw
  rw [Law.expect_map]
  split_ifs with h1 h2
  · simp_rw [pooled_count_ahead' hSP roster g h1]
    exact Law.expect_const _ _
  · simp_rw [pooled_count_behind' hSP roster g h2]
    exact Law.expect_const _ _
  · have he : sA = sB := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    subst he
    rw [pooledScore_tie]
    unfold tiedCount
    simp_rw [survivorCount_const hSP sA 0]

/-- **Pooled top-S master formula for the actual law, any key kernel.** The
survivor law is the actual composite: draw the pooled scores, then push the
key law through the lexicographic sort. Nothing about the outcome
probabilities is assumed. -/
theorem pooled_master {Ω K G : Type*} [Fintype Ω] [Fintype K] {P S : ℕ}
    (hSP : S ≤ P) (L : Law Ω) (roster : Fin P → G) (g : G) (sA sB : Ω → ℝ)
    (keys : K → Fin P → ℤ) (KL : Law K) :
    (L.bind fun ω => tieSelectionLaw hSP (pooledScore roster g (sA ω) (sB ω)) keys KL).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      (L.prob (fun ω => sB ω < sA ω) * ((min S (blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω < sB ω) * ((S - (P - blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω = sB ω) * tiedCount hSP keys KL roster g) / S := by
  rw [Law.expect_bind]
  simp_rw [div_eq_mul_inv, Law.expect_mul_const, conditional_count]
  congr 1
  have hpt : ∀ ω, (if sB ω < sA ω then ((min S (blockSize roster g) : ℕ) : ℝ)
      else if sA ω < sB ω then ((S - (P - blockSize roster g) : ℕ) : ℝ)
      else tiedCount hSP keys KL roster g) =
      ((min S (blockSize roster g) : ℕ) : ℝ) * (if sB ω < sA ω then 1 else 0) +
      ((S - (P - blockSize roster g) : ℕ) : ℝ) * (if sA ω < sB ω then 1 else 0) +
      tiedCount hSP keys KL roster g * (if sA ω = sB ω then 1 else 0) := by
    intro ω
    rcases lt_trichotomy (sA ω) (sB ω) with h | h | h
    · simp [h, not_lt_of_gt h, ne_of_lt h]
    · simp [h]
    · simp [h, not_lt_of_gt h, ne_of_gt h]
  simp_rw [hpt]
  rw [Law.expect_add, Law.expect_add, Law.expect_const_mul, Law.expect_const_mul,
    Law.expect_const_mul, Law.expect_indicator, Law.expect_indicator, Law.expect_indicator]
  ring

/-- **Slot-tie instance (B2.7 / Doc A B2.3):** `T_A = S x` with `x = K/P`. -/
theorem slot_master {Ω G : Type*} [Fintype Ω] {P S : ℕ} (hSP : S ≤ P) (hP : 0 < P)
    (L : Law Ω) (roster : Fin P → G) (g : G) (sA sB : Ω → ℝ) :
    (L.bind fun ω => slotTieSelectionLaw hSP (pooledScore roster g (sA ω) (sB ω))).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      (L.prob (fun ω => sB ω < sA ω) * ((min S (blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω < sB ω) * ((S - (P - blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω = sB ω) * ((S : ℝ) * ((blockSize roster g : ℝ) / P))) / S := by
  simp_rw [slotTieSelectionLaw_eq]
  rw [pooled_master]
  unfold tiedCount
  rw [slot_tied_count hSP hP 0 roster g]
  rfl

/-- **Incumbent-A instance:** `T_A = H` when every copy of `g` has strictly more
evaluations than every other slot. -/
theorem incumbent_master_A {Ω G : Type*} [Fintype Ω] {P S : ℕ} (hSP : S ≤ P)
    (L : Law Ω) (roster : Fin P → G) (g : G) (sA sB : Ω → ℝ) (evaluations : Fin P → ℕ)
    (hinc : ∀ i j, roster i = g → roster j ≠ g → evaluations j < evaluations i) :
    (L.bind fun ω =>
        incumbentSelectionLaw hSP (pooledScore roster g (sA ω) (sB ω)) evaluations).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      (L.prob (fun ω => sB ω < sA ω) * ((min S (blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω < sB ω) * ((S - (P - blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω = sB ω) * ((min S (blockSize roster g) : ℕ) : ℝ)) / S := by
  simp_rw [incumbentSelectionLaw_eq]
  rw [pooled_master]
  unfold tiedCount
  rw [pointLaw_expect, incumbent_tied_count_A hSP 0 evaluations roster g hinc]
  rfl

/-- **Incumbent-B instance:** `T_A = L` when every other slot has strictly more
evaluations than every copy of `g`. -/
theorem incumbent_master_B {Ω G : Type*} [Fintype Ω] {P S : ℕ} (hSP : S ≤ P)
    (L : Law Ω) (roster : Fin P → G) (g : G) (sA sB : Ω → ℝ) (evaluations : Fin P → ℕ)
    (hinc : ∀ i j, roster i ≠ g → roster j = g → evaluations j < evaluations i) :
    (L.bind fun ω =>
        incumbentSelectionLaw hSP (pooledScore roster g (sA ω) (sB ω)) evaluations).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      (L.prob (fun ω => sB ω < sA ω) * ((min S (blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω < sB ω) * ((S - (P - blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω = sB ω) * ((S - (P - blockSize roster g) : ℕ) : ℝ)) / S := by
  simp_rw [incumbentSelectionLaw_eq]
  rw [pooled_master]
  unfold tiedCount
  rw [pointLaw_expect, incumbent_tied_count_B hSP 0 evaluations roster g hinc]
  rfl

/-- **Genotype-coin instance:** `T_A = (H+L)/2` with exactly two genotypes present. -/
theorem genotype_master {Ω G : Type*} [Fintype Ω] [Fintype G] {P S : ℕ} (hSP : S ≤ P)
    (L : Law Ω) (roster : Fin P → G) (g h : G) (hgh : g ≠ h)
    (hbin : ∀ i, roster i = g ∨ roster i = h) (sA sB : Ω → ℝ) :
    (L.bind fun ω =>
        genotypeTieSelectionLaw hSP (pooledScore roster g (sA ω) (sB ω)) roster).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      (L.prob (fun ω => sB ω < sA ω) * ((min S (blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω < sB ω) * ((S - (P - blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω = sB ω) *
          ((((min S (blockSize roster g) : ℕ) : ℝ) +
            ((S - (P - blockSize roster g) : ℕ) : ℝ)) / 2)) / S := by
  simp_rw [genotypeTieSelectionLaw_eq]
  rw [pooled_master]
  unfold tiedCount
  rw [genotype_tied_count hSP 0 roster g h hgh hbin]
  rfl

end Master

/-! ## 4. Closing the `T_A` input of `implemented_topS_master` -/

section ImplementedTieCount

theorem prob_prod_fst' {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (L : Law Ω) (K : Law Λ)
    (E : Ω → Prop) : (L.prod K).prob (fun ω => E ω.1) = L.prob E := by
  have h := SEKernel.ScorePooling.prob_prod_rectangle L K E (fun _ => True)
  simpa using h

theorem implemented_order_tied_iff {Ω G : Type*} [Fintype Ω] [Fintype G] {P S : ℕ}
    (hSP : S ≤ P) (L : Law Ω) (roster : Fin P → G) (g : G) (scoreA scoreB : Ω → ℝ)
    (keys : Ω → Fin P → ℤ) (ω : Ω) :
    (implementedPooledExperiment hSP L roster g scoreA scoreB keys).order ω = .tied ↔
      scoreA ω = scoreB ω := by
  rcases lt_trichotomy (scoreA ω) (scoreB ω) with h | h | h
  · simp [implementedPooledExperiment, h, not_lt_of_gt h, ne_of_lt h]
  · simp [implementedPooledExperiment, h]
  · simp [implementedPooledExperiment, h, ne_of_gt h]

/-- A tied conditional mean is the common tied value whenever the tied event
has positive probability. -/
theorem tieCount_of_const {Ω : Type*} [Fintype Ω] (E : PooledExperiment Ω) (T : ℝ)
    (hT : ∀ ω, E.order ω = .tied → E.retainedA ω = T)
    (hτ : E.law.prob (fun ω => E.order ω = .tied) ≠ 0) : E.tieCount = T := by
  have hcell : E.law.cellExpect E.retainedA (fun ω => E.order ω = .tied) =
      T * E.law.prob (fun ω => E.order ω = .tied) := by
    unfold Law.cellExpect Law.expect Law1.mean Law.prob
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only
    by_cases h : E.order ω = .tied
    · rw [if_pos h, if_pos h, hT ω h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  unfold PooledExperiment.tieCount Law.conditionalMean
  rw [hcell]
  field_simp

/-- On the independent product of a score law and a key law, the tied
conditional expected count of the implemented experiment is the key kernel's
tied count. -/
theorem product_tieCount {Ω K G : Type*} [Fintype Ω] [Fintype K] [Fintype G] {P S : ℕ}
    (hSP : S ≤ P) (L₀ : Law Ω) (KL : Law K) (roster : Fin P → G) (g : G)
    (sA sB : Ω → ℝ) (keys : K → Fin P → ℤ)
    (hτ : L₀.prob (fun ω => sA ω = sB ω) ≠ 0) :
    (implementedPooledExperiment hSP (L₀.prod KL) roster g (fun ω => sA ω.1)
      (fun ω => sB ω.1) (fun ω => keys ω.2)).tieCount = tiedCount hSP keys KL roster g := by
  set E := implementedPooledExperiment hSP (L₀.prod KL) roster g (fun ω => sA ω.1)
    (fun ω => sB ω.1) (fun ω => keys ω.2) with hE
  have hev : (fun ω => E.order ω = .tied) = (fun ω : Ω × K => sA ω.1 = sB ω.1) := by
    funext ω
    exact propext (implemented_order_tied_iff hSP _ roster g _ _ _ ω)
  have htc : E.tieCount = (L₀.prod KL).conditionalMean E.retainedA
      (fun ω => sA ω.1 = sB ω.1) := by
    unfold PooledExperiment.tieCount
    rw [hev]
    rfl
  have hcell : (L₀.prod KL).cellExpect E.retainedA (fun ω => sA ω.1 = sB ω.1) =
      (L₀.prod KL).expect (fun ω => (if sA ω.1 = sB ω.1 then (1:ℝ) else 0) *
        (survivorCount roster (lexSurvivors hSP (fun _ => (0:ℝ)) (keys ω.2)) g : ℝ)) := by
    unfold Law.cellExpect
    congr 1
    funext ω
    by_cases h : sA ω.1 = sB ω.1
    · rw [if_pos h, if_pos h, one_mul]
      have hs : (fun i => if roster i = g then sA ω.1 else sB ω.1) = fun _ => sB ω.1 := by
        funext i
        split_ifs <;> simp [h]
      show ((survivorCount roster (lexSurvivors hSP
        (fun i => if roster i = g then sA ω.1 else sB ω.1) (keys ω.2)) g : ℕ) : ℝ) = _
      rw [hs, survivorCount_const hSP (sB ω.1) 0]
    · rw [if_neg h, if_neg h, zero_mul]
  have hm := Law.expect_prod_mul L₀ KL (fun a => if sA a = sB a then (1:ℝ) else 0)
    (fun k => (survivorCount roster (lexSurvivors hSP (fun _ => (0:ℝ)) (keys k)) g : ℝ))
  rw [Law.expect_indicator] at hm
  have hprob : (L₀.prod KL).prob (fun ω => sA ω.1 = sB ω.1) =
      L₀.prob (fun ω => sA ω = sB ω) := prob_prod_fst' L₀ KL (fun ω => sA ω = sB ω)
  rw [htc]
  unfold Law.conditionalMean
  rw [hcell, hprob]
  have hm' : (L₀.prod KL).expect (fun ω => (if sA ω.1 = sB ω.1 then (1:ℝ) else 0) *
      (survivorCount roster (lexSurvivors hSP (fun _ => (0:ℝ)) (keys ω.2)) g : ℝ)) =
      L₀.prob (fun ω => sA ω = sB ω) * tiedCount hSP keys KL roster g := hm
  rw [hm']
  field_simp

/-- `implemented_topS_master` with its `T_A` input closed for uniform slot ties:
the score law and the slot permutation are independent product coordinates. -/
theorem slot_implemented_master {Ω G : Type*} [Fintype Ω] [Fintype G] {P S : ℕ}
    (hSP : S ≤ P) (hS : 0 < S) (hP : 0 < P) (L₀ : Law Ω) (roster : Fin P → G) (g : G)
    (sA sB : Ω → ℝ) (hτ : L₀.prob (fun ω => sA ω = sB ω) ≠ 0) :
    (L₀.prod (uniformLaw (Equiv.Perm (Fin P)))).expect (fun ω => (survivorCount roster
      (lexSurvivors hSP (fun i => if roster i = g then sA ω.1 else sB ω.1)
        (slotKey ω.2)) g : ℝ) / S) =
      (L₀.prob (fun ω => sB ω < sA ω) *
          ((min S ((Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) +
        L₀.prob (fun ω => sA ω < sB ω) *
          ((S - (P - (Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) +
        L₀.prob (fun ω => sA ω = sB ω) * ((S : ℝ) * ((blockSize roster g : ℝ) / P))) / S := by
  have hT := product_tieCount hSP L₀ (uniformLaw (Equiv.Perm (Fin P))) roster g sA sB slotKey hτ
  have hc : tiedCount hSP slotKey (uniformLaw (Equiv.Perm (Fin P))) roster g =
      (S : ℝ) * ((blockSize roster g : ℝ) / P) := slot_tied_count hSP hP 0 roster g
  rw [hc] at hT
  have h1 : (L₀.prod (uniformLaw (Equiv.Perm (Fin P)))).prob (fun ω => sB ω.1 < sA ω.1) =
      L₀.prob (fun ω => sB ω < sA ω) := prob_prod_fst' _ _ (fun ω => sB ω < sA ω)
  have h2 : (L₀.prod (uniformLaw (Equiv.Perm (Fin P)))).prob (fun ω => sA ω.1 < sB ω.1) =
      L₀.prob (fun ω => sA ω < sB ω) := prob_prod_fst' _ _ (fun ω => sA ω < sB ω)
  have h3 : (L₀.prod (uniformLaw (Equiv.Perm (Fin P)))).prob (fun ω => sA ω.1 = sB ω.1) =
      L₀.prob (fun ω => sA ω = sB ω) := prob_prod_fst' _ _ (fun ω => sA ω = sB ω)
  exact implemented_topS_master (Ω := Ω × Equiv.Perm (Fin P)) hSP hS
    (L₀.prod (uniformLaw (Equiv.Perm (Fin P)))) roster g (fun ω => sA ω.1) (fun ω => sB ω.1)
    (fun ω => slotKey ω.2) _ _ _ _ h1 h2 h3 hT

/-- `implemented_topS_master` with `T_A` closed for the fair genotype coin. -/
theorem genotype_implemented_master {Ω G : Type*} [Fintype Ω] [Fintype G] {P S : ℕ}
    (hSP : S ≤ P) (hS : 0 < S) (L₀ : Law Ω) (roster : Fin P → G) (g h : G) (hgh : g ≠ h)
    (hbin : ∀ i, roster i = g ∨ roster i = h)
    (sA sB : Ω → ℝ) (hτ : L₀.prob (fun ω => sA ω = sB ω) ≠ 0) :
    (L₀.prod (uniformLaw (Equiv.Perm (Fin (Fintype.card G))))).expect
      (fun ω => (survivorCount roster
        (lexSurvivors hSP (fun i => if roster i = g then sA ω.1 else sB ω.1)
          (genotypeKey roster ω.2)) g : ℝ) / S) =
      (L₀.prob (fun ω => sB ω < sA ω) *
          ((min S ((Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) +
        L₀.prob (fun ω => sA ω < sB ω) *
          ((S - (P - (Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) +
        L₀.prob (fun ω => sA ω = sB ω) *
          ((((min S (blockSize roster g) : ℕ) : ℝ) +
            ((S - (P - blockSize roster g) : ℕ) : ℝ)) / 2)) / S := by
  have hT := product_tieCount hSP L₀ (uniformLaw (Equiv.Perm (Fin (Fintype.card G))))
    roster g sA sB (genotypeKey roster) hτ
  have hc : tiedCount hSP (genotypeKey roster)
      (uniformLaw (Equiv.Perm (Fin (Fintype.card G)))) roster g =
      ((((min S (blockSize roster g) : ℕ) : ℝ) +
            ((S - (P - blockSize roster g) : ℕ) : ℝ)) / 2) :=
    genotype_tied_count hSP 0 roster g h hgh hbin
  rw [hc] at hT
  have h1 : (L₀.prod (uniformLaw (Equiv.Perm (Fin (Fintype.card G))))).prob
      (fun ω => sB ω.1 < sA ω.1) = L₀.prob (fun ω => sB ω < sA ω) :=
    prob_prod_fst' _ _ (fun ω => sB ω < sA ω)
  have h2 : (L₀.prod (uniformLaw (Equiv.Perm (Fin (Fintype.card G))))).prob
      (fun ω => sA ω.1 < sB ω.1) = L₀.prob (fun ω => sA ω < sB ω) :=
    prob_prod_fst' _ _ (fun ω => sA ω < sB ω)
  have h3 : (L₀.prod (uniformLaw (Equiv.Perm (Fin (Fintype.card G))))).prob
      (fun ω => sA ω.1 = sB ω.1) = L₀.prob (fun ω => sA ω = sB ω) :=
    prob_prod_fst' _ _ (fun ω => sA ω = sB ω)
  exact implemented_topS_master (Ω := Ω × Equiv.Perm (Fin (Fintype.card G))) hSP hS
    (L₀.prod (uniformLaw (Equiv.Perm (Fin (Fintype.card G))))) roster g
    (fun ω => sA ω.1) (fun ω => sB ω.1) (fun ω => genotypeKey roster ω.2) _ _ _ _ h1 h2 h3 hT

/-- `implemented_topS_master` with `T_A = H` closed for protected incumbent `g`. -/
theorem incumbent_implemented_master_A {Ω G : Type*} [Fintype Ω] [Fintype G] {P S : ℕ}
    (hSP : S ≤ P) (hS : 0 < S) (L₀ : Law Ω) (roster : Fin P → G) (g : G)
    (sA sB : Ω → ℝ) (evaluations : Fin P → ℕ)
    (hinc : ∀ i j, roster i = g → roster j ≠ g → evaluations j < evaluations i)
    (hτ : L₀.prob (fun ω => sA ω = sB ω) ≠ 0) :
    L₀.expect (fun ω => (survivorCount roster
      (lexSurvivors hSP (fun i => if roster i = g then sA ω else sB ω)
        (incumbentKey evaluations)) g : ℝ) / S) =
      (L₀.prob (fun ω => sB ω < sA ω) *
          ((min S ((Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) +
        L₀.prob (fun ω => sA ω < sB ω) *
          ((S - (P - (Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) +
        L₀.prob (fun ω => sA ω = sB ω) * ((min S (blockSize roster g) : ℕ) : ℝ)) / S := by
  refine implemented_topS_master hSP hS L₀ roster g sA sB (fun _ => incumbentKey evaluations)
    _ _ _ _ rfl rfl rfl ?_
  apply tieCount_of_const
  · intro ω hω
    have he : sA ω = sB ω := (implemented_order_tied_iff hSP L₀ roster g sA sB _ ω).1 hω
    have hs : (fun i => if roster i = g then sA ω else sB ω) = fun _ => sB ω := by
      funext i
      split_ifs <;> simp [he]
    show ((survivorCount roster (lexSurvivors hSP
      (fun i => if roster i = g then sA ω else sB ω) (incumbentKey evaluations)) g : ℕ) : ℝ) = _
    rw [hs, incumbent_tied_count_A hSP _ evaluations roster g hinc]
    rfl
  · have hev : (fun ω => (implementedPooledExperiment hSP L₀ roster g sA sB
        (fun _ => incumbentKey evaluations)).order ω = .tied) = (fun ω => sA ω = sB ω) := by
      funext ω
      exact propext (implemented_order_tied_iff hSP _ roster g _ _ _ ω)
    change L₀.prob (fun ω => (implementedPooledExperiment hSP L₀ roster g sA sB
        (fun _ => incumbentKey evaluations)).order ω = .tied) ≠ 0
    rw [hev]
    exact hτ

/-- `implemented_topS_master` with `T_A = L` closed for protected incumbents
outside `g`. -/
theorem incumbent_implemented_master_B {Ω G : Type*} [Fintype Ω] [Fintype G] {P S : ℕ}
    (hSP : S ≤ P) (hS : 0 < S) (L₀ : Law Ω) (roster : Fin P → G) (g : G)
    (sA sB : Ω → ℝ) (evaluations : Fin P → ℕ)
    (hinc : ∀ i j, roster i ≠ g → roster j = g → evaluations j < evaluations i)
    (hτ : L₀.prob (fun ω => sA ω = sB ω) ≠ 0) :
    L₀.expect (fun ω => (survivorCount roster
      (lexSurvivors hSP (fun i => if roster i = g then sA ω else sB ω)
        (incumbentKey evaluations)) g : ℝ) / S) =
      (L₀.prob (fun ω => sB ω < sA ω) *
          ((min S ((Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) +
        L₀.prob (fun ω => sA ω < sB ω) *
          ((S - (P - (Finset.univ.filter fun i => roster i = g).card) : ℕ) : ℝ) +
        L₀.prob (fun ω => sA ω = sB ω) * ((S - (P - blockSize roster g) : ℕ) : ℝ)) / S := by
  refine implemented_topS_master hSP hS L₀ roster g sA sB (fun _ => incumbentKey evaluations)
    _ _ _ _ rfl rfl rfl ?_
  apply tieCount_of_const
  · intro ω hω
    have he : sA ω = sB ω := (implemented_order_tied_iff hSP L₀ roster g sA sB _ ω).1 hω
    have hs : (fun i => if roster i = g then sA ω else sB ω) = fun _ => sB ω := by
      funext i
      split_ifs <;> simp [he]
    show ((survivorCount roster (lexSurvivors hSP
      (fun i => if roster i = g then sA ω else sB ω) (incumbentKey evaluations)) g : ℕ) : ℝ) = _
    rw [hs, incumbent_tied_count_B hSP _ evaluations roster g hinc]
    rfl
  · have hev : (fun ω => (implementedPooledExperiment hSP L₀ roster g sA sB
        (fun _ => incumbentKey evaluations)).order ω = .tied) = (fun ω => sA ω = sB ω) := by
      funext ω
      exact propext (implemented_order_tied_iff hSP _ roster g _ _ _ ω)
    change L₀.prob (fun ω => (implementedPooledExperiment hSP L₀ roster g sA sB
        (fun _ => incumbentKey evaluations)).order ω = .tied) ≠ 0
    rw [hev]
    exact hτ

end ImplementedTieCount

/-! ## 5. Concrete stochastic realizations under the actual sort -/

section Witnesses

theorem order_probs_total {Ω : Type*} [Fintype Ω] (L : Law Ω) (sA sB : Ω → ℝ) :
    L.prob (fun ω => sB ω < sA ω) + L.prob (fun ω => sA ω < sB ω) +
      L.prob (fun ω => sA ω = sB ω) = 1 := by
  rw [← L.expect_indicator, ← L.expect_indicator, ← L.expect_indicator,
    ← Law.expect_add, ← Law.expect_add]
  have hpt : (fun ω => ((if sB ω < sA ω then (1:ℝ) else 0) +
      (if sA ω < sB ω then 1 else 0)) + (if sA ω = sB ω then 1 else 0)) = fun _ => 1 := by
    funext ω
    rcases lt_trichotomy (sA ω) (sB ω) with h | h | h
    · simp [h, not_lt_of_gt h, ne_of_lt h]
    · simp [h]
    · simp [h, not_lt_of_gt h, ne_of_gt h]
  rw [hpt, Law.expect_const]

/-- Count form of `pooled_master`. -/
theorem pooled_master_count {Ω K G : Type*} [Fintype Ω] [Fintype K] {P S : ℕ}
    (hSP : S ≤ P) (hS : 0 < S) (L : Law Ω) (roster : Fin P → G) (g : G)
    (sA sB : Ω → ℝ) (keys : K → Fin P → ℤ) (KL : Law K) :
    (L.bind fun ω => tieSelectionLaw hSP (pooledScore roster g (sA ω) (sB ω)) keys KL).expect
        (fun A => (survivorCount roster A g : ℝ)) =
      L.prob (fun ω => sB ω < sA ω) * ((min S (blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω < sB ω) * ((S - (P - blockSize roster g) : ℕ) : ℝ) +
        L.prob (fun ω => sA ω = sB ω) * tiedCount hSP keys KL roster g := by
  have h := pooled_master hSP L roster g sA sB keys KL
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  simp only [div_eq_mul_inv, Law.expect_mul_const] at h
  have h' := congrArg (fun v => v * (S : ℝ)) h
  simp only [mul_assoc, inv_mul_cancel₀ hs, mul_one] at h'
  exact h'

/-- One complementary paired binary board: `true` means A correct and B wrong,
`false` means B correct and A wrong. -/
noncomputable def boardScoreA (b : Bool) : ℝ := if b then 1 else 0
noncomputable def boardScoreB (b : Bool) : ℝ := if b then 0 else 1

theorem board_probs (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (MutationBaseline.bernoulli p hp hp').prob (fun b => boardScoreB b < boardScoreA b) = p ∧
    (MutationBaseline.bernoulli p hp hp').prob (fun b => boardScoreA b < boardScoreB b) = 1-p ∧
    (MutationBaseline.bernoulli p hp hp').prob (fun b => boardScoreA b = boardScoreB b) = 0 ∧
    (MutationBaseline.bernoulli p hp hp').expect boardScoreA = p ∧
    (MutationBaseline.bernoulli p hp hp').expect boardScoreB = 1-p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Law.prob, Law.expect, Law1.mean, MutationBaseline.bernoulli,
      boardScoreA, boardScoreB]

theorem h412 : (4:ℕ) ≤ 12 := by norm_num

/-- **B2.8 / Doc A B2.3, any key kernel.** One copy of `g` among `P = 12`,
`S = 4`, a tie-free score law whose two strict orders are equally likely:
the expected survivor share under the actual sort is `1/8`. -/
theorem neutral_newcomer_share {Ω K G : Type*} [Fintype Ω] [Fintype K] (L : Law Ω)
    (roster : Fin 12 → G) (g : G) (hone : blockSize roster g = 1) (sA sB : Ω → ℝ)
    (hnotie : L.prob (fun ω => sA ω = sB ω) = 0)
    (hsym : L.prob (fun ω => sB ω < sA ω) = L.prob (fun ω => sA ω < sB ω))
    (keys : K → Fin 12 → ℤ) (KL : Law K) :
    (L.bind fun ω => tieSelectionLaw h412 (pooledScore roster g (sA ω) (sB ω)) keys KL).expect
        (fun A => (survivorCount roster A g : ℝ) / 4) = 1/8 ∧
    (L.bind fun ω => tieSelectionLaw h412 (pooledScore roster g (sA ω) (sB ω)) keys KL).expect
        (fun A => (survivorCount roster A g : ℝ)) = 1/2 := by
  have htot := order_probs_total L sA sB
  have hr : L.prob (fun ω => sB ω < sA ω) = 1/2 := by linarith
  have hm := pooled_master h412 L roster g sA sB keys KL
  have hc := pooled_master_count h412 (by norm_num) L roster g sA sB keys KL
  rw [hone, hnotie, hr, ← hsym, hr] at hm hc
  norm_num at hm hc
  exact ⟨hm, hc⟩

/-- The newcomer roster: slot 11 (the last, appended offspring slot) carries
the newcomer genotype `true`. -/
def newcomerRoster (i : Fin 12) : Bool := decide ((i : ℕ) = 11)

theorem newcomerRoster_block : blockSize newcomerRoster true = 1 := by
  have h : (Finset.univ.filter fun i : Fin 12 => newcomerRoster i = true).card = 1 := by
    decide
  unfold blockSize
  convert h

/-- The fair complementary board (`D = ±1` with equal probability). -/
noncomputable def fairBoard : Law Bool := MutationBaseline.bernoulli (1/2) (by norm_num) (by norm_num)

theorem fairBoard_probs :
    fairBoard.prob (fun b => boardScoreB b < boardScoreA b) = 1/2 ∧
    fairBoard.prob (fun b => boardScoreA b < boardScoreB b) = 1/2 ∧
    fairBoard.prob (fun b => boardScoreA b = boardScoreB b) = 0 := by
  obtain ⟨h1, h2, h3, -, -⟩ := board_probs (1/2) (by norm_num) (by norm_num)
  refine ⟨h1, ?_, h3⟩
  rw [show fairBoard.prob (fun b => boardScoreA b < boardScoreB b) = 1 - 1/2 from h2]
  norm_num

/-- **Concrete 1/8 > 1/12 witness on the actual uniform-slot-tie law.** -/
theorem neutral_newcomer_witness_slot :
    (fairBoard.bind fun b => slotTieSelectionLaw h412
        (pooledScore newcomerRoster true (boardScoreA b) (boardScoreB b))).expect
        (fun A => (survivorCount newcomerRoster A true : ℝ) / 4) = 1/8 ∧
    (fairBoard.bind fun b => slotTieSelectionLaw h412
        (pooledScore newcomerRoster true (boardScoreA b) (boardScoreB b))).expect
        (fun A => (survivorCount newcomerRoster A true : ℝ)) = 1/2 ∧
    (1:ℝ)/12 < 1/8 ∧ (1:ℝ)/3 < 1/2 := by
  obtain ⟨h1, h2, h3⟩ := fairBoard_probs
  have h := neutral_newcomer_share fairBoard newcomerRoster true newcomerRoster_block
    boardScoreA boardScoreB h3 (by rw [h1, h2]) slotKey
    (uniformLaw (Equiv.Perm (Fin 12)))
  exact ⟨h.1, h.2, by norm_num, by norm_num⟩

/-- **The same witness on the actual protected-incumbent law**, for every
evaluation-count vector (the board is tie-free). -/
theorem neutral_newcomer_witness_incumbent (evaluations : Fin 12 → ℕ) :
    (fairBoard.bind fun b => incumbentSelectionLaw h412
        (pooledScore newcomerRoster true (boardScoreA b) (boardScoreB b)) evaluations).expect
        (fun A => (survivorCount newcomerRoster A true : ℝ) / 4) = 1/8 := by
  obtain ⟨h1, h2, h3⟩ := fairBoard_probs
  exact (neutral_newcomer_share fairBoard newcomerRoster true newcomerRoster_block
    boardScoreA boardScoreB h3 (by rw [h1, h2]) (fun _ : Unit => incumbentKey evaluations)
    (pointLaw ())).1

/-- Ten copies of A (`true`, slots 0-9) and two of B (`false`, slots 10-11). -/
def majorityRoster (i : Fin 12) : Bool := decide ((i : ℕ) < 10)

theorem majorityRoster_block : blockSize majorityRoster true = 10 := by
  have h : (Finset.univ.filter fun i : Fin 12 => majorityRoster i = true).card = 10 := by
    decide
  unfold blockSize
  convert h

/-- The 51/49 complementary board. -/
noncomputable def biasedBoard : Law Bool :=
  MutationBaseline.bernoulli (51/100) (by norm_num) (by norm_num)

/-- True accuracies and the uniform current frequencies of the 10/2 roster. -/
noncomputable def trueAccuracy (g : Bool) : ℝ := if g then 51/100 else 49/100
noncomputable def currentShare (g : Bool) : ℝ := if g then 5/6 else 1/6

/-- **Doc B Counterexample B5.3, realized on the actual sort, any key kernel.**
Unbiased complementary scoring (`E sA = 51/100`, `E sB = 49/100`), no ties;
the expected A survivor share is `151/200 < 5/6` and the expected true mean
fitness of the survivors falls by exactly `47/30000`. -/
theorem block_fitness_decline {K : Type*} [Fintype K] (keys : K → Fin 12 → ℤ) (KL : Law K) :
    biasedBoard.expect boardScoreA = 51/100 ∧ biasedBoard.expect boardScoreB = 49/100 ∧
    biasedBoard.prob (fun b => boardScoreA b = boardScoreB b) = 0 ∧
    (biasedBoard.bind fun b => tieSelectionLaw h412
        (pooledScore majorityRoster true (boardScoreA b) (boardScoreB b)) keys KL).expect
        (fun A => (survivorCount majorityRoster A true : ℝ) / 4) = 151/200 ∧
    (biasedBoard.bind fun b => tieSelectionLaw h412
        (pooledScore majorityRoster true (boardScoreA b) (boardScoreB b)) keys KL).expect
        (survivorMean majorityRoster trueAccuracy) -
      ∑ g, currentShare g * trueAccuracy g = -47/30000 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := board_probs (51/100) (by norm_num) (by norm_num)
  change biasedBoard.prob _ = _ at h1 h2 h3
  change biasedBoard.expect _ = _ at h4 h5
  set M := biasedBoard.bind fun b => tieSelectionLaw h412
    (pooledScore majorityRoster true (boardScoreA b) (boardScoreB b)) keys KL
  have hm := pooled_master h412 biasedBoard majorityRoster true boardScoreA boardScoreB keys KL
  have hc := pooled_master_count h412 (by norm_num) biasedBoard majorityRoster true
    boardScoreA boardScoreB keys KL
  rw [majorityRoster_block] at hm hc
  rw [h1, h2, h3] at hm hc
  norm_num at hm hc
  have hsum := expectedSurvivorCount_sum M majorityRoster
  rw [Fintype.sum_bool] at hsum
  norm_num at hsum
  have hfalse : expectedSurvivorCount M majorityRoster false = 49/50 := by
    have : expectedSurvivorCount M majorityRoster true = 151/50 := hc
    linarith
  have hprice := price_count_identity (by norm_num : 0 < 4) M majorityRoster currentShare
    trueAccuracy
  rw [Fintype.sum_bool, Fintype.sum_bool, hfalse,
    show expectedSurvivorCount M majorityRoster true = 151/50 from hc] at hprice
  refine ⟨h4, by rw [h5]; norm_num, h3, hm, ?_⟩
  rw [Fintype.sum_bool]
  simp only [currentShare, trueAccuracy, if_true, Bool.false_eq_true, if_false] at hprice ⊢
  norm_num at hprice ⊢
  linarith

/-- The witness on the actual uniform-slot-tie law. -/
theorem block_fitness_decline_slot :
    (biasedBoard.bind fun b => slotTieSelectionLaw h412
        (pooledScore majorityRoster true (boardScoreA b) (boardScoreB b))).expect
        (fun A => (survivorCount majorityRoster A true : ℝ) / 4) = 151/200 ∧
    (biasedBoard.bind fun b => slotTieSelectionLaw h412
        (pooledScore majorityRoster true (boardScoreA b) (boardScoreB b))).expect
        (survivorMean majorityRoster trueAccuracy) -
      ∑ g, currentShare g * trueAccuracy g = -47/30000 ∧
    (151:ℝ)/200 < 5/6 := by
  have h := block_fitness_decline slotKey (uniformLaw (Equiv.Perm (Fin 12)))
  exact ⟨h.2.2.2.1, h.2.2.2.2, by norm_num⟩

/-- `currentShare` is the actual roster frequency. -/
theorem majorityRoster_share :
    ((blockSize majorityRoster true : ℝ) / 12) = currentShare true ∧
      (((12 - blockSize majorityRoster true : ℕ) : ℝ) / 12) = currentShare false := by
  rw [majorityRoster_block]
  norm_num [currentShare]

end Witnesses

/-! ## 6. Identical outcomes: the protected-incumbent mutation floor -/

section MutationFloor

open MutationBaseline

/-- **Doc A B3.2 / Doc B B3.3, selection step.** With identical scores, a
priority key placing every voter (`ph i = false`) strictly ahead of every board
(`ph i = true`), and at least `S` voters, the actual sort retains no board. -/
theorem identical_outcomes_no_board {P S : ℕ} (hSP : S ≤ P) (c : ℝ) (key : Fin P → ℤ)
    (ph : Fin P → Bool)
    (hprio : ∀ i j, ph i = false → ph j = true → key i < key j)
    (hvoters : S ≤ blockSize ph false) :
    survivorCount ph (lexSurvivors hSP (fun _ => c) key) true = 0 := by
  have h : survivorCount ph (lexSurvivors hSP (fun _ => c) key) false =
      min S (blockSize ph false) := count_of_precedes hSP (fun _ => c) key ph false
    (fun i j hi hj => rankRecord_const_lt_of_key c key (hprio i j hi (by simpa using hj)))
  rw [Nat.min_eq_left hvoters] at h
  have hsum := survivorCount_sum ph (lexSurvivors hSP (fun _ => c) key)
  rw [Fintype.sum_bool] at hsum
  omega

/-- Survivor board fraction. -/
noncomputable def boardFraction {P S : ℕ} (ph : Fin P → Bool) (A : Survivors P S) : ℝ :=
  (survivorCount ph A true : ℝ) / S

theorem boardFraction_bounds {P S : ℕ} (hS : 0 < S) (ph : Fin P → Bool) (A : Survivors P S) :
    0 ≤ boardFraction ph A ∧ boardFraction ph A ≤ 1 := by
  have hle : survivorCount ph A true ≤ S := by
    have hsum := survivorCount_sum ph A
    rw [Fintype.sum_bool] at hsum
    omega
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  unfold boardFraction
  constructor
  · exact div_nonneg (by positivity) hs.le
  · rw [div_le_one hs]
    exact_mod_cast hle

/-- One generation: a survivor law, then `P - S` offspring, offspring `j` a board
with the MutationBaseline transmission probability at the survivor board
fraction (uniform donor marginal, then mutation; `u` voter→board, `d`
board→voter). Offspring are independent product coordinates. -/
noncomputable def generationLaw {P S : ℕ} (hS : 0 < S) (sel : Law (Survivors P S))
    (ph : Fin P → Bool) (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    Law (Survivors P S × (Fin (P - S) → Bool)) :=
  sel.bind (fun A => (Law.pi (fun _ : Fin (P - S) =>
    offspringLaw u d (boardFraction ph A) hu hu' hd hd'
      (boardFraction_bounds hS ph A).1 (boardFraction_bounds hS ph A).2)).map
    (fun o => (A, o)))

/-- The next population's board share: retained survivors keep their
phenotype; each offspring board counts one. -/
noncomputable def nextBoardShare {P S : ℕ} (ph : Fin P → Bool)
    (z : Survivors P S × (Fin (P - S) → Bool)) : ℝ :=
  ((S : ℝ) * boardFraction ph z.1 + ∑ j, (if z.2 j then (1:ℝ) else 0)) / P

/-- Exact one-generation transmission for the actual survivor law. -/
theorem generation_expected_share {P S : ℕ} (hS : 0 < S) (hSP : S ≤ P)
    (sel : Law (Survivors P S)) (ph : Fin P → Bool) (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 1) :
    (generationLaw hS sel ph u d hu hu' hd hd').expect (nextBoardShare ph) =
      affineStep ((P - S : ℕ) / (P : ℝ)) u d (sel.expect (boardFraction ph)) := by
  have hP : 0 < P := lt_of_lt_of_le hS hSP
  unfold generationLaw
  rw [Law.expect_bind, ← MutationBaseline.expect_affineStep]
  congr 1
  funext A
  rw [Law.expect_map]
  set O := Law.pi (fun _ : Fin (P - S) =>
    offspringLaw u d (boardFraction ph A) hu hu' hd hd'
      (boardFraction_bounds hS ph A).1 (boardFraction_bounds hS ph A).2) with hO
  have hX : ∀ j : Fin (P - S), O.expect (fun o => if o j then (1:ℝ) else 0) =
      mutationProbability u d (boardFraction ph A) := by
    intro j
    rw [hO, Law.expect_pi_coord (fun _ : Fin (P - S) =>
        offspringLaw u d (boardFraction ph A) hu hu' hd hd'
          (boardFraction_bounds hS ph A).1 (boardFraction_bounds hS ph A).2) j
        (fun b => if b then (1:ℝ) else 0)]
    exact offspring_mean _ _ _ _ _ _ _ _ _
  have hT := finite_population_transmission O P S hP hSP u d (boardFraction ph A)
    (fun j o => if o j then (1:ℝ) else 0) hX
  exact hT

/-- **Mutation floor (Doc A B3.2, Doc B B3.3 one-generation form).** Every
realized score vector is constant (identical outcomes), voters have strictly
more evaluations than boards, and at least `S` voters are present. Under the
actual protected-incumbent law every survivor is a voter and the expected next
board share is exactly the offspring mutation influx `r u`, `r = (P-S)/P`. -/
theorem incumbent_mutation_floor {Ω : Type*} [Fintype Ω] {P S : ℕ} (hS : 0 < S)
    (hSP : S ≤ P) (L : Law Ω) (score : Ω → Fin P → ℝ)
    (hident : ∀ ω i j, score ω i = score ω j) (evaluations : Fin P → ℕ) (ph : Fin P → Bool)
    (hprio : ∀ i j, ph i = false → ph j = true → evaluations j < evaluations i)
    (hvoters : S ≤ blockSize ph false)
    (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    (L.bind fun ω => incumbentSelectionLaw hSP (score ω) evaluations).expect
        (fun A => (survivorCount ph A true : ℝ)) = 0 ∧
    (generationLaw hS (L.bind fun ω => incumbentSelectionLaw hSP (score ω) evaluations)
        ph u d hu hu' hd hd').expect (nextBoardShare ph) =
      ((P - S : ℕ) / (P : ℝ)) * u := by
  have hP : 0 < P := lt_of_lt_of_le hS hSP
  have hconst : ∀ ω, score ω = fun _ => score ω ⟨0, hP⟩ := by
    intro ω
    funext i
    exact hident ω i ⟨0, hP⟩
  have hzero : ∀ ω, (incumbentSelectionLaw hSP (score ω) evaluations).expect
      (fun A => (survivorCount ph A true : ℝ)) = 0 := by
    intro ω
    rw [incumbentSelectionLaw_eq]
    unfold tieSelectionLaw
    rw [Law.expect_map, pointLaw_expect, hconst ω,
      identical_outcomes_no_board hSP _ (incumbentKey evaluations) ph (fun i j hi hj => by
        have := hprio i j hi hj
        unfold incumbentKey
        omega) hvoters]
    simp
  have h1 : (L.bind fun ω => incumbentSelectionLaw hSP (score ω) evaluations).expect
      (fun A => (survivorCount ph A true : ℝ)) = 0 := by
    rw [Law.expect_bind]
    simp_rw [hzero]
    exact Law.expect_const _ _
  refine ⟨h1, ?_⟩
  rw [generation_expected_share hS hSP]
  have h2 : (L.bind fun ω => incumbentSelectionLaw hSP (score ω) evaluations).expect
      (boardFraction ph) = 0 := by
    unfold boardFraction
    simp only [div_eq_mul_inv]
    rw [Law.expect_mul_const, h1, zero_mul]
  rw [h2]
  unfold affineStep
  ring

/-- **Doc B B3.4 / Doc A B3.2, slot ties restore the baseline.** With
identical scores and the actual uniform slot-permutation law, the expected
survivor board fraction is the current board share `x` and the next
generation follows the random-survival recursion `r u + (1 - r(u+d)) x`. -/
theorem slot_ties_restore_baseline {Ω : Type*} [Fintype Ω] {P S : ℕ} (hS : 0 < S)
    (hSP : S ≤ P) (L : Law Ω) (score : Ω → Fin P → ℝ)
    (hident : ∀ ω i j, score ω i = score ω j) (ph : Fin P → Bool)
    (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    (L.bind fun ω => slotTieSelectionLaw hSP (score ω)).expect (boardFraction ph) =
      (blockSize ph true : ℝ) / P ∧
    (generationLaw hS (L.bind fun ω => slotTieSelectionLaw hSP (score ω))
        ph u d hu hu' hd hd').expect (nextBoardShare ph) =
      affineStep ((P - S : ℕ) / (P : ℝ)) u d ((blockSize ph true : ℝ) / P) := by
  have hP : 0 < P := lt_of_lt_of_le hS hSP
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  have hconst : ∀ ω, score ω = fun _ => score ω ⟨0, hP⟩ := by
    intro ω
    funext i
    exact hident ω i ⟨0, hP⟩
  have hx : ∀ ω, (slotTieSelectionLaw hSP (score ω)).expect (boardFraction ph) =
      (blockSize ph true : ℝ) / P := by
    intro ω
    rw [slotTieSelectionLaw_eq]
    unfold tieSelectionLaw boardFraction
    rw [Law.expect_map]
    simp only [div_eq_mul_inv]
    rw [Law.expect_mul_const, hconst ω]
    have := slot_tied_count hSP hP (score ω ⟨0, hP⟩) ph true
    simp only [div_eq_mul_inv] at this
    rw [this]
    unfold blockSize
    rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have h1 : (L.bind fun ω => slotTieSelectionLaw hSP (score ω)).expect (boardFraction ph) =
      (blockSize ph true : ℝ) / P := by
    rw [Law.expect_bind]
    simp_rw [hx]
    exact Law.expect_const _ _
  exact ⟨h1, by rw [generation_expected_share hS hSP, h1]⟩

/-- **Doc B B3.4 counterexample on the actual genotype-coin law.** Two board
copies and ten voters, `S = 4`, identical scores: the fair genotype coin
retains one board in expectation, uniform slot ties retain `2/3`. -/
def twoBoardRoster (i : Fin 12) : Bool := decide (10 ≤ (i : ℕ))

theorem twoBoardRoster_block : blockSize twoBoardRoster true = 2 := by
  have h : (Finset.univ.filter fun i : Fin 12 => twoBoardRoster i = true).card = 2 := by
    decide
  unfold blockSize
  convert h

theorem genotype_coin_breaks_baseline (c : ℝ) :
    (genotypeTieSelectionLaw h412 (fun _ => c) twoBoardRoster).expect
        (fun A => (survivorCount twoBoardRoster A true : ℝ)) = 1 ∧
    (slotTieSelectionLaw h412 (fun _ => c)).expect
        (fun A => (survivorCount twoBoardRoster A true : ℝ)) = 2/3 := by
  constructor
  · rw [genotypeTieSelectionLaw_eq]
    unfold tieSelectionLaw
    rw [Law.expect_map]
    have h := genotype_tied_count h412 c twoBoardRoster true false (by decide)
      (fun i => Bool.eq_false_or_eq_true (twoBoardRoster i))
    have hb := twoBoardRoster_block
    unfold blockSize at hb
    rw [hb] at h
    rw [h]
    norm_num
  · rw [slotTieSelectionLaw_eq]
    unfold tieSelectionLaw
    rw [Law.expect_map, slot_tied_count h412 (by norm_num) c twoBoardRoster true]
    have hb := twoBoardRoster_block
    unfold blockSize at hb
    rw [hb]
    norm_num

/-- Doc B B3.3 numerics: the floor `r u = 2/25` (`P = 12`, `S = 4`,
`u = 3/25`) equals the random-survival control mean at generation 1 and is
strictly below it at every generation `t ≥ 2`. -/
theorem floor_below_control (t : ℕ) (ht : 2 ≤ t) :
    ((12 - 4 : ℕ) / (12 : ℝ)) * (3/25) = 2/25 ∧
    meanTrajectory (2/3) (3/25) (3/125) 0 1 = 2/25 ∧
    (2:ℝ)/25 < meanTrajectory (2/3) (3/25) (3/125) 0 t := by
  refine ⟨by norm_num, by rw [experiment_trajectory]; norm_num, ?_⟩
  rw [experiment_trajectory]
  have hb : ((113:ℝ)/125)^t ≤ (113/125)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
  nlinarith

end MutationFloor

/-! ## 7. Historical pooling through the actual protected-incumbent sort -/

section HistoricalPooling

open SEKernel.ScorePooling

/-- **Doc B B4.4 adapter, pointwise.** One newcomer copy of `g`, `P - 1`
incumbent copies with strictly more evaluations, `1 ≤ S ≤ P - 1`. Under the
actual protected-incumbent sort the newcomer is retained exactly on
ScorePooling's strict historical-win event. -/
theorem historical_sort_retains_iff {G : Type*} {P S m : ℕ} (hSP : S ≤ P) (hS : 0 < S)
    (hSP1 : S ≤ P - 1) (roster : Fin P → G) (g : G) (hone : blockSize roster g = 1)
    (evaluations : Fin P → ℕ)
    (hinc : ∀ i j, roster i ≠ g → roster j = g → evaluations j < evaluations i)
    (ω : Bool × (Fin m → Bool)) :
    survivorCount roster (lexSurvivors hSP
      (pooledScore roster g (currentScore ω) (historicalScore ω)) (incumbentKey evaluations)) g =
      if historicalScore ω < currentScore ω then 1 else 0 := by
  rcases lt_trichotomy (historicalScore ω) (currentScore ω) with h | h | h
  · rw [if_pos h, pooled_count_ahead' hSP roster g h, hone]
    omega
  · rw [if_neg (lt_irrefl _ |> fun hn => by rw [h] at *; exact hn), h, pooledScore_tie,
      incumbent_tied_count_B hSP _ evaluations roster g hinc]
    unfold blockSize at hone
    rw [hone]
    omega
  · rw [if_neg (not_lt_of_gt h), pooled_count_behind' hSP roster g h, hone]
    omega

/-- **Doc B B4.4 adapter, in law.** The actual survivor law (overlap score
law, then the protected-incumbent kernel) gives the newcomer the expected
survivor share `newcomerSurvivorShare`, hence `(1/2)(1 - (1/2)^m)/S`. -/
theorem historical_actual_share {G : Type*} {P S m : ℕ} (hSP : S ≤ P) (hS : 0 < S)
    (hSP1 : S ≤ P - 1) (roster : Fin P → G) (g : G) (hone : blockSize roster g = 1)
    (evaluations : Fin P → ℕ)
    (hinc : ∀ i j, roster i ≠ g → roster j = g → evaluations j < evaluations i) :
    ((overlapLaw m).bind fun ω => incumbentSelectionLaw hSP
        (pooledScore roster g (currentScore ω) (historicalScore ω)) evaluations).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      (overlapLaw m).expect (newcomerSurvivorShare S) ∧
    ((overlapLaw m).bind fun ω => incumbentSelectionLaw hSP
        (pooledScore roster g (currentScore ω) (historicalScore ω)) evaluations).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      ((1/2 : ℝ) * (1 - (1/2 : ℝ)^m)) / S := by
  have h1 : ((overlapLaw m).bind fun ω => incumbentSelectionLaw hSP
        (pooledScore roster g (currentScore ω) (historicalScore ω)) evaluations).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      (overlapLaw m).expect (newcomerSurvivorShare S) := by
    rw [Law.expect_bind]
    congr 1
    funext ω
    rw [incumbentSelectionLaw_eq]
    unfold tieSelectionLaw
    rw [Law.expect_map, pointLaw_expect,
      historical_sort_retains_iff hSP hS hSP1 roster g hone evaluations hinc ω]
    unfold newcomerSurvivorShare
    split_ifs <;> simp
  exact ⟨h1, h1.trans (historical_expected_share m S)⟩

/-- Under current common-pool ranking all copies share the current score, so
the protected incumbents take every slot: the newcomer never survives. -/
theorem current_pool_newcomer_never_survives {G : Type*} {P S m : ℕ} (hSP : S ≤ P)
    (hSP1 : S ≤ P - 1) (roster : Fin P → G) (g : G) (hone : blockSize roster g = 1)
    (evaluations : Fin P → ℕ)
    (hinc : ∀ i j, roster i ≠ g → roster j = g → evaluations j < evaluations i)
    (ω : Bool × (Fin m → Bool)) :
    survivorCount roster (lexSurvivors hSP
      (pooledScore roster g (currentScore ω) (currentScore ω)) (incumbentKey evaluations)) g = 0 := by
  rw [pooledScore_tie, incumbent_tied_count_B hSP _ evaluations roster g hinc]
  unfold blockSize at hone
  rw [hone]
  omega

/-- **Doc B B4.4 numerical instance on the actual sort**: `P = 12`, `S = 4`,
`N = 3` evaluations (`m = 2` past pools): expected newcomer survivor share
`3/32 > 1/12`, and zero under current-pool ranking. -/
theorem historical_actual_instance (evaluations : Fin 12 → ℕ)
    (hinc : ∀ i j, newcomerRoster i ≠ true → newcomerRoster j = true →
      evaluations j < evaluations i) :
    ((overlapLaw 2).bind fun ω => incumbentSelectionLaw h412
        (pooledScore newcomerRoster true (currentScore ω) (historicalScore ω)) evaluations).expect
        (fun A => (survivorCount newcomerRoster A true : ℝ) / 4) = 3/32 ∧
    (3:ℝ)/32 > 1/12 ∧
    ((overlapLaw 2).bind fun ω => incumbentSelectionLaw h412
        (pooledScore newcomerRoster true (currentScore ω) (currentScore ω)) evaluations).expect
        (fun A => (survivorCount newcomerRoster A true : ℝ) / 4) = 0 := by
  refine ⟨?_, by norm_num, ?_⟩
  · have h := (historical_actual_share (m := 2) h412 (by norm_num) (by norm_num)
      newcomerRoster true newcomerRoster_block evaluations hinc).2
    simp only [Nat.cast_ofNat] at h
    rw [h]
    norm_num
  · rw [Law.expect_bind]
    have hz : ∀ ω : Bool × (Fin 2 → Bool), (incumbentSelectionLaw h412
        (pooledScore newcomerRoster true (currentScore ω) (currentScore ω)) evaluations).expect
        (fun A => (survivorCount newcomerRoster A true : ℝ) / 4) = 0 := by
      intro ω
      rw [incumbentSelectionLaw_eq]
      unfold tieSelectionLaw
      rw [Law.expect_map, pointLaw_expect,
        current_pool_newcomer_never_survives h412 (by norm_num) newcomerRoster true
          newcomerRoster_block evaluations hinc ω]
      simp
    simp_rw [hz]
    exact Law.expect_const _ _

end HistoricalPooling

/-! ## 8. Total variance under task heterogeneity; covariance/affine adapters -/

section Variance

/-- Finite law of total variance for a two-stage draw (task, then outcome). -/
theorem total_variance {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (τ : Law Ω)
    (K : Ω → Law Λ) (X : Λ → ℝ) :
    (τ.bind K).variance X =
      τ.variance (fun t => (K t).expect X) + τ.expect (fun t => (K t).variance X) := by
  rw [Law.variance_eq, Law.variance_eq, Law.expect_bind, Law.expect_bind]
  have hv : (fun t => (K t).variance X) =
      fun t => (K t).expect (fun ω => X ω ^ 2) - (K t).expect X ^ 2 := by
    funext t
    exact Law.variance_eq _ _
  rw [hv, Law.expect_sub]
  ring

/-- **Doc A B6.2.** Boards are iid two-stage draws: a task from `τ`, then the
paired difference `D` from `K task`. The variance of the `n`-board mean is
the between-task variance of `Δ(t) = E[D|t]` plus the mean within-task
variance, divided by `n`. -/
theorem task_heterogeneity_variance {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] {n : ℕ}
    (hn : 0 < n) (τ : Law Ω) (K : Ω → Law Λ) (D : Λ → ℝ) :
    (Law.pi (fun _ : Fin n => τ.bind K)).variance (fun z => (∑ i, D (z i)) / n) =
      (τ.variance (fun t => (K t).expect D) + τ.expect (fun t => (K t).variance D)) / n := by
  rw [(Law.iid_average hn (τ.bind K) D).2, total_variance]

/-- Finite frequency-weighted covariance and variance. -/
def covX {G : Type*} [Fintype G] (x f r : G → ℝ) : ℝ :=
  (∑ g, x g * f g * r g) - (∑ g, x g * f g) * (∑ g, x g * r g)

def varX {G : Type*} [Fintype G] (x f : G → ℝ) : ℝ :=
  (∑ g, x g * f g ^ 2) - (∑ g, x g * f g) ^ 2

/-- The actual current genotype frequencies of a roster. -/
noncomputable def rosterFreq {P : ℕ} {G : Type*} (roster : Fin P → G) (g : G) : ℝ :=
  (blockSize roster g : ℝ) / P

theorem blockSize_sum {P : ℕ} {G : Type*} [Fintype G] (roster : Fin P → G) :
    ∑ g, blockSize roster g = P := by
  unfold blockSize
  have h := Finset.card_eq_sum_card_fiberwise (f := roster) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

theorem rosterFreq_sum {P : ℕ} {G : Type*} [Fintype G] (hP : 0 < P)
    (roster : Fin P → G) : ∑ g, rosterFreq roster g = 1 := by
  unfold rosterFreq
  rw [← Finset.sum_div]
  have h := blockSize_sum roster
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hP
  rw [show (∑ g, (blockSize roster g : ℝ)) = P by exact_mod_cast h, div_self hp]

/-- Per-copy expected survival weight of a genotype (zero when absent). -/
noncomputable def survivalWeight {P S : ℕ} {G : Type*} [Fintype G]
    (L : Law (Survivors P S)) (roster : Fin P → G) (g : G) : ℝ :=
  if blockSize roster g = 0 then 0 else expectedSurvivorCount L roster g / blockSize roster g

theorem freq_mul_survivalWeight {P S : ℕ} {G : Type*} [Fintype G] (hP : 0 < P)
    (L : Law (Survivors P S)) (roster : Fin P → G) (g : G) :
    rosterFreq roster g * survivalWeight L roster g = expectedSurvivorCount L roster g / P := by
  unfold rosterFreq survivalWeight
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hP
  by_cases hb : blockSize roster g = 0
  · rw [if_pos hb]
    have habs : ∀ i, roster i ≠ g := by
      intro i hi
      unfold blockSize at hb
      have : i ∈ Finset.univ.filter (fun i => roster i = g) := by simp [hi]
      rw [Finset.card_eq_zero] at hb
      rw [hb] at this
      simp at this
    rw [expectedSurvivorCount_absent L roster g habs]
    simp
  · rw [if_neg hb]
    have hb' : (blockSize roster g : ℝ) ≠ 0 := by exact_mod_cast hb
    field_simp

/-- **Doc B B5.1 / Doc A B5.1, covariance form on the actual survivor law.**
With `r̄ = S/P`, the expected survivor-mean change equals `Cov_x(f, r)/r̄`,
where `r` is the per-copy expected survival weight; zero weights allowed. -/
theorem survivor_covariance_identity {P S : ℕ} {G : Type*} [Fintype G] (hP : 0 < P)
    (hS : 0 < S) (L : Law (Survivors P S)) (roster : Fin P → G) (f : G → ℝ) :
    L.expect (survivorMean roster f) - ∑ g, rosterFreq roster g * f g =
      covX (rosterFreq roster) f (survivalWeight L roster) / ((S : ℝ) / P) := by
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hP
  have hprice := price_count_identity hS L roster (rosterFreq roster) f
  have hxr : ∀ g, rosterFreq roster g * f g * survivalWeight L roster g =
      f g * (expectedSurvivorCount L roster g / P) := by
    intro g
    rw [mul_comm (rosterFreq roster g) (f g), mul_assoc, freq_mul_survivalWeight hP]
  have hsumr : ∑ g, rosterFreq roster g * survivalWeight L roster g = (S : ℝ) / P := by
    simp_rw [freq_mul_survivalWeight hP]
    rw [← Finset.sum_div, expectedSurvivorCount_sum]
  unfold covX
  simp_rw [hxr]
  rw [hsumr]
  have hB : ∑ g, f g * (expectedSurvivorCount L roster g / P) =
      (∑ g, expectedSurvivorCount L roster g * f g) / P := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    ring
  have hpr : ∑ g, (expectedSurvivorCount L roster g - S * rosterFreq roster g) * f g =
      (∑ g, expectedSurvivorCount L roster g * f g) - S * ∑ g, rosterFreq roster g * f g := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [hpr] at hprice
  have hE : L.expect (survivorMean roster f) - ∑ g, rosterFreq roster g * f g =
      ((∑ g, expectedSurvivorCount L roster g * f g) -
        S * ∑ g, rosterFreq roster g * f g) / S := by
    rw [← hprice]
    field_simp
  rw [hB, hE]
  field_simp

/-- **Doc B B5.2 (affine survival weights).** If every genotype's expected
survivor count is its copy number times `a + b f_g`, the expected survivor
selection gain is `b Var_x(f) / r̄` with `r̄ = S/P`. -/
theorem affine_survival_variance {P S : ℕ} {G : Type*} [Fintype G] (hP : 0 < P)
    (hS : 0 < S) (L : Law (Survivors P S)) (roster : Fin P → G) (f : G → ℝ) (a b : ℝ)
    (haff : ∀ g, expectedSurvivorCount L roster g = (blockSize roster g : ℝ) * (a + b * f g)) :
    L.expect (survivorMean roster f) - ∑ g, rosterFreq roster g * f g =
      b * varX (rosterFreq roster) f / ((S : ℝ) / P) := by
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hP
  have hN : ∀ g, expectedSurvivorCount L roster g = P * rosterFreq roster g * (a + b * f g) := by
    intro g
    rw [haff g]
    unfold rosterFreq
    field_simp
  have hx1 := rosterFreq_sum hP roster
  have htot : (∑ g, (P : ℝ) * rosterFreq roster g * (a + b * f g)) = S := by
    simp_rw [← hN]
    exact expectedSurvivorCount_sum L roster
  have hcon : (P : ℝ) * a + P * b * (∑ g, rosterFreq roster g * f g) = S := by
    have hexp : (∑ g, (P : ℝ) * rosterFreq roster g * (a + b * f g)) =
        P * a * (∑ g, rosterFreq roster g) + P * b * (∑ g, rosterFreq roster g * f g) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      ring
    rw [hexp, hx1, mul_one] at htot
    exact htot
  have hprice := price_count_identity hS L roster (rosterFreq roster) f
  simp_rw [hN] at hprice
  have hrhs : (∑ g, ((P : ℝ) * rosterFreq roster g * (a + b * f g) - S * rosterFreq roster g) * f g) =
      ((P : ℝ) * a - S) * (∑ g, rosterFreq roster g * f g) +
        P * b * (∑ g, rosterFreq roster g * f g ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [hrhs] at hprice
  unfold varX
  have hPa : (P : ℝ) * a - S = -(P * b * (∑ g, rosterFreq roster g * f g)) := by linarith
  rw [hPa] at hprice
  field_simp
  linear_combination hprice

end Variance

/-! ## 9. Multi-generation: the incumbent floor against the uniform control -/

section MultiGeneration

open MutationBaseline SEKernel.ScorePooling

/-- The next roster: retained survivors occupy slots `0..S-1` (in a fixed
enumeration of the survivor set), offspring occupy slots `S..P-1`. Only the
board/voter phenotype (`true` = board) of each slot is tracked. -/
noncomputable def nextRoster {P S : ℕ} (hSP : S ≤ P) (z : Fin P → Bool) (B : Survivors P S)
    (o : Fin (P - S) → Bool) : Fin P → Bool :=
  fun k => Fin.append (fun i : Fin S => z ((Finset.equivFinOfCardEq B.property).symm i).val) o
    (Fin.cast (Nat.add_sub_cancel' hSP).symm k)

theorem nextRoster_sum {P S : ℕ} (hSP : S ≤ P) (z : Fin P → Bool) (B : Survivors P S)
    (o : Fin (P - S) → Bool) (F : Bool → ℝ) :
    ∑ k, F (nextRoster hSP z B o k) = ∑ i ∈ B.val, F (z i) + ∑ j, F (o j) := by
  unfold nextRoster
  have h1 := Equiv.sum_comp (finCongr (Nat.add_sub_cancel' hSP).symm)
    (fun m => F (Fin.append
      (fun i : Fin S => z ((Finset.equivFinOfCardEq B.property).symm i).val) o m))
  simp only [finCongr_apply] at h1
  rw [h1, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  congr 1
  have h2 := Equiv.sum_comp (Finset.equivFinOfCardEq B.property).symm
    (fun x : B.val => F (z x.val))
  rw [h2]
  exact Finset.sum_coe_sort B.val (fun i => F (z i))

theorem blockSize_true_sum {n : ℕ} (z : Fin n → Bool) :
    (blockSize z true : ℝ) = ∑ k, bit (z k) := by
  unfold blockSize
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rcases Bool.eq_false_or_eq_true (z k) with h | h <;> simp [h, bit]

theorem blockSize_false_sum {n : ℕ} (z : Fin n → Bool) :
    (blockSize z false : ℝ) = ∑ k, (1 - bit (z k)) := by
  unfold blockSize
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rcases Bool.eq_false_or_eq_true (z k) with h | h <;> simp [h, bit]

theorem survivorCount_true_sum {P S : ℕ} (z : Fin P → Bool) (B : Survivors P S) :
    (survivorCount z B true : ℝ) = ∑ i ∈ B.val, bit (z i) := by
  unfold survivorCount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rcases Bool.eq_false_or_eq_true (z k) with h | h <;> simp [h, bit]

theorem survivorCount_false_sum {P S : ℕ} (z : Fin P → Bool) (B : Survivors P S) :
    (survivorCount z B false : ℝ) = ∑ i ∈ B.val, (1 - bit (z i)) := by
  unfold survivorCount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rcases Bool.eq_false_or_eq_true (z k) with h | h <;> simp [h, bit]

/-- The board share of a phenotype roster. -/
noncomputable def boardShare {P : ℕ} (z : Fin P → Bool) : ℝ := (blockSize z true : ℝ) / P

theorem boardShare_nextRoster {P S : ℕ} (hS : 0 < S) (hSP : S ≤ P) (z : Fin P → Bool)
    (B : Survivors P S) (o : Fin (P - S) → Bool) :
    boardShare (nextRoster hSP z B o) =
      ((S : ℝ) * boardFraction z B + ∑ j, (if o j then (1:ℝ) else 0)) / P := by
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  unfold boardShare boardFraction
  rw [blockSize_true_sum, nextRoster_sum hSP z B o bit, ← survivorCount_true_sum]
  congr 1
  rw [mul_div_cancel₀ _ hs]
  rfl

/-- One generation as a kernel on phenotype rosters: a survivor law `sel z`,
then `P - S` independent offspring drawn from the offspring law `off z B`,
then the next roster (survivors first, offspring appended). -/
noncomputable def genKernel {P S : ℕ} (hSP : S ≤ P)
    (sel : (Fin P → Bool) → Law (Survivors P S))
    (off : (Fin P → Bool) → Survivors P S → Law Bool) (z : Fin P → Bool) :
    Law (Fin P → Bool) :=
  (sel z).bind (fun B => (Law.pi (fun _ : Fin (P - S) => off z B)).map (nextRoster hSP z B))

/-- The offspring law as the MutationBaseline interface: board with the
transmission probability at the survivor board fraction. -/
noncomputable def interfaceOff {P S : ℕ} (hS : 0 < S) (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (z : Fin P → Bool) (B : Survivors P S) : Law Bool :=
  offspringLaw u d (boardFraction z B) hu hu' hd hd'
    (boardFraction_bounds hS z B).1 (boardFraction_bounds hS z B).2

theorem interfaceOff_mean {P S : ℕ} (hS : 0 < S) (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (z : Fin P → Bool) (B : Survivors P S) :
    (interfaceOff hS u d hu hu' hd hd' z B).expect (fun b => if b then (1:ℝ) else 0) =
      mutationProbability u d (boardFraction z B) :=
  offspring_mean _ _ _ _ _ _ _ _ _

/-- Post-mutation board probability given the pre-mutation phenotype. -/
noncomputable def mutateProb (u d : ℝ) (a : Bool) : ℝ := if a then 1 - d else u

theorem mutateProb_bounds {u d : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1)
    (a : Bool) : 0 ≤ mutateProb u d a ∧ mutateProb u d a ≤ 1 := by
  unfold mutateProb
  cases a <;> simp <;> constructor <;> linarith

theorem survivors_nonempty {P S : ℕ} (hS : 0 < S) (B : Survivors P S) : Nonempty B.val := by
  have hpos : 0 < B.val.card := by rw [B.property]; exact hS
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact ⟨⟨x, hx⟩⟩

/-- **The explicit offspring mechanism**: two parents drawn independently and
uniformly from the survivors, a fair crossover coin chooses which parent
donates the phenotype-locus allele, then mutation (voter→board `u`,
board→voter `d`). -/
noncomputable def crossoverOff {P S : ℕ} (hS : 0 < S) (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (z : Fin P → Bool) (B : Survivors P S) : Law Bool :=
  haveI := survivors_nonempty hS B
  (uniformLaw (B.val × B.val × Bool)).bind (fun q =>
    bernoulli (mutateProb u d (z (if q.2.2 then q.1 else q.2.1).val))
      (mutateProb_bounds hu hu' hd hd' _).1 (mutateProb_bounds hu hu' hd hd' _).2)

/-- Uniform two-parent crossover preserves the survivor board marginal, so the
explicit mechanism has the B1 transmission probability. -/
theorem crossoverOff_mean {P S : ℕ} (hS : 0 < S) (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (z : Fin P → Bool) (B : Survivors P S) :
    (crossoverOff hS u d hu hu' hd hd' z B).expect (fun b => if b then (1:ℝ) else 0) =
      mutationProbability u d (boardFraction z B) := by
  haveI := survivors_nonempty hS B
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  unfold crossoverOff
  rw [Law.expect_bind]
  simp_rw [bernoulli_mean]
  rw [uniform_expect]
  have hcard : (Fintype.card (B.val × B.val × Bool) : ℝ) = (S : ℝ) * S * 2 := by
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, B.property]
    push_cast
    ring
  have hsum : (∑ q : B.val × B.val × Bool,
      mutateProb u d (z (if q.2.2 then q.1 else q.2.1).val)) =
      2 * S * ∑ p : B.val, mutateProb u d (z p.val) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, B.property, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hB : (∑ p : B.val, mutateProb u d (z p.val)) =
      (1 - d) * (survivorCount z B true : ℝ) + u * (survivorCount z B false : ℝ) := by
    rw [Finset.sum_coe_sort B.val (fun i => mutateProb u d (z i)),
      survivorCount_true_sum, survivorCount_false_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases Bool.eq_false_or_eq_true (z i) with h | h <;> simp [h, mutateProb, SEKernel.ScorePooling.bit]
  have htot := survivorCount_sum z B
  rw [Fintype.sum_bool] at htot
  have htotR : (survivorCount z B true : ℝ) + (survivorCount z B false : ℝ) = S := by
    exact_mod_cast htot
  rw [hcard, hsum, hB]
  unfold mutationProbability boardFraction
  have hf : (survivorCount z B false : ℝ) = S - survivorCount z B true := by linarith
  rw [hf]
  field_simp
  ring

theorem genKernel_share {P S : ℕ} (hS : 0 < S) (hSP : S ≤ P)
    (sel : (Fin P → Bool) → Law (Survivors P S))
    (off : (Fin P → Bool) → Survivors P S → Law Bool) (u d : ℝ) (z : Fin P → Bool)
    (hoff : ∀ B, (off z B).expect (fun b => if b then (1:ℝ) else 0) =
      mutationProbability u d (boardFraction z B)) :
    (genKernel hSP sel off z).expect boardShare =
      affineStep ((P - S : ℕ) / (P : ℝ)) u d ((sel z).expect (boardFraction z)) := by
  have hP : 0 < P := lt_of_lt_of_le hS hSP
  unfold genKernel
  rw [Law.expect_bind, ← MutationBaseline.expect_affineStep]
  congr 1
  funext B
  rw [Law.expect_map]
  simp_rw [boardShare_nextRoster hS hSP z B]
  have hX : ∀ j : Fin (P - S), (Law.pi (fun _ : Fin (P - S) => off z B)).expect
      (fun o => if o j then (1:ℝ) else 0) = mutationProbability u d (boardFraction z B) := by
    intro j
    rw [Law.expect_pi_coord (fun _ : Fin (P - S) => off z B) j
        (fun b => if b then (1:ℝ) else 0)]
    exact hoff B
  exact finite_population_transmission (Law.pi (fun _ : Fin (P - S) => off z B)) P S hP hSP
    u d (boardFraction z B) (fun j o => if o j then (1:ℝ) else 0) hX

/-- The law of the roster at generation `t` (generation `0` is `z0`). -/
noncomputable def chainLaw {Z : Type*} [Fintype Z] (K : Z → Law Z) (z0 : Z) : ℕ → Law Z
  | 0 => pointLaw z0
  | t + 1 => (chainLaw K z0 t).bind K

theorem expect_congr_support {Ω : Type*} [Fintype Ω] (L : Law Ω) (F H : Ω → ℝ)
    (h : ∀ ω, L.mass ω ≠ 0 → F ω = H ω) : L.expect F = L.expect H := by
  unfold Law.expect Law1.mean
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hm : L.mass ω = 0
  · simp [hm]
  · rw [h ω hm]

theorem bind_support {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (L : Law Ω) (K : Ω → Law Λ)
    (η : Λ) (h : (L.bind K).mass η ≠ 0) : ∃ ω, L.mass ω ≠ 0 ∧ (K ω).mass η ≠ 0 := by
  have h' : ∑ ω, L.mass ω * (K ω).mass η ≠ 0 := h
  obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
  exact ⟨ω, left_ne_zero_of_mul hω, right_ne_zero_of_mul hω⟩

theorem map_support {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (L : Law Ω) (f : Ω → Λ)
    (η : Λ) (h : (L.map f).mass η ≠ 0) : ∃ ω, f ω = η := by
  by_contra hne
  push_neg at hne
  apply h
  show L.prob (fun ω => f ω = η) = 0
  have he : (fun ω => f ω = η) = fun _ => False := funext (fun ω => propext ⟨hne ω, False.elim⟩)
  rw [he]
  exact Law.prob_false L

/-- The selection arm under identical scores: a fixed phenotype priority key
`prio z` pushed through the actual sort. -/
noncomputable def floorSel {P S : ℕ} (hSP : S ≤ P) (c : ℝ)
    (prio : (Fin P → Bool) → Fin P → ℤ) (z : Fin P → Bool) : Law (Survivors P S) :=
  tieSelectionLaw hSP (fun _ => c) (fun _ : Unit => prio z) (pointLaw ())

/-- The control arm: identical scores and the uniform slot-permutation tie law
(the survivors are `π⁻¹{0,…,S-1}` for a uniform permutation `π`, so every slot
is retained with probability `S/P`; see `slot_tied_survivors`). -/
noncomputable def controlSel {P S : ℕ} (hSP : S ≤ P) (c : ℝ) (_z : Fin P → Bool) :
    Law (Survivors P S) :=
  slotTieSelectionLaw hSP (fun _ => c)

/-- Persistence: from a roster with at least `S` voters, every roster reachable
in one floor generation again has at least `S` voters. -/
theorem floor_kernel_support {P S : ℕ} (hSP : S ≤ P) (c : ℝ)
    (prio : (Fin P → Bool) → Fin P → ℤ)
    (hprio : ∀ z i j, z i = false → z j = true → prio z i < prio z j)
    (off : (Fin P → Bool) → Survivors P S → Law Bool)
    (w : Fin P → Bool) (hw : S ≤ blockSize w false) (z : Fin P → Bool)
    (hz : (genKernel hSP (floorSel hSP c prio) off w).mass z ≠ 0) :
    S ≤ blockSize z false := by
  obtain ⟨B, hB, hBz⟩ := bind_support _ _ z hz
  obtain ⟨o, ho⟩ := map_support _ _ z hBz
  obtain ⟨_, hBeq⟩ := map_support _ _ B hB
  have hnb : survivorCount w B true = 0 := by
    rw [← hBeq]
    exact identical_outcomes_no_board hSP c (prio w) w (hprio w) hw
  have hsum := survivorCount_sum w B
  rw [Fintype.sum_bool] at hsum
  have hfalse : survivorCount w B false = S := by omega
  have hreal : (S : ℝ) ≤ (blockSize z false : ℝ) := by
    rw [← ho, blockSize_false_sum, nextRoster_sum hSP w B o (fun b => 1 - bit b),
      ← survivorCount_false_sum, hfalse]
    have : 0 ≤ ∑ j, (1 - bit (o j)) := Finset.sum_nonneg (fun j _ => by
      rcases Bool.eq_false_or_eq_true (o j) with h | h <;> simp [h, bit])
    linarith
  exact_mod_cast hreal

theorem floor_chain_support {P S : ℕ} (hSP : S ≤ P) (c : ℝ)
    (prio : (Fin P → Bool) → Fin P → ℤ)
    (hprio : ∀ z i j, z i = false → z j = true → prio z i < prio z j)
    (off : (Fin P → Bool) → Survivors P S → Law Bool)
    (z0 : Fin P → Bool) (h0 : S ≤ blockSize z0 false) (t : ℕ) (z : Fin P → Bool)
    (hz : (chainLaw (genKernel hSP (floorSel hSP c prio) off) z0 t).mass z ≠ 0) :
    S ≤ blockSize z false := by
  induction t generalizing z with
  | zero =>
    change (pointLaw z0).mass z ≠ 0 at hz
    by_cases he : z = z0
    · rw [he]; exact h0
    · exact absurd (by simp [pointLaw, he] : (pointLaw z0).mass z = 0) hz
  | succ t ih =>
    obtain ⟨w, hw, hwz⟩ := bind_support _ _ z hz
    exact floor_kernel_support hSP c prio hprio off w (ih w hw) z hwz

/-- **Doc B B3.3 / Doc A B3.2, every generation.** Identical scores, a
persistent voter-first priority, and at least `S` voters initially: at every
generation `t ≥ 1` the expected board share is exactly the floor `r u`. -/
theorem floor_chain_share {P S : ℕ} (hS : 0 < S) (hSP : S ≤ P) (c : ℝ)
    (prio : (Fin P → Bool) → Fin P → ℤ)
    (hprio : ∀ z i j, z i = false → z j = true → prio z i < prio z j)
    (u d : ℝ) (off : (Fin P → Bool) → Survivors P S → Law Bool)
    (hoff : ∀ z B, (off z B).expect (fun b => if b then (1:ℝ) else 0) =
      mutationProbability u d (boardFraction z B))
    (z0 : Fin P → Bool) (h0 : S ≤ blockSize z0 false) (t : ℕ) :
    (chainLaw (genKernel hSP (floorSel hSP c prio) off) z0 (t + 1)).expect
      boardShare = ((P - S : ℕ) / (P : ℝ)) * u := by
  change ((chainLaw _ z0 t).bind _).expect boardShare = _
  rw [Law.expect_bind]
  have hpt : ∀ w, (chainLaw (genKernel hSP (floorSel hSP c prio) off) z0 t).mass w ≠ 0 →
      (genKernel hSP (floorSel hSP c prio) off w).expect boardShare =
        ((P - S : ℕ) / (P : ℝ)) * u := by
    intro w hw
    have hvw := floor_chain_support hSP c prio hprio off z0 h0 t w hw
    rw [genKernel_share hS hSP _ off u d w (hoff w)]
    have hzero : (floorSel hSP c prio w).expect (boardFraction w) = 0 := by
      unfold floorSel tieSelectionLaw
      rw [Law.expect_map, pointLaw_expect]
      unfold boardFraction
      rw [identical_outcomes_no_board hSP c (prio w) w (hprio w) hvw]
      simp
    rw [hzero]
    unfold affineStep
    ring
  rw [expect_congr_support _ _ _ hpt, Law.expect_const]

/-- **The control arm follows the random-survival recursion of means.** -/
theorem control_chain_share {P S : ℕ} (hS : 0 < S) (hSP : S ≤ P) (c : ℝ)
    (u d : ℝ) (off : (Fin P → Bool) → Survivors P S → Law Bool)
    (hoff : ∀ z B, (off z B).expect (fun b => if b then (1:ℝ) else 0) =
      mutationProbability u d (boardFraction z B))
    (z0 : Fin P → Bool) (t : ℕ) :
    (chainLaw (genKernel hSP (controlSel hSP c) off) z0 t).expect boardShare =
      meanTrajectory ((P - S : ℕ) / (P : ℝ)) u d (boardShare z0) t := by
  have hP : 0 < P := lt_of_lt_of_le hS hSP
  have hstep : ∀ w, (genKernel hSP (controlSel hSP c) off w).expect boardShare =
      affineStep ((P - S : ℕ) / (P : ℝ)) u d (boardShare w) := by
    intro w
    rw [genKernel_share hS hSP _ off u d w (hoff w)]
    congr 1
    have h := (slot_ties_restore_baseline hS hSP (pointLaw ()) (fun _ => fun _ => c)
      (fun _ _ _ => rfl) w 0 0 le_rfl zero_le_one le_rfl zero_le_one).1
    rw [Law.expect_bind, pointLaw_expect] at h
    exact h
  induction t with
  | zero =>
    change (pointLaw z0).expect boardShare = _
    rw [pointLaw_expect]
    rfl
  | succ t ih =>
    change ((chainLaw _ z0 t).bind _).expect boardShare = _
    rw [Law.expect_bind]
    simp_rw [hstep]
    rw [MutationBaseline.expect_affineStep, ih]
    rfl

/-- The all-voter initial roster. -/
def allVoters (P : ℕ) : Fin P → Bool := fun _ => false

theorem allVoters_block (P : ℕ) : blockSize (allVoters P) false = P ∧
    blockSize (allVoters P) true = 0 := by
  unfold blockSize allVoters
  constructor
  · simp
  · simp

/-- The explicit protocol's offspring law at the experiment's rates. -/
noncomputable def expOff (z : Fin 12 → Bool) (B : Survivors 12 4) : Law Bool :=
  crossoverOff (by norm_num : 0 < 4) (3/25) (3/125) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) z B

/-- **Doc B B3.3 numerical comparison on the two actual chains** (`P = 12`,
`S = 4`, two-parent uniform crossover then mutation with `u = 3/25`,
`d = 3/125`, from pure voters): the floor arm has mean board share `2/25` at
every `t ≥ 1`; the control arm has `(5/6)(1 - (113/125)^t)`; they agree at
`t = 1` and the floor is strictly below the control at every `t ≥ 2`. -/
theorem floor_vs_control_instance (c : ℝ) (prio : (Fin 12 → Bool) → Fin 12 → ℤ)
    (hprio : ∀ z i j, z i = false → z j = true → prio z i < prio z j) (t : ℕ) :
    (chainLaw (genKernel h412 (floorSel h412 c prio) expOff) (allVoters 12) (t + 1)).expect
        boardShare = 2/25 ∧
    (chainLaw (genKernel h412 (controlSel h412 c) expOff) (allVoters 12) t).expect
        boardShare = (5/6) * (1 - (113/125)^t) ∧
    (1 ≤ t → (2:ℝ)/25 < (chainLaw (genKernel h412 (controlSel h412 c) expOff)
        (allVoters 12) (t + 1)).expect boardShare) := by
  have h0 : 4 ≤ blockSize (allVoters 12) false := by rw [(allVoters_block 12).1]; norm_num
  have hb0 : boardShare (allVoters 12) = 0 := by
    unfold boardShare
    rw [(allVoters_block 12).2]
    simp
  have hr : (((12 - 4 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = 2/3 := by norm_num
  have hoff : ∀ z B, (expOff z B).expect (fun b => if b then (1:ℝ) else 0) =
      mutationProbability (3/25) (3/125) (boardFraction z B) :=
    fun z B => crossoverOff_mean _ _ _ _ _ _ _ z B
  refine ⟨?_, ?_, ?_⟩
  · rw [floor_chain_share (by norm_num) h412 c prio hprio _ _ expOff hoff _ h0 t, hr]
    norm_num
  · rw [control_chain_share (by norm_num) h412 c _ _ expOff hoff _ t, hb0, hr,
      experiment_trajectory]
  · intro ht
    rw [control_chain_share (by norm_num) h412 c _ _ expOff hoff _ (t + 1), hb0, hr]
    exact (floor_below_control (t + 1) (by omega)).2.2

end MultiGeneration

/-! ## 10. Non-vacuity and the B2.10 control contrast -/

section Extras

open MutationBaseline

/-- A concrete persistent voter-first priority (boards rank after voters). -/
def voterFirst {P : ℕ} (z : Fin P → Bool) (i : Fin P) : ℤ := if z i then 1 else 0

theorem voterFirst_prio {P : ℕ} (z : Fin P → Bool) (i j : Fin P) (hi : z i = false)
    (hj : z j = true) : voterFirst z i < voterFirst z j := by
  simp [voterFirst, hi, hj]

/-- `floor_vs_control_instance` with the concrete voter-first key: its
priority hypothesis is satisfiable. -/
theorem floor_vs_control_voterFirst (c : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    (chainLaw (genKernel h412 (floorSel h412 c voterFirst) expOff) (allVoters 12) (t + 1)).expect
        boardShare = 2/25 ∧
    (2:ℝ)/25 < (chainLaw (genKernel h412 (controlSel h412 c) expOff)
        (allVoters 12) (t + 1)).expect boardShare := by
  have h := floor_vs_control_instance c voterFirst voterFirst_prio t
  exact ⟨h.1, h.2.2 ht⟩

/-- With state-dependent evaluation counts, the floor selection law IS the
actual protected-incumbent law, and evaluation priority of voters over boards
in every state supplies the persistent voter-first hypothesis. -/
theorem floorSel_incumbent {P S : ℕ} (hSP : S ≤ P) (c : ℝ)
    (ev : (Fin P → Bool) → Fin P → ℕ) (z : Fin P → Bool) :
    floorSel hSP c (fun w => incumbentKey (ev w)) z =
      incumbentSelectionLaw hSP (fun _ => c) (ev z) := rfl

theorem incumbent_prio {P : ℕ} (ev : (Fin P → Bool) → Fin P → ℕ)
    (hev : ∀ z i j, z i = false → z j = true → ev z j < ev z i) :
    ∀ z i j, z i = false → z j = true →
      (fun w => incumbentKey (ev w)) z i < (fun w => incumbentKey (ev w)) z j := by
  intro z i j hi hj
  have := hev z i j hi hj
  simp only [incumbentKey]
  omega

/-- **Doc B (B2.10).** For any survivor law, the expected next board share
minus the uniform-slot-tie control at the same roster (identical scores) is
`β (E Y - x)`, with `β = 1 - r(u+d)`. -/
theorem selection_control_contrast {P S : ℕ} (hS : 0 < S) (hSP : S ≤ P)
    (sel : Law (Survivors P S)) (c : ℝ) (ph : Fin P → Bool)
    (u d : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    (generationLaw hS sel ph u d hu hu' hd hd').expect (nextBoardShare ph) -
      (generationLaw hS (slotTieSelectionLaw hSP (fun _ => c)) ph u d hu hu' hd hd').expect
        (nextBoardShare ph) =
      (1 - ((P - S : ℕ) / (P : ℝ)) * (u + d)) *
        (sel.expect (boardFraction ph) - (blockSize ph true : ℝ) / P) := by
  have hc := (slot_ties_restore_baseline hS hSP (pointLaw ()) (fun _ => fun _ => c)
    (fun _ _ _ => rfl) ph u d hu hu' hd hd').1
  rw [Law.expect_bind, pointLaw_expect] at hc
  rw [generation_expected_share hS hSP, generation_expected_share hS hSP, hc]
  unfold affineStep
  ring

end Extras

/-! ## 11. Tie-rule penalty, balanced sign, and the referee's balanced witness -/

section Balanced

/-- **Doc B B3.1 / Doc A B3.1 on the actual laws.** At the same score law,
uniform slot ties minus protected incumbents outside `g` change the expected
survivor share by exactly `τ (x - L/S)`. -/
theorem slot_minus_incumbent_actual {Ω G : Type*} [Fintype Ω] {P S : ℕ} (hSP : S ≤ P)
    (hP : 0 < P) (hS : 0 < S) (L : Law Ω) (roster : Fin P → G) (g : G) (sA sB : Ω → ℝ)
    (evaluations : Fin P → ℕ)
    (hinc : ∀ i j, roster i ≠ g → roster j = g → evaluations j < evaluations i) :
    (L.bind fun ω => slotTieSelectionLaw hSP (pooledScore roster g (sA ω) (sB ω))).expect
        (fun A => (survivorCount roster A g : ℝ) / S) -
      (L.bind fun ω =>
        incumbentSelectionLaw hSP (pooledScore roster g (sA ω) (sB ω)) evaluations).expect
        (fun A => (survivorCount roster A g : ℝ) / S) =
      L.prob (fun ω => sA ω = sB ω) *
        ((blockSize roster g : ℝ) / P - ((S - (P - blockSize roster g) : ℕ) : ℝ) / S) := by
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  rw [slot_master hSP hP, incumbent_master_B hSP L roster g sA sB evaluations hinc]
  field_simp
  ring

/-- The tie-rule penalty is strictly positive at interior abundance and
proper truncation: `S x > L` whenever `0 < K < P` and `0 < S < P`. -/
theorem tie_penalty_pos {P S K : ℕ} (hS : 0 < S) (hSP : S < P) (hK : 0 < K) (hKP : K < P) :
    ((S - (P - K) : ℕ) : ℝ) / S < (K : ℝ) / P := by
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  have hp : (0:ℝ) < P := by exact_mod_cast (lt_trans hS hSP)
  rw [div_lt_div_iff₀ hs hp]
  by_cases hle : S ≤ P - K
  · rw [Nat.sub_eq_zero_of_le hle]
    simp only [Nat.cast_zero, zero_mul]
    have : (0:ℝ) < K := by exact_mod_cast hK
    positivity
  · have hlt : P - K < S := lt_of_not_ge hle
    have hcast : ((S - (P - K) : ℕ) : ℝ) = (S : ℝ) + K - P := by
      rw [Nat.cast_sub hlt.le, Nat.cast_sub hKP.le]
      ring
    rw [hcast]
    have h1 : (0:ℝ) < (P : ℝ) - S := by
      have : (S : ℝ) < P := by exact_mod_cast hSP
      linarith
    have h2 : (0:ℝ) < (P : ℝ) - K := by
      have : (K : ℝ) < P := by exact_mod_cast hKP
      linarith
    nlinarith [mul_pos h1 h2]

/-- **Doc A B5.3 / Doc B B5.4, composed on the actual law.** Balanced pooled
counts (`K = P/2`, `P` even, `0 < S < P`), iid paired binary boards
(`n ≥ 1`; codes `0,1,2` = A-only, B-only, same), and the actual uniform
slot-tie law: the expected A survivor share exceeds `1/2` iff `b < a`.
Only the order of the two pooled scores enters the sort; boards on which both
are correct add the same amount to both and are absorbed in code `2`. -/
theorem balanced_iid_sign {G : Type*} {P S n : ℕ} (hP : Even P) (hS : 0 < S) (hSP : S < P)
    (roster : Fin P → G) (g : G) (hbal : blockSize roster g = P / 2)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (htotal : a + b + c = 1)
    (hn : 0 < n) :
    0 < ((PairedScores.sampleLaw a b c ha hb hc htotal n).bind fun z =>
        slotTieSelectionLaw hSP.le (pooledScore roster g
          (PairedScores.count z 0 : ℝ) (PairedScores.count z 1 : ℝ))).expect
        (fun A => (survivorCount roster A g : ℝ) / S) - 1/2 ↔ b < a := by
  set Lz := PairedScores.sampleLaw a b c ha hb hc htotal n
  have hP0 : 0 < P := lt_trans hS hSP
  rw [slot_master hSP.le hP0]
  have e1 : (fun z : Fin n → Fin 3 => (PairedScores.count z 1 : ℝ) < (PairedScores.count z 0 : ℝ)) =
      (fun z => PairedScores.count z 1 < PairedScores.count z 0) := by
    funext z; exact propext Nat.cast_lt
  have e2 : (fun z : Fin n → Fin 3 => (PairedScores.count z 0 : ℝ) < (PairedScores.count z 1 : ℝ)) =
      (fun z => PairedScores.count z 0 < PairedScores.count z 1) := by
    funext z; exact propext Nat.cast_lt
  have e3 : (fun z : Fin n → Fin 3 => (PairedScores.count z 0 : ℝ) = (PairedScores.count z 1 : ℝ)) =
      (fun z => PairedScores.count z 0 = PairedScores.count z 1) := by
    funext z; exact propext Nat.cast_inj
  rw [e1, e2, e3]
  set rp := Lz.prob (fun z => PairedScores.count z 1 < PairedScores.count z 0)
  set rm := Lz.prob (fun z => PairedScores.count z 0 < PairedScores.count z 1)
  set tau := Lz.prob (fun z => PairedScores.count z 0 = PairedScores.count z 1)
  have htot : rp + rm + tau = 1 := PairedScores.outcome_probability_total Lz
  have hx : (S : ℝ) * ((blockSize roster g : ℝ) / P) = (S : ℝ) / 2 := by
    rw [hbal]
    obtain ⟨k, hk⟩ := hP
    have hk2 : P / 2 = k := by omega
    rw [hk2]
    have hpk : (P : ℝ) = 2 * k := by rw [hk]; push_cast; ring
    have hk0 : (k : ℝ) ≠ 0 := by
      have : 0 < k := by omega
      exact_mod_cast Nat.ne_of_gt this
    rw [hpk]
    field_simp
  have hmin : ((min S (blockSize roster g) : ℕ) : ℝ) = (upperCount (P / 2) S : ℝ) := by
    rw [hbal]
    unfold upperCount
    rw [min_comm]
  have hlow : ((S - (P - blockSize roster g) : ℕ) : ℝ) = (lowerCount P (P / 2) S : ℝ) := by
    rw [hbal]
    rfl
  rw [hx, hmin, hlow]
  have hsign := balanced_sign hP hS hSP rp rm tau htot ((S : ℝ) / 2) rfl
  unfold blockFraction at hsign
  rw [hsign]
  have hw := (PairedScores.iid_win_sign ha hb hc htotal hn).1
  unfold PairedScores.winProbability at hw
  change 1/2 < rp + 1/2 * tau ↔ b < a at hw
  rw [← hw]
  constructor <;> intro h <;> linarith

/-- The referee's balanced witness on actual laws: one board, codes
`0,1,2` with masses `3/10, 1/5, 1/2`, `P = 12`, `S = 4`, `K = 6`. -/
noncomputable def refereeBoard : Law (Fin 3) :=
  PairedScores.pairedLaw (3/10) (1/5) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

noncomputable def codeScoreA (j : Fin 3) : ℝ := if j = 0 then 1 else 0
noncomputable def codeScoreB (j : Fin 3) : ℝ := if j = 1 then 1 else 0

/-- Six A copies (slots 0-5) and six B copies (slots 6-11). -/
def balancedRoster (i : Fin 12) : Bool := decide ((i : ℕ) < 6)

theorem balancedRoster_block : blockSize balancedRoster true = 6 := by
  have h : (Finset.univ.filter fun i : Fin 12 => balancedRoster i = true).card = 6 := by
    decide
  unfold blockSize
  convert h

theorem refereeBoard_probs :
    refereeBoard.prob (fun j => codeScoreB j < codeScoreA j) = 3/10 ∧
    refereeBoard.prob (fun j => codeScoreA j < codeScoreB j) = 1/5 ∧
    refereeBoard.prob (fun j => codeScoreA j = codeScoreB j) = 1/2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Law.prob, refereeBoard, PairedScores.pairedLaw, PairedScores.weight,
      Fin.sum_univ_three, codeScoreA, codeScoreB]

/-- **Referee gap 1 counterexample, realized**: with ties to the incumbent B
block the balanced A share falls to `1/2 - 1/5` although `Δ = +1/10`; uniform
slot ties and the fair genotype coin both give `1/2 + 1/20`. -/
theorem balanced_incumbent_witness (evaluations : Fin 12 → ℕ)
    (hinc : ∀ i j, balancedRoster i ≠ true → balancedRoster j = true →
      evaluations j < evaluations i) :
    (refereeBoard.bind fun j => incumbentSelectionLaw h412
        (pooledScore balancedRoster true (codeScoreA j) (codeScoreB j)) evaluations).expect
        (fun A => (survivorCount balancedRoster A true : ℝ) / 4) - 1/2 = -1/5 ∧
    (refereeBoard.bind fun j => slotTieSelectionLaw h412
        (pooledScore balancedRoster true (codeScoreA j) (codeScoreB j))).expect
        (fun A => (survivorCount balancedRoster A true : ℝ) / 4) - 1/2 = 1/20 ∧
    (refereeBoard.bind fun j => genotypeTieSelectionLaw h412
        (pooledScore balancedRoster true (codeScoreA j) (codeScoreB j)) balancedRoster).expect
        (fun A => (survivorCount balancedRoster A true : ℝ) / 4) - 1/2 = 1/20 := by
  obtain ⟨h1, h2, h3⟩ := refereeBoard_probs
  refine ⟨?_, ?_, ?_⟩
  · have h := incumbent_master_B h412 refereeBoard balancedRoster true codeScoreA codeScoreB
      evaluations hinc
    simp only [Nat.cast_ofNat] at h
    rw [h, h1, h2, h3, balancedRoster_block]
    norm_num
  · have h := slot_master h412 (by norm_num) refereeBoard balancedRoster true codeScoreA
      codeScoreB
    simp only [Nat.cast_ofNat] at h
    rw [h, h1, h2, h3, balancedRoster_block]
    norm_num
  · have h := genotype_master h412 refereeBoard balancedRoster true false (by decide)
      (fun i => Bool.eq_false_or_eq_true (balancedRoster i)) codeScoreA codeScoreB
    simp only [Nat.cast_ofNat] at h
    rw [h, h1, h2, h3, balancedRoster_block]
    norm_num

/-- Doc B B3.4 in share form on the actual laws (`genotype_coin_differs_from_slot_ties`
realized): identical scores, two board copies of twelve, `S = 4`: survivor
share `1/4` under the genotype coin, `1/6` under uniform slot ties. -/
theorem genotype_coin_share_witness (c : ℝ) :
    (genotypeTieSelectionLaw h412 (fun _ => c) twoBoardRoster).expect
        (fun A => (survivorCount twoBoardRoster A true : ℝ) / 4) = 1/4 ∧
    (slotTieSelectionLaw h412 (fun _ => c)).expect
        (fun A => (survivorCount twoBoardRoster A true : ℝ) / 4) = 1/6 := by
  obtain ⟨h1, h2⟩ := genotype_coin_breaks_baseline c
  simp only [div_eq_mul_inv]
  rw [Law.expect_mul_const, Law.expect_mul_const, h1, h2]
  norm_num

/-- Eleven A copies (slots 0-10), one B copy. -/
def elevenRoster (i : Fin 12) : Bool := decide ((i : ℕ) < 11)

theorem elevenRoster_block : blockSize elevenRoster true = 11 := by
  have h : (Finset.univ.filter fun i : Fin 12 => elevenRoster i = true).card = 11 := by
    decide
  unfold blockSize
  convert h

/-- **Doc A B2.3 "a worse type can increase", realized on the actual sort
(any key kernel; the one complementary board is tie-free).** A rare worse
type (`f_A = 9/20 < f_B = 11/20`, one copy) has expected survivor share
`9/80 > 1/12`; a common better type (`f_A = 11/20`, eleven copies) has
`71/80 < 11/12`. -/
theorem worse_type_can_increase {K : Type*} [Fintype K] (keys : K → Fin 12 → ℤ) (KL : Law K) :
    (MutationBaseline.bernoulli (9/20) (by norm_num) (by norm_num)).expect boardScoreA = 9/20 ∧
    (MutationBaseline.bernoulli (9/20) (by norm_num) (by norm_num)).expect boardScoreB = 11/20 ∧
    ((MutationBaseline.bernoulli (9/20) (by norm_num) (by norm_num)).bind fun b =>
        tieSelectionLaw h412 (pooledScore newcomerRoster true (boardScoreA b) (boardScoreB b))
          keys KL).expect (fun A => (survivorCount newcomerRoster A true : ℝ) / 4) = 9/80 ∧
    (1:ℝ)/12 < 9/80 ∧
    ((MutationBaseline.bernoulli (11/20) (by norm_num) (by norm_num)).bind fun b =>
        tieSelectionLaw h412 (pooledScore elevenRoster true (boardScoreA b) (boardScoreB b))
          keys KL).expect (fun A => (survivorCount elevenRoster A true : ℝ) / 4) = 71/80 ∧
    (71:ℝ)/80 < 11/12 := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := board_probs (9/20) (by norm_num) (by norm_num)
  obtain ⟨b1, b2, b3, -, -⟩ := board_probs (11/20) (by norm_num) (by norm_num)
  have hm1 := pooled_master h412 (MutationBaseline.bernoulli (9/20) (by norm_num) (by norm_num))
    newcomerRoster true boardScoreA boardScoreB keys KL
  have hm2 := pooled_master h412 (MutationBaseline.bernoulli (11/20) (by norm_num) (by norm_num))
    elevenRoster true boardScoreA boardScoreB keys KL
  simp only [Nat.cast_ofNat] at hm1 hm2
  rw [a1, a2, a3, newcomerRoster_block] at hm1
  rw [b1, b2, b3, elevenRoster_block] at hm2
  norm_num at hm1 hm2
  refine ⟨a4, by rw [a5]; norm_num, hm1, by norm_num, hm2, by norm_num⟩

/-! ### Twelve fair paired boards (`D = ±1`, `n = 12`) -/

/-- Twelve iid fair complementary boards: `true` = A correct and B wrong,
`false` = B correct and A wrong. -/
noncomputable def twelveLaw : Law (Fin 12 → Bool) := Law.pi (fun _ : Fin 12 => fairBoard)

/-- Number of boards won by A, and by B. -/
def winsA (z : Fin 12 → Bool) : ℕ := (Finset.univ.filter fun i => z i = true).card
def winsB (z : Fin 12 → Bool) : ℕ := (Finset.univ.filter fun i => z i = false).card

/-- Pooled accuracies of the two genotypes on the twelve boards. -/
noncomputable def twelveScoreA (z : Fin 12 → Bool) : ℝ := (winsA z : ℝ) / 12
noncomputable def twelveScoreB (z : Fin 12 → Bool) : ℝ := (winsB z : ℝ) / 12

theorem winsA_add_winsB (z : Fin 12 → Bool) : winsA z + winsB z = 12 := by
  unfold winsA winsB
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 12)))
    (fun i => z i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have he : (Finset.univ.filter fun i => z i = false) =
      Finset.univ.filter fun i => ¬ z i = true := by
    ext i
    simp
  rw [he]
  exact h

theorem twelve_prob (E : (Fin 12 → Bool) → Prop) [DecidablePred E] :
    twelveLaw.prob E = ((Finset.univ.filter E).card : ℝ) / 4096 := by
  have hb : ∀ b, fairBoard.mass b = 1/2 := by
    intro b
    cases b
    · simp [fairBoard, MutationBaseline.bernoulli]
      norm_num
    · simp [fairBoard, MutationBaseline.bernoulli]
  have hm : ∀ z, twelveLaw.mass z = 1/4096 := by
    intro z
    show ∏ i, fairBoard.mass (z i) = 1/4096
    simp only [hb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [← Law.expect_indicator twelveLaw E]
  unfold Law.expect Law1.mean
  simp_rw [hm]
  rw [← Finset.mul_sum, Finset.sum_boole]
  ring

theorem card_winsA_six :
    ((Finset.univ : Finset (Fin 12 → Bool)).filter (fun z => winsA z = 6)).card = 924 := by
  have h := Finset.card_powersetCard 6 (Finset.univ : Finset (Fin 12))
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [show Nat.choose 12 6 = 924 by rfl] at h
  rw [← h]
  apply Finset.card_nbij' (fun z => Finset.univ.filter fun i => z i = true)
    (fun s i => decide (i ∈ s))
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz
    simp [Finset.mem_powersetCard, winsA] at hz ⊢
    exact hz
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, winsA]
    simpa using hs.2
  · intro z _
    funext i
    simp
  · intro s _
    ext i
    simp

theorem card_winsA_hi_lo :
    ((Finset.univ : Finset (Fin 12 → Bool)).filter (fun z => 6 < winsA z)).card =
      ((Finset.univ : Finset (Fin 12 → Bool)).filter (fun z => winsA z < 6)).card := by
  have hflip : ∀ z : Fin 12 → Bool, winsA (fun i => !z i) = winsB z := by
    intro z
    unfold winsA winsB
    congr 1
    ext i
    simp
  apply Finset.card_nbij' (fun z i => !z i) (fun z i => !z i)
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
    have := winsA_add_winsB z
    rw [hflip]
    omega
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
    have := winsA_add_winsB z
    rw [hflip]
    omega
  · intro z _
    funext i
    simp
  · intro z _
    funext i
    simp

/-- Exact score-order probabilities on twelve fair boards:
`τ = C(12,6)/2^12 = 231/1024` and each strict order `793/2048`. -/
theorem twelve_order_probs :
    twelveLaw.prob (fun z => twelveScoreA z = twelveScoreB z) = 231/1024 ∧
    twelveLaw.prob (fun z => twelveScoreB z < twelveScoreA z) = 793/2048 ∧
    twelveLaw.prob (fun z => twelveScoreA z < twelveScoreB z) = 793/2048 := by
  have ev : ∀ z, (twelveScoreA z = twelveScoreB z ↔ winsA z = 6) ∧
      (twelveScoreB z < twelveScoreA z ↔ 6 < winsA z) ∧
      (twelveScoreA z < twelveScoreB z ↔ winsA z < 6) := by
    intro z
    have h := winsA_add_winsB z
    have hB : (winsB z : ℝ) = 12 - winsA z := by
      have : ((winsA z + winsB z : ℕ) : ℝ) = 12 := by exact_mod_cast h
      push_cast at this
      linarith
    unfold twelveScoreA twelveScoreB
    rw [hB]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro he
        have : (winsA z : ℝ) = 6 := by linarith
        exact_mod_cast this
      · intro he
        rw [he]
        norm_num
    · constructor
      · intro hl
        have : (6 : ℝ) < winsA z := by linarith
        exact_mod_cast this
      · intro hl
        have : (6 : ℝ) < winsA z := by exact_mod_cast hl
        linarith
    · constructor
      · intro hl
        have : (winsA z : ℝ) < 6 := by linarith
        exact_mod_cast this
      · intro hl
        have : (winsA z : ℝ) < 6 := by exact_mod_cast hl
        linarith
  have e1 : (fun z => twelveScoreA z = twelveScoreB z) = (fun z => winsA z = 6) :=
    funext (fun z => propext (ev z).1)
  have e2 : (fun z => twelveScoreB z < twelveScoreA z) = (fun z => 6 < winsA z) :=
    funext (fun z => propext (ev z).2.1)
  have e3 : (fun z => twelveScoreA z < twelveScoreB z) = (fun z => winsA z < 6) :=
    funext (fun z => propext (ev z).2.2)
  have htie : twelveLaw.prob (fun z => winsA z = 6) = 231/1024 := by
    rw [twelve_prob, card_winsA_six]
    norm_num
  have hsym : twelveLaw.prob (fun z => 6 < winsA z) = twelveLaw.prob (fun z => winsA z < 6) := by
    rw [twelve_prob, twelve_prob, card_winsA_hi_lo]
  have htot := order_probs_total twelveLaw twelveScoreA twelveScoreB
  rw [e1, e2, e3] at htot ⊢
  refine ⟨htie, ?_, ?_⟩ <;> linarith

/-- **Doc A B2.3, twelve paired boards, on the actual sort.** One neutral
newcomer, `P = 12`, `S = 4`: uniform slot ties give expected share
`(1-τ)/8 + τ/12 = 947/8192 > 1/12`; protected incumbents give
`(1-τ)/8 = 793/8192`, still above `1/12` because `τ < 1/3`. -/
theorem twelve_board_newcomer (evaluations : Fin 12 → ℕ)
    (hinc : ∀ i j, newcomerRoster i ≠ true → newcomerRoster j = true →
      evaluations j < evaluations i) :
    (twelveLaw.bind fun z => slotTieSelectionLaw h412
        (pooledScore newcomerRoster true (twelveScoreA z) (twelveScoreB z))).expect
        (fun A => (survivorCount newcomerRoster A true : ℝ) / 4) = 947/8192 ∧
    (1:ℝ)/12 < 947/8192 ∧
    (twelveLaw.bind fun z => incumbentSelectionLaw h412
        (pooledScore newcomerRoster true (twelveScoreA z) (twelveScoreB z)) evaluations).expect
        (fun A => (survivorCount newcomerRoster A true : ℝ) / 4) = 793/8192 ∧
    (1:ℝ)/12 < 793/8192 := by
  obtain ⟨h1, h2, h3⟩ := twelve_order_probs
  have hs := slot_master h412 (by norm_num) twelveLaw newcomerRoster true twelveScoreA twelveScoreB
  have hi := incumbent_master_B h412 twelveLaw newcomerRoster true twelveScoreA twelveScoreB
    evaluations hinc
  simp only [Nat.cast_ofNat] at hs hi
  rw [h1, h2, h3, newcomerRoster_block] at hs hi
  norm_num at hs hi
  exact ⟨hs, by norm_num, hi, by norm_num⟩

/-- **Referee value, realized.** Balanced counts (`K = 6`), `Δ = 0`, twelve
fair boards, ties to the incumbent B block: `E Y - 1/2 = -231/2048`. -/
theorem twelve_board_balanced_incumbent (evaluations : Fin 12 → ℕ)
    (hinc : ∀ i j, balancedRoster i ≠ true → balancedRoster j = true →
      evaluations j < evaluations i) :
    (twelveLaw.bind fun z => incumbentSelectionLaw h412
        (pooledScore balancedRoster true (twelveScoreA z) (twelveScoreB z)) evaluations).expect
        (fun A => (survivorCount balancedRoster A true : ℝ) / 4) - 1/2 = -231/2048 := by
  obtain ⟨h1, h2, h3⟩ := twelve_order_probs
  have hi := incumbent_master_B h412 twelveLaw balancedRoster true twelveScoreA twelveScoreB
    evaluations hinc
  simp only [Nat.cast_ofNat] at hi
  rw [h1, h2, h3, balancedRoster_block] at hi
  rw [hi]
  norm_num

/-- A concrete evaluation vector making the non-`true` block the protected
incumbents: the incumbent-priority hypotheses above are satisfiable. -/
def incumbentEvals (roster : Fin 12 → Bool) (i : Fin 12) : ℕ := if roster i then 0 else 1

theorem incumbentEvals_spec (roster : Fin 12 → Bool) :
    ∀ i j, roster i ≠ true → roster j = true → incumbentEvals roster j < incumbentEvals roster i := by
  intro i j hi hj
  simp [incumbentEvals, hj, hi]

end Balanced

end SEKernel.Closeout.Selection

#print axioms SEKernel.Closeout.Selection.lexSurvivors_cross
#print axioms SEKernel.Closeout.Selection.cross_set_unique
#print axioms SEKernel.Closeout.Selection.cross_target_count
#print axioms SEKernel.Closeout.Selection.rankRecord_lt_of_score
#print axioms SEKernel.Closeout.Selection.rankRecord_lt_of_key
#print axioms SEKernel.Closeout.Selection.rankRecord_const_lt_of_key
#print axioms SEKernel.Closeout.Selection.rankRecord_const_lt_iff
#print axioms SEKernel.Closeout.Selection.lexSurvivors_const
#print axioms SEKernel.Closeout.Selection.count_of_precedes
#print axioms SEKernel.Closeout.Selection.count_of_follows
#print axioms SEKernel.Closeout.Selection.pointLaw_expect
#print axioms SEKernel.Closeout.Selection.slotTieSelectionLaw_eq
#print axioms SEKernel.Closeout.Selection.incumbentSelectionLaw_eq
#print axioms SEKernel.Closeout.Selection.genotypeTieSelectionLaw_eq
#print axioms SEKernel.Closeout.Selection.slot_tied_survivors
#print axioms SEKernel.Closeout.Selection.listOrder_tied_survivors
#print axioms SEKernel.Closeout.Selection.listOrder_tied_count
#print axioms SEKernel.Closeout.Selection.uniform_perm_coord
#print axioms SEKernel.Closeout.Selection.slot_tied_count
#print axioms SEKernel.Closeout.Selection.incumbent_tied_count_A
#print axioms SEKernel.Closeout.Selection.incumbent_tied_count_B
#print axioms SEKernel.Closeout.Selection.genotype_tied_count
#print axioms SEKernel.Closeout.Selection.survivorCount_const
#print axioms SEKernel.Closeout.Selection.pooledScore_tie
#print axioms SEKernel.Closeout.Selection.pooled_count_ahead'
#print axioms SEKernel.Closeout.Selection.pooled_count_behind'
#print axioms SEKernel.Closeout.Selection.conditional_count
#print axioms SEKernel.Closeout.Selection.pooled_master
#print axioms SEKernel.Closeout.Selection.slot_master
#print axioms SEKernel.Closeout.Selection.incumbent_master_A
#print axioms SEKernel.Closeout.Selection.incumbent_master_B
#print axioms SEKernel.Closeout.Selection.genotype_master
#print axioms SEKernel.Closeout.Selection.prob_prod_fst'
#print axioms SEKernel.Closeout.Selection.implemented_order_tied_iff
#print axioms SEKernel.Closeout.Selection.tieCount_of_const
#print axioms SEKernel.Closeout.Selection.product_tieCount
#print axioms SEKernel.Closeout.Selection.slot_implemented_master
#print axioms SEKernel.Closeout.Selection.genotype_implemented_master
#print axioms SEKernel.Closeout.Selection.incumbent_implemented_master_A
#print axioms SEKernel.Closeout.Selection.incumbent_implemented_master_B
#print axioms SEKernel.Closeout.Selection.order_probs_total
#print axioms SEKernel.Closeout.Selection.pooled_master_count
#print axioms SEKernel.Closeout.Selection.board_probs
#print axioms SEKernel.Closeout.Selection.h412
#print axioms SEKernel.Closeout.Selection.neutral_newcomer_share
#print axioms SEKernel.Closeout.Selection.newcomerRoster_block
#print axioms SEKernel.Closeout.Selection.fairBoard_probs
#print axioms SEKernel.Closeout.Selection.neutral_newcomer_witness_slot
#print axioms SEKernel.Closeout.Selection.neutral_newcomer_witness_incumbent
#print axioms SEKernel.Closeout.Selection.majorityRoster_block
#print axioms SEKernel.Closeout.Selection.block_fitness_decline
#print axioms SEKernel.Closeout.Selection.block_fitness_decline_slot
#print axioms SEKernel.Closeout.Selection.majorityRoster_share
#print axioms SEKernel.Closeout.Selection.identical_outcomes_no_board
#print axioms SEKernel.Closeout.Selection.boardFraction_bounds
#print axioms SEKernel.Closeout.Selection.generation_expected_share
#print axioms SEKernel.Closeout.Selection.incumbent_mutation_floor
#print axioms SEKernel.Closeout.Selection.slot_ties_restore_baseline
#print axioms SEKernel.Closeout.Selection.twoBoardRoster_block
#print axioms SEKernel.Closeout.Selection.genotype_coin_breaks_baseline
#print axioms SEKernel.Closeout.Selection.floor_below_control
#print axioms SEKernel.Closeout.Selection.historical_sort_retains_iff
#print axioms SEKernel.Closeout.Selection.historical_actual_share
#print axioms SEKernel.Closeout.Selection.current_pool_newcomer_never_survives
#print axioms SEKernel.Closeout.Selection.historical_actual_instance
#print axioms SEKernel.Closeout.Selection.total_variance
#print axioms SEKernel.Closeout.Selection.task_heterogeneity_variance
#print axioms SEKernel.Closeout.Selection.blockSize_sum
#print axioms SEKernel.Closeout.Selection.rosterFreq_sum
#print axioms SEKernel.Closeout.Selection.freq_mul_survivalWeight
#print axioms SEKernel.Closeout.Selection.survivor_covariance_identity
#print axioms SEKernel.Closeout.Selection.affine_survival_variance
#print axioms SEKernel.Closeout.Selection.nextRoster_sum
#print axioms SEKernel.Closeout.Selection.blockSize_true_sum
#print axioms SEKernel.Closeout.Selection.blockSize_false_sum
#print axioms SEKernel.Closeout.Selection.survivorCount_true_sum
#print axioms SEKernel.Closeout.Selection.survivorCount_false_sum
#print axioms SEKernel.Closeout.Selection.boardShare_nextRoster
#print axioms SEKernel.Closeout.Selection.interfaceOff_mean
#print axioms SEKernel.Closeout.Selection.mutateProb_bounds
#print axioms SEKernel.Closeout.Selection.survivors_nonempty
#print axioms SEKernel.Closeout.Selection.crossoverOff_mean
#print axioms SEKernel.Closeout.Selection.genKernel_share
#print axioms SEKernel.Closeout.Selection.expect_congr_support
#print axioms SEKernel.Closeout.Selection.bind_support
#print axioms SEKernel.Closeout.Selection.map_support
#print axioms SEKernel.Closeout.Selection.floor_kernel_support
#print axioms SEKernel.Closeout.Selection.floor_chain_support
#print axioms SEKernel.Closeout.Selection.floor_chain_share
#print axioms SEKernel.Closeout.Selection.control_chain_share
#print axioms SEKernel.Closeout.Selection.allVoters_block
#print axioms SEKernel.Closeout.Selection.floor_vs_control_instance
#print axioms SEKernel.Closeout.Selection.voterFirst_prio
#print axioms SEKernel.Closeout.Selection.floor_vs_control_voterFirst
#print axioms SEKernel.Closeout.Selection.floorSel_incumbent
#print axioms SEKernel.Closeout.Selection.incumbent_prio
#print axioms SEKernel.Closeout.Selection.selection_control_contrast
#print axioms SEKernel.Closeout.Selection.slot_minus_incumbent_actual
#print axioms SEKernel.Closeout.Selection.tie_penalty_pos
#print axioms SEKernel.Closeout.Selection.balanced_iid_sign
#print axioms SEKernel.Closeout.Selection.balancedRoster_block
#print axioms SEKernel.Closeout.Selection.refereeBoard_probs
#print axioms SEKernel.Closeout.Selection.balanced_incumbent_witness
#print axioms SEKernel.Closeout.Selection.genotype_coin_share_witness
#print axioms SEKernel.Closeout.Selection.elevenRoster_block
#print axioms SEKernel.Closeout.Selection.worse_type_can_increase
#print axioms SEKernel.Closeout.Selection.winsA_add_winsB
#print axioms SEKernel.Closeout.Selection.twelve_prob
#print axioms SEKernel.Closeout.Selection.card_winsA_six
#print axioms SEKernel.Closeout.Selection.card_winsA_hi_lo
#print axioms SEKernel.Closeout.Selection.twelve_order_probs
#print axioms SEKernel.Closeout.Selection.twelve_board_newcomer
#print axioms SEKernel.Closeout.Selection.twelve_board_balanced_incumbent
#print axioms SEKernel.Closeout.Selection.incumbentEvals_spec
