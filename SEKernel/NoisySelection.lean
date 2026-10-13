/-
Finite noisy selection for the Chile extension (Doc A/B, Part B).
The state retains ordered slots, bounded evaluation counters, and histories.
Selection accounting uses expected genotype survivor counts, including zero
counts.  It never identifies truncation with proportional selection.
-/
import SEKernel.FiniteProbability
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

namespace SEKernel.NoisySelection

open Finset FiniteProbability
open scoped Classical

/-- A finite-horizon state: histories and list order remain available to ties.
The bounds are an interface choice, not an assertion that counts are Markov. -/
structure EvolutionState (G H : Type*) (P horizon : ℕ) where
  roster : Fin P → G
  evaluations : Fin P → Fin (horizon + 1)
  history : Fin P → Fin horizon → Option H
  generation : Fin (horizon + 1)
  deriving Fintype

/-- Composing the specified finite mechanisms preserves every row's
normalization on the full state, including the history fields. -/
theorem full_state_transition_normalized {G H : Type*} [Fintype G] [Fintype H]
    {P horizon : ℕ} (K J : Kernel (EvolutionState G H P horizon)
      (EvolutionState G H P horizon)) (z : EvolutionState G H P horizon) :
    (∀ z', 0≤(Kernel.comp K J z).mass z') ∧
      (∑ z', (Kernel.comp K J z).mass z')=1 :=
  ⟨(Kernel.comp K J z).nonneg,(Kernel.comp K J z).total⟩

/-- Exactly S distinct current slots survive. -/
abbrev Survivors (P S : ℕ) := {A : Finset (Fin P) // A.card = S}

noncomputable def pointLaw {Ω : Type*} [Fintype Ω] (ω : Ω) : Law Ω where
  mass η := if η = ω then 1 else 0
  nonneg η := by split_ifs <;> norm_num
  total := by simp

/-- A proved uniform finite law; it will randomize slots or genotypes. -/
noncomputable def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Law Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (by positivity)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- Ascending lexicographic records give descending scores, ascending tie
keys, and finally the original slot index. -/
def rankRecord {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ) (i : Fin P) :
    ℝ ×ₗ (ℤ ×ₗ Fin P) := toLex (-score i, toLex (key i, i))

theorem rankRecord_injective {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ) :
    Function.Injective (rankRecord score key) := by
  intro i j h
  exact congrArg (fun r : ℝ ×ₗ (ℤ ×ₗ Fin P) => (ofLex (ofLex r).2).2) h

noncomputable def rankingList {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ) :
    List (Fin P) := by
  let r := fun i j => rankRecord score key i ≤ rankRecord score key j
  letI : IsTrans (Fin P) r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Antisymm r := ⟨fun _ _ hij hji => rankRecord_injective score key (le_antisymm hij hji)⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  exact Finset.univ.sort r

theorem rankingList_nodup {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ) :
    (rankingList score key).Nodup := by
  let r := fun i j => rankRecord score key i ≤ rankRecord score key j
  letI : IsTrans (Fin P) r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Antisymm r := ⟨fun _ _ hij hji => rankRecord_injective score key (le_antisymm hij hji)⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  exact Finset.sort_nodup (Finset.univ : Finset (Fin P)) r

theorem rankingList_length {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ) :
    (rankingList score key).length = P := by
  unfold rankingList
  simp only [Finset.length_sort, Finset.card_univ, Fintype.card_fin]

theorem rankingList_lexicographic {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ) :
    (rankingList score key).Pairwise
      (fun i j => rankRecord score key i ≤ rankRecord score key j) := by
  let r := fun i j => rankRecord score key i ≤ rankRecord score key j
  letI : IsTrans (Fin P) r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Antisymm r := ⟨fun _ _ hij hji => rankRecord_injective score key (le_antisymm hij hji)⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  exact Finset.pairwise_sort (Finset.univ : Finset (Fin P)) r

/-- The actual deterministic top-S algorithm, not a supplied survivor set. -/
noncomputable def lexSurvivors {P S : ℕ} (hSP : S ≤ P)
    (score : Fin P → ℝ) (key : Fin P → ℤ) : Survivors P S :=
  ⟨((rankingList score key).take S).toFinset, by
    rw [List.toFinset_card_of_nodup ((rankingList_nodup score key).take),
      List.length_take, rankingList_length, Nat.min_eq_left hSP]⟩

/-- The finite key law is explicit; its pushforward through lexicographic
sorting is the survivor law. -/
noncomputable def tieSelectionLaw {P S : ℕ} {K : Type*} [Fintype K]
    (hSP : S ≤ P) (score : Fin P → ℝ) (keys : K → Fin P → ℤ) (L : Law K) :
    Law (Survivors P S) := L.map (fun k => lexSurvivors hSP score (keys k))

/-- More evaluations wins a score tie; equal counts retain list order. -/
noncomputable def incumbentSelectionLaw {P S : ℕ} (hSP : S ≤ P)
    (score : Fin P → ℝ) (evaluations : Fin P → ℕ) : Law (Survivors P S) :=
  tieSelectionLaw hSP score (fun _ : Unit => fun i => -(evaluations i : ℤ))
    (pointLaw ())

noncomputable def slotTieSelectionLaw {P S : ℕ} (hSP : S ≤ P)
    (score : Fin P → ℝ) : Law (Survivors P S) :=
  tieSelectionLaw hSP score (fun π : Equiv.Perm (Fin P) => fun i => (π i : ℕ))
    (uniformLaw (Equiv.Perm (Fin P)))

/-- Genotype permutation is a different law from slot permutation. -/
noncomputable def genotypeTieSelectionLaw {P S : ℕ} {G : Type*} [Fintype G]
    (hSP : S ≤ P) (score : Fin P → ℝ) (roster : Fin P → G) :
    Law (Survivors P S) :=
  tieSelectionLaw hSP score
    (fun π : Equiv.Perm (Fin (Fintype.card G)) => fun i =>
      (π (Fintype.equivFin G (roster i)) : ℕ))
    (uniformLaw (Equiv.Perm (Fin (Fintype.card G))))

section Counts
variable {P S : ℕ} {G : Type*} [Fintype G]

noncomputable def survivorCount (roster : Fin P → G) (A : Survivors P S) (g : G) : ℕ :=
  (A.val.filter fun i => roster i = g).card

theorem survivorCount_sum (roster : Fin P → G) (A : Survivors P S) :
    ∑ g, survivorCount roster A g = S := by
  classical
  simp only [survivorCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simpa using A.property

noncomputable def expectedSurvivorCount (L : Law (Survivors P S))
    (roster : Fin P → G) (g : G) : ℝ :=
  L.expect (fun A => (survivorCount roster A g : ℝ))

theorem expectedSurvivorCount_nonneg (L : Law (Survivors P S))
    (roster : Fin P → G) (g : G) : 0 ≤ expectedSurvivorCount L roster g :=
  L.expect_nonneg (fun _ => by positivity)

theorem expectedSurvivorCount_sum (L : Law (Survivors P S)) (roster : Fin P → G) :
    ∑ g, expectedSurvivorCount L roster g = S := by
  unfold expectedSurvivorCount
  rw [← L.expect_sum]
  have hp (A : Survivors P S) : (∑ g, (survivorCount roster A g : ℝ)) = S := by
    exact_mod_cast survivorCount_sum roster A
  simp_rw [hp]
  exact L.expect_const _

theorem expectedSurvivorCount_absent (L : Law (Survivors P S))
    (roster : Fin P → G) (g : G) (habsent : ∀ i, roster i≠g) :
    expectedSurvivorCount L roster g=0 := by
  unfold expectedSurvivorCount survivorCount
  have hempty (A : Survivors P S) : (A.val.filter fun i => roster i=g)=∅ := by
    ext i; simp [habsent i]
  simp only [hempty,Finset.card_empty,Nat.cast_zero,L.expect_const]

noncomputable def survivorMean (roster : Fin P → G) (f : G → ℝ)
    (A : Survivors P S) : ℝ := (∑ g, (survivorCount roster A g : ℝ) * f g) / S

/-- Referee count-form Price identity.  Zero expected survivor counts are
allowed, and no proportional-selection theorem is invoked. -/
theorem price_count_identity (hS : 0 < S) (L : Law (Survivors P S))
    (roster : Fin P → G) (x f : G → ℝ) :
    (S : ℝ) * (L.expect (survivorMean roster f) - ∑ g, x g * f g) =
      ∑ g, (expectedSurvivorCount L roster g - S*x g) * f g := by
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  unfold survivorMean expectedSurvivorCount
  simp only [div_eq_mul_inv, L.expect_mul_const, L.expect_sum]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  field_simp

end Counts

inductive BlockOrder where
  | ahead | behind | tied
  deriving DecidableEq, Fintype

noncomputable def upperCount (copies survivors : ℕ) : ℕ := min copies survivors
noncomputable def lowerCount (population copies survivors : ℕ) : ℕ :=
  survivors - (population - copies)

section Block
variable {Ω : Type*} [Fintype Ω]

/-- A pooled score experiment carries its realized retained A-count.  The
strict-order count facts are pointwise top-S hypotheses; the tied count is
left to the stated finite key kernel. -/
structure PooledExperiment (Ω : Type*) [Fintype Ω] where
  law : Law Ω
  order : Ω → BlockOrder
  retainedA : Ω → ℝ

noncomputable def PooledExperiment.tieCount (E : PooledExperiment Ω) : ℝ :=
  E.law.conditionalMean E.retainedA (fun ω => E.order ω = .tied)

/-- The master formula keeps all three outcome probabilities and the tied
conditional expected COUNT as inputs.  The pairwise fair coin is separate. -/
theorem topS_master (E : PooledExperiment Ω) (S : ℕ) (hS : 0 < S)
    (H L rplus rminus tau T_A : ℝ)
    (hahead : ∀ ω, E.order ω = .ahead → E.retainedA ω = H)
    (hbehind : ∀ ω, E.order ω = .behind → E.retainedA ω = L)
    (hrplus : E.law.prob (fun ω => E.order ω = .ahead) = rplus)
    (hrminus : E.law.prob (fun ω => E.order ω = .behind) = rminus)
    (htau : E.law.prob (fun ω => E.order ω = .tied) = tau)
    (hTA : E.tieCount = T_A) :
    E.law.expect (fun ω => E.retainedA ω / S) =
      (rplus*H+rminus*L+tau*T_A)/S := by
  have hc (b : BlockOrder) (v : ℝ) (hv : ∀ ω, E.order ω = b → E.retainedA ω = v) :
      E.law.cellExpect E.retainedA (fun ω => E.order ω = b) =
        E.law.prob (fun ω => E.order ω = b) * v := by
    classical
    unfold Law.cellExpect Law.prob Law.expect Law1.mean
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hb : E.order ω = b
    · simp [hb, hv ω hb]
    · simp [hb]
  have ht := E.law.total_expectation E.retainedA E.order
  have hsum (f : BlockOrder → ℝ) : ∑ b, f b = f .ahead + f .behind + f .tied := by
    have hu : (Finset.univ : Finset BlockOrder) = {.ahead, .behind, .tied} := by
      ext b; cases b <;> simp
    rw [hu]; simp [add_assoc]
  rw [hsum] at ht
  rw [E.law.prob_mul_conditionalMean, E.law.prob_mul_conditionalMean,
    hc .ahead H hahead, hc .behind L hbehind, hrplus, hrminus] at ht
  change E.law.expect E.retainedA = rplus*H+rminus*L+
    E.law.prob (fun ω => E.order ω = .tied)*E.tieCount at ht
  rw [htau, hTA] at ht
  simpa only [div_eq_mul_inv, E.law.expect_mul_const] using
    congrArg (fun v : ℝ => v/(S:ℝ)) ht

end Block

/-- The normalized master expression, useful for exact algebraic instances. -/
noncomputable def blockFraction (S H L rplus rminus tau T_A : ℝ) : ℝ :=
  (rplus*H+rminus*L+tau*T_A)/S

theorem slot_tie_decomposition {S H L rplus rminus tau x : ℝ}
    (hS : S ≠ 0) (htotal : rplus+rminus+tau = 1) :
    blockFraction S H L rplus rminus tau (S*x) - x =
      (1-tau)/2*((H+L)/S-2*x) +
      (H-L)/S*(rplus+tau/2-1/2) := by
  have hr : rminus = 1-rplus-tau := by linarith
  rw [hr]
  unfold blockFraction
  field_simp
  ring

theorem incumbent_tie_penalty {S H L rplus rminus tau x : ℝ} (hS : S ≠ 0) :
    blockFraction S H L rplus rminus tau (S*x) -
      blockFraction S H L rplus rminus tau L = tau*(x-L/S) := by
  unfold blockFraction
  field_simp
  ring

theorem pairwise_incumbent_penalty (rplus tau : ℝ) :
    rplus = (rplus+tau/2)-tau/2 := by ring

/-- Balanced counts plus a fair tied COUNT S/2.  This hypothesis covers
uniform slot ties or a fair genotype coin, and excludes incumbent ties. -/
theorem balanced_fair_formula {S H L rplus rminus tau : ℝ}
    (hS : S ≠ 0) (hHL : H+L=S) (htotal : rplus+rminus+tau=1) :
    blockFraction S H L rplus rminus tau (S/2)-1/2 =
      (rplus-rminus)*(H-L)/(2*S) := by
  have hr : rminus = 1-rplus-tau := by linarith
  have hH : H = S-L := by linarith
  rw [hr, hH]
  unfold blockFraction
  field_simp
  ring

/-- The referee correction for protected incumbents at balanced abundance. -/
theorem balanced_incumbent_formula {S H L rplus rminus tau : ℝ}
    (hS : S ≠ 0) (hHL : H+L=S) (htotal : rplus+rminus+tau=1) :
    blockFraction S H L rplus rminus tau L-1/2 =
      (rplus-rminus)*(H-L)/(2*S)-tau*(1/2-L/S) := by
  have hf := balanced_fair_formula hS hHL htotal
  have hp := incumbent_tie_penalty (H:=H) (L:=L) (rplus:=rplus) (rminus:=rminus)
    (tau:=tau) (x:=(1/2:ℝ)) hS
  norm_num only [mul_one_div] at hp
  linarith

theorem balanced_count_geometry {P S : ℕ} (hP : Even P) (hS : 0 < S) (hSP : S < P) :
    upperCount (P/2) S + lowerCount P (P/2) S = S ∧
      lowerCount P (P/2) S < upperCount (P/2) S := by
  obtain ⟨k, hk⟩ := hP
  subst P
  unfold upperCount lowerCount
  omega

/-- The finite balanced sign consumer records even population, proper
positive survivor size, and fair ties as explicit hypotheses. -/
theorem balanced_sign {P S : ℕ} (hP : Even P) (hS : 0 < S) (hSP : S < P)
    (rplus rminus tau : ℝ) (htotal : rplus+rminus+tau=1)
    (T_A : ℝ) (hfair : T_A = (S:ℝ)/2) :
    (0 < blockFraction S (upperCount (P/2) S) (lowerCount P (P/2) S)
      rplus rminus tau T_A-1/2 ↔ rminus < rplus) := by
  obtain ⟨hHL,hlt⟩ := balanced_count_geometry hP hS hSP
  have hsr : (S:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  rw [hfair, balanced_fair_formula hsr (by exact_mod_cast hHL) htotal]
  have hdiff : 0 < (upperCount (P/2) S : ℝ)-(lowerCount P (P/2) S : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hlt)
  have hden : 0 < 2*(S:ℝ) := by positivity
  rw [div_pos_iff_of_pos_right hden, mul_pos_iff_of_pos_right hdiff, sub_pos]

/-- A finite exact master-formula counterexample, before any transmission. -/
theorem neutral_rare_block : blockFraction 4 1 0 (1/2) (1/2) 0 (1/3) = 1/8 ∧
    (1/12 : ℝ) < blockFraction 4 1 0 (1/2) (1/2) 0 (1/3) := by
  norm_num [blockFraction]

theorem genotype_coin_differs_from_slot_ties :
    blockFraction 4 2 0 0 0 1 1 = 1/4 ∧
    blockFraction 4 2 0 0 0 1 (2/3) = 1/6 := by
  norm_num [blockFraction]

theorem unbiased_block_fitness_decline :
    blockFraction 4 4 2 (51/100) (49/100) 0 0 = 151/200 ∧
    ((51/100:ℝ)-(49/100)) *
      (blockFraction 4 4 2 (51/100) (49/100) 0 0-5/6) = -47/30000 := by
  norm_num [blockFraction]

theorem balanced_incumbent_sign_counterexample :
    blockFraction 4 4 0 (3/10) (1/5) (1/2) 0-1/2 = -1/5 ∧
    blockFraction 4 4 0 (3/10) (1/5) (1/2) 2-1/2 = 1/20 := by
  norm_num [blockFraction]

section Decomposition
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

def mean (x f : G → ℝ) : ℝ := ∑ g, x g*f g

/-- Frozen fitness, transmission, and changing environment are three
different finite terms.  No sign is assigned to the latter two. -/
theorem selection_transmission_environment (L : Law Ω) (x f : G → ℝ)
    (Y Xnext fnext : Ω → G → ℝ) :
    L.expect (fun ω => mean (Xnext ω) (fnext ω))-mean x f =
      (L.expect (fun ω => mean (Y ω) f)-mean x f) +
      L.expect (fun ω => ∑ g, (Xnext ω g-Y ω g)*f g) +
      L.expect (fun ω => ∑ g, Xnext ω g*(fnext ω g-f g)) := by
  have hid (ω : Ω) : mean (Xnext ω) (fnext ω) = mean (Y ω) f +
      (∑ g, (Xnext ω g-Y ω g)*f g) +
      ∑ g, Xnext ω g*(fnext ω g-f g) := by
    unfold mean
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    ring
  simp_rw [hid, L.expect_add]
  ring

theorem arbitrary_update_environment (L : Law Ω) (x f : G → ℝ)
    (Xnext fnext : Ω → G → ℝ) :
    L.expect (fun ω => mean (Xnext ω) (fnext ω))-mean x f =
      (∑ g, (L.expect (fun ω => Xnext ω g)-x g)*f g) +
      L.expect (fun ω => ∑ g, Xnext ω g*(fnext ω g-f g)) := by
  have h := selection_transmission_environment L x f Xnext Xnext fnext
  simp only [sub_self, zero_mul, Finset.sum_const_zero, L.expect_const, add_zero] at h
  rw [h]
  unfold mean
  rw [L.expect_sum]
  simp_rw [L.expect_mul_const]
  simp [sub_mul, Finset.sum_sub_distrib]

theorem controlled_remainder_bound {selection transmission environment gamma : ℝ}
    (hgain : 0 ≤ selection)
    (hbound : |transmission+environment| ≤ gamma*selection) :
    (1-gamma)*selection ≤ selection+transmission+environment := by
  have h := (neg_le_abs (transmission+environment)).trans hbound
  nlinarith

theorem affine_control_contrast (alpha beta selected current : ℝ) :
    (alpha+beta*selected)-(alpha+beta*current) = beta*(selected-current) := by ring

end Decomposition

section Truncation
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The pointwise certificate defining a true top set, with arbitrary ties. -/
def IsTopSet (f : ι → ℝ) (A : Finset ι) : Prop :=
  ∀ i ∈ A, ∀ j ∉ A, f j ≤ f i

theorem rankingList_mem {P : ℕ} (score : Fin P → ℝ) (key : Fin P → ℤ) (i : Fin P) :
    i ∈ rankingList score key := by
  let r := fun i j => rankRecord score key i ≤ rankRecord score key j
  letI : IsTrans (Fin P) r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Antisymm r := ⟨fun _ _ hij hji => rankRecord_injective score key (le_antisymm hij hji)⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  exact (Finset.mem_sort r).2 (Finset.mem_univ i)

/-- The implemented lexicographic selection really is a top set of scores;
the tie key changes only choices within equal-score classes. -/
theorem lexSurvivors_topSet {P S : ℕ} (hSP : S ≤ P)
    (score : Fin P → ℝ) (key : Fin P → ℤ) :
    IsTopSet score (lexSurvivors hSP score key).val := by
  intro i hi j hj
  have hi' : i ∈ (rankingList score key).take S := by simpa [lexSurvivors] using hi
  have hj' : j ∉ (rankingList score key).take S := by simpa [lexSurvivors] using hj
  have hjdrop : j ∈ (rankingList score key).drop S := by
    have hall := rankingList_mem score key j
    rw [← List.take_append_drop S (rankingList score key), List.mem_append] at hall
    exact hall.resolve_left hj'
  have hpair := rankingList_lexicographic score key
  rw [← List.take_append_drop S (rankingList score key), List.pairwise_append] at hpair
  have hrel := hpair.2.2 i hi' j hjdrop
  simp only [rankRecord, Prod.Lex.toLex_le_toLex] at hrel
  rcases hrel with hlt | ⟨heq,_⟩ <;> linarith

omit [Fintype ι] [Nonempty ι] in
/-- When every target slot strictly outranks every other slot, top-S keeps
exactly the minimum of target occupancy and capacity. -/
theorem higher_target_count (score : ι → ℝ) (target B : Finset ι)
    (htop : IsTopSet score B)
    (hstrict : ∀ i ∈ target, ∀ j ∉ target, score j<score i) :
    (B ∩ target).card=min B.card target.card := by
  classical
  have hle : (B ∩ target).card ≤ min B.card target.card :=
    le_min (Finset.card_le_card Finset.inter_subset_left)
      (Finset.card_le_card Finset.inter_subset_right)
  apply le_antisymm hle
  by_contra hn
  have hlt : (B ∩ target).card < min B.card target.card := lt_of_not_ge hn
  have hmiss : ∃ i ∈ target, i ∉ B := by
    by_contra hno
    have hsub : target ⊆ B := by simpa [Finset.subset_iff] using hno
    rw [Finset.inter_eq_right.mpr hsub] at hlt
    omega
  have hout : ∃ j ∈ B, j ∉ target := by
    by_contra hno
    have hsub : B ⊆ target := by simpa [Finset.subset_iff] using hno
    rw [Finset.inter_eq_left.mpr hsub] at hlt
    omega
  obtain ⟨i,hi,hiB⟩ := hmiss
  obtain ⟨j,hj,hjtarget⟩ := hout
  exact (not_le_of_gt (hstrict i hi j hjtarget)) (htop j hj i hiB)

/-- The strict pooled-genotype count used by the master formula is proved
for the actual implemented lexicographic selection, with any tie key. -/
theorem pooled_count_ahead {P S : ℕ} {G : Type*} [Fintype G]
    (hSP : S≤P) (roster : Fin P → G) (g : G) (high low : ℝ) (hgap : low<high)
    (key : Fin P → ℤ) :
    survivorCount roster
      (lexSurvivors hSP (fun i => if roster i=g then high else low) key) g =
      min S ((Finset.univ.filter fun i => roster i=g).card) := by
  classical
  let target := Finset.univ.filter (fun i => roster i=g)
  have h := higher_target_count (fun i => if roster i=g then high else low)
    target (lexSurvivors hSP (fun i => if roster i=g then high else low) key).val
    (lexSurvivors_topSet hSP _ key) (by
      intro i hi j hj
      have hi' : roster i=g := by simpa [target] using hi
      have hj' : roster j≠g := by simpa [target] using hj
      simpa only [hi',hj',↓reduceIte] using hgap)
  rw [(lexSurvivors hSP _ key).property] at h
  simpa only [survivorCount,target,Finset.inter_filter,Finset.inter_univ] using h

theorem pooled_count_behind {P S : ℕ} {G : Type*} [Fintype G]
    (hSP : S≤P) (roster : Fin P → G) (g : G) (low high : ℝ) (hgap : low<high)
    (key : Fin P → ℤ) :
    survivorCount roster
      (lexSurvivors hSP (fun i => if roster i=g then low else high) key) g =
      S-(P-(Finset.univ.filter fun i => roster i=g).card) := by
  classical
  let B := (lexSurvivors hSP (fun i => if roster i=g then low else high) key).val
  let target := Finset.univ.filter (fun i => roster i≠g)
  have h := higher_target_count (fun i => if roster i=g then low else high) target B
    (lexSurvivors_topSet hSP _ key) (by
      intro i hi j hj
      have hi' : roster i≠g := by simpa [target] using hi
      have hj' : roster j=g := by simpa [target] using hj
      simpa only [hi',hj',↓reduceIte] using hgap)
  have hB : B.card=S := (lexSurvivors hSP _ key).property
  have hboth := Finset.card_filter_add_card_filter_not (s:=B) (fun i => roster i=g)
  have hpop := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i : Fin P => roster i=g)
  have h' : (B.filter (fun i => roster i≠g)).card = min S target.card := by
    simpa only [target,Finset.inter_filter,Finset.inter_univ,hB] using h
  simp only [Finset.card_univ,Fintype.card_fin] at hpop
  change (B.filter (fun i => roster i=g)).card = _
  dsimp only [target] at h'
  simp only [ne_eq] at h' hboth hpop
  omega

noncomputable def implementedPooledExperiment {Ω G : Type*} [Fintype Ω] [Fintype G]
    {P S : ℕ} (hSP : S≤P) (L : Law Ω) (roster : Fin P → G) (g : G)
    (scoreA scoreB : Ω → ℝ) (keys : Ω → Fin P → ℤ) : PooledExperiment Ω where
  law := L
  order ω := if scoreB ω<scoreA ω then .ahead else if scoreA ω<scoreB ω then .behind else .tied
  retainedA ω := survivorCount roster
    (lexSurvivors hSP (fun i => if roster i=g then scoreA ω else scoreB ω) (keys ω)) g

/-- The master formula specialized to the actual ordered-roster sorting
implementation.  The tied conditional expected count remains an explicit
input from the chosen key kernel; it is never replaced by a pairwise coin. -/
theorem implemented_topS_master {Ω G : Type*} [Fintype Ω] [Fintype G]
    {P S : ℕ} (hSP : S≤P) (hS : 0<S) (L : Law Ω) (roster : Fin P → G) (g : G)
    (scoreA scoreB : Ω → ℝ) (keys : Ω → Fin P → ℤ) (rplus rminus tau T_A : ℝ)
    (hrplus : L.prob (fun ω => scoreB ω<scoreA ω)=rplus)
    (hrminus : L.prob (fun ω => scoreA ω<scoreB ω)=rminus)
    (htau : L.prob (fun ω => scoreA ω=scoreB ω)=tau)
    (hT : (implementedPooledExperiment hSP L roster g scoreA scoreB keys).tieCount=T_A) :
    L.expect (fun ω => (survivorCount roster
      (lexSurvivors hSP (fun i => if roster i=g then scoreA ω else scoreB ω) (keys ω)) g : ℝ)/S)=
      (rplus*((min S ((Finset.univ.filter fun i => roster i=g).card) : ℕ) : ℝ)+
        rminus*((S-(P-(Finset.univ.filter fun i => roster i=g).card) : ℕ) : ℝ)+tau*T_A)/S := by
  classical
  let E := implementedPooledExperiment hSP L roster g scoreA scoreB keys
  have hahead (ω : Ω) (h : E.order ω= .ahead) : E.retainedA ω=
      ((min S ((Finset.univ.filter fun i => roster i=g).card) : ℕ) : ℝ) := by
    have hgap : scoreB ω<scoreA ω := by
      dsimp [E,implementedPooledExperiment] at h
      split_ifs at h <;> simp_all
    change (survivorCount roster (lexSurvivors hSP (fun i => if roster i=g then scoreA ω else scoreB ω) (keys ω)) g : ℝ)=_
    exact congrArg (fun n : ℕ => (n : ℝ)) (pooled_count_ahead hSP roster g (scoreA ω) (scoreB ω) hgap (keys ω))
  have hbehind (ω : Ω) (h : E.order ω= .behind) : E.retainedA ω=
      (S-(P-(Finset.univ.filter fun i => roster i=g).card) : ℕ) := by
    have hgap : scoreA ω<scoreB ω := by
      dsimp [E,implementedPooledExperiment] at h
      split_ifs at h <;> simp_all
    change (survivorCount roster (lexSurvivors hSP (fun i => if roster i=g then scoreA ω else scoreB ω) (keys ω)) g : ℝ)=_
    exact congrArg (fun n : ℕ => (n : ℝ)) (pooled_count_behind hSP roster g (scoreA ω) (scoreB ω) hgap (keys ω))
  have hp : E.law.prob (fun ω => E.order ω= .ahead)=rplus := by
    convert hrplus using 1
    apply congrArg L.prob
    funext ω; apply propext
    dsimp [E,implementedPooledExperiment]
    split_ifs <;> simp_all
  have hm : E.law.prob (fun ω => E.order ω= .behind)=rminus := by
    convert hrminus using 1
    apply congrArg L.prob
    funext ω; apply propext
    dsimp [E,implementedPooledExperiment]
    split_ifs <;> simp_all <;> linarith
  have ht : E.law.prob (fun ω => E.order ω= .tied)=tau := by
    convert htau using 1
    apply congrArg L.prob
    funext ω; apply propext
    dsimp [E,implementedPooledExperiment]
    split_ifs <;> simp_all <;> linarith
  exact topS_master E S hS _ _ rplus rminus tau T_A hahead hbehind hp hm ht hT

theorem topSet_threshold (f : ι → ℝ) (A : Finset ι) (hA : A.Nonempty)
    (htop : IsTopSet f A) : ∃ t : ℝ,
      (∀ i ∈ A, t ≤ f i) ∧ (∀ i ∉ A, f i ≤ t) := by
  classical
  let B := A.image f
  have hB : B.Nonempty := hA.image f
  refine ⟨B.min' hB, ?_, ?_⟩
  · intro i hi
    exact Finset.min'_le B (f i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  · intro i hi
    obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp (Finset.min'_mem B hB)
    rw [← heq]
    exact htop j hj i hi

/-- A true top set dominates every feasible fractional inclusion vector.
The proof retains the actual selected and unselected slots. -/
theorem topSet_dominates_fractional (f : ι → ℝ) (A : Finset ι)
    (hA : A.Nonempty) (htop : IsTopSet f A) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hsum : ∑ i, w i = A.card) :
    (∑ i, w i*f i) ≤ ∑ i ∈ A, f i := by
  classical
  obtain ⟨t,hsel,hunsel⟩ := topSet_threshold f A hA htop
  let I : ι → ℝ := fun i => if i ∈ A then 1 else 0
  have hI : (∑ i, I i) = A.card := by simp [I]
  have hIf : (∑ i, I i*f i) = ∑ i ∈ A, f i := by
    simp [I, Finset.sum_filter]
  have hz : (∑ i, (I i-w i)) = 0 := by rw [Finset.sum_sub_distrib, hI, hsum]; ring
  have hnon : 0 ≤ ∑ i, (I i-w i)*(f i-t) := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i ∈ A
    · exact mul_nonneg (by simpa [I,hi] using sub_nonneg.mpr (hw i).2)
        (sub_nonneg.mpr (hsel i hi))
    · exact mul_nonneg_of_nonpos_of_nonpos
        (by simpa [I,hi] using neg_nonpos.mpr (hw i).1)
        (sub_nonpos.mpr (hunsel i hi))
  have hid : (∑ i, (I i-w i)*(f i-t)) =
      (∑ i ∈ A, f i) - (∑ i, w i*f i) := by
    simp_rw [sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hIf, hI, hsum]
    ring
  linarith

theorem uniform_expect (f : ι → ℝ) :
    (uniformLaw ι).expect f = (∑ i, f i)/(Fintype.card ι : ℝ) := by
  unfold uniformLaw Law.expect Law1.mean
  rw [← Finset.mul_sum]
  ring

/-- Doc A B5.3a: the actual true top-S mean dominates the uniform mean by
min(1,(P-S)/S) times uniform variance. -/
theorem true_top_variance_bound (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (A : Finset ι) (hA : A.Nonempty) (htop : IsTopSet f A)
    (hproper : A.card < Fintype.card ι) :
    min (1:ℝ) (((Fintype.card ι : ℝ)-A.card)/A.card) *
      (uniformLaw ι).variance f ≤
      (∑ i ∈ A, f i)/(A.card:ℝ)-(uniformLaw ι).expect f := by
  classical
  let q : ℝ := Fintype.card ι
  let s : ℝ := A.card
  let μ := (uniformLaw ι).expect f
  let r := s/q
  let c := min r (1-r)
  let w : ι → ℝ := fun i => r+c*(f i-μ)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos
  have hs : 0 < s := by dsimp [s]; exact_mod_cast A.card_pos.mpr hA
  have hsq : s < q := by dsimp [s,q]; exact_mod_cast hproper
  have hr : 0 < r := div_pos hs hq
  have hr' : r ≤ 1 := by dsimp [r]; exact (div_le_one hq).2 hsq.le
  have hc : 0 ≤ c := le_min hr.le (sub_nonneg.mpr hr')
  have hcr : c ≤ r := min_le_left _ _
  have hcr' : c ≤ 1-r := min_le_right _ _
  have hμ : 0 ≤ μ ∧ μ ≤ 1 := by
    constructor
    · exact (uniformLaw ι).expect_nonneg (fun i => (hf i).1)
    · simpa using (uniformLaw ι).expect_mono (fun i => (hf i).2)
  have hsumf : (∑ i, f i) = q*μ := by
    dsimp [μ,q]
    rw [uniform_expect]
    field_simp
  have hsumcenter : (∑ i, (f i-μ)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ i, f i)-q*μ=0
    rw [hsumf]; ring
  have hwsum : (∑ i, w i) = A.card := by
    simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum, hsumcenter,
      mul_zero, add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change q*(s/q)=s
    field_simp
  have hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1 := by
    intro i
    dsimp only [w]
    have hfi := hf i
    constructor
    · nlinarith
    · nlinarith
  have hexchange := topSet_dominates_fractional f A hA htop w hw hwsum
  have hv : (∑ i, (f i-μ)*f i) = q*(uniformLaw ι).variance f := by
    rw [(uniformLaw ι).variance_eq, uniform_expect]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumf]
    change (∑ i, f i*f i)-μ*(q*μ) = q*((∑ i, f i^2)/q-μ^2)
    simp_rw [← pow_two]
    field_simp
  have hwf : (∑ i, w i*f i) = s*μ+c*q*(uniformLaw ι).variance f := by
    simp only [w, add_mul, Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsumf, hv]
    dsimp [r]
    field_simp
  rw [hwf] at hexchange
  have hcoef : c/r = min (1:ℝ) ((q-s)/s) := by
    rw [← min_div_div_right hr.le r (1-r), div_self hr.ne']
    congr 1
    dsimp [r]
    field_simp
  change min (1:ℝ) ((q-s)/s) * (uniformLaw ι).variance f ≤ _/s-μ
  rw [← hcoef]
  have halg : c/r*(uniformLaw ι).variance f =
      (c*q*(uniformLaw ι).variance f)/s := by
    dsimp [r]
    field_simp
  rw [halg]
  apply (le_sub_iff_add_le).2
  have hid : c*q*(uniformLaw ι).variance f/s+μ =
      (s*μ+c*q*(uniformLaw ι).variance f)/s := by field_simp <;> ring
  rw [hid]
  exact (div_le_div_iff_of_pos_right hs).2 hexchange

/-- Oracle regret under a uniform error bound.  The estimated top-set
property is structural; no assumption about the desired true sum is made. -/
theorem topSet_regret (f estimate : ι → ℝ) (A B : Finset ι)
    (hA : A.card=B.card) (hB : B.Nonempty) (htop : IsTopSet estimate B)
    (ε : ℝ) (hε : 0 ≤ ε) (herr : ∀ i, |estimate i-f i| ≤ ε) :
    (∑ i ∈ A, f i)/(A.card:ℝ)-2*ε ≤ (∑ i ∈ B, f i)/(B.card:ℝ) := by
  classical
  let w : ι → ℝ := fun i => if i ∈ A then 1 else 0
  have hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1 := by intro i; dsimp [w]; split_ifs <;> norm_num
  have hsum : (∑ i, w i) = B.card := by simp [w,hA]
  have hexchange := topSet_dominates_fractional estimate B hB htop w hw hsum
  have hx : (∑ i ∈ A, estimate i) ≤ ∑ i ∈ B, estimate i := by
    simpa [w,Finset.sum_filter] using hexchange
  have hlow : (∑ i ∈ A, f i)-A.card*ε ≤ ∑ i ∈ A, estimate i := by
    have h := Finset.sum_le_sum (s:=A) (fun i _ => (abs_le.mp (herr i)).1)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
    linarith
  have hhigh : (∑ i ∈ B, estimate i) ≤ (∑ i ∈ B, f i)+B.card*ε := by
    have h := Finset.sum_le_sum (s:=B) (fun i _ => (abs_le.mp (herr i)).2)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
    linarith
  have hs : (0:ℝ)<B.card := by exact_mod_cast B.card_pos.mpr hB
  rw [hA]
  rw [hA] at hlow
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ hs).2
  have hid : ((∑ i ∈ B, f i)/(B.card:ℝ)+2*ε)*(B.card:ℝ) =
      (∑ i ∈ B, f i)+2*ε*(B.card:ℝ) := by field_simp <;> ring
  rw [hid]
  nlinarith

noncomputable def setMean (f : ι → ℝ) (A : Finset ι) : ℝ :=
  (∑ i ∈ A, f i)/(A.card:ℝ)

theorem setMean_bounds (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (A : Finset ι) (hA : A.Nonempty) : 0 ≤ setMean f A ∧ setMean f A ≤ 1 := by
  have hs : (0:ℝ)<A.card := by exact_mod_cast A.card_pos.mpr hA
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => (hf i).1)) hs.le
  · apply (div_le_one hs).2
    simpa using Finset.sum_le_sum (s:=A) (fun i _ => (hf i).2)

/-- Finite noisy oracle regret.  Its advertised Bernoulli/Hoeffding
specializations, and the resulting variance guarantee, are vacuous at
n ≤ 36 boards in the experiment; this theorem supplies no scale prediction. -/
theorem noisy_topSet_regret {Ω : Type*} [Fintype Ω] (L : Law Ω)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (A : Finset ι)
    (hA : A.Nonempty) (B : Ω → Finset ι) (estimate : Ω → ι → ℝ)
    (hcard : ∀ ω, A.card=(B ω).card) (htop : ∀ ω, IsTopSet (estimate ω) (B ω))
    (ε : ℝ) (hε : 0 ≤ ε) :
    setMean f A-2*ε-L.prob (fun ω => ∃ i, ε < |estimate ω i-f i|) ≤
      L.expect (fun ω => setMean f (B ω)) := by
  classical
  let bad : Ω → Prop := fun ω => ∃ i, ε < |estimate ω i-f i|
  have hB (ω : Ω) : (B ω).Nonempty := by
    apply Finset.card_pos.mp
    rw [← hcard ω]
    exact A.card_pos.mpr hA
  have hp (ω : Ω) : setMean f A-2*ε-(if bad ω then 1 else 0) ≤ setMean f (B ω) := by
    by_cases hb : bad ω
    · simp only [hb, ↓reduceIte]
      have ha := setMean_bounds f hf A hA
      have hbb := setMean_bounds f hf (B ω) (hB ω)
      linarith
    · simp only [hb, ↓reduceIte, sub_zero]
      exact topSet_regret f (estimate ω) A (B ω) (hcard ω) (hB ω) (htop ω)
        ε hε (fun i => le_of_not_gt (fun hi => hb ⟨i,hi⟩))
  have h := L.expect_mono hp
  simpa only [L.expect_sub, L.expect_const, L.expect_indicator, bad] using h

/-- Actual estimator variances give a union bound with no cross-group
independence assumption. -/
theorem bad_score_probability {Ω : Type*} [Fintype Ω] (L : Law Ω)
    (f : ι → ℝ) (estimate : Ω → ι → ℝ)
    (hunbiased : ∀ i, L.expect (fun ω => estimate ω i) = f i)
    (ε : ℝ) (hε : 0 < ε) :
    L.prob (fun ω => ∃ i, ε < |estimate ω i-f i|) ≤
      min 1 ((∑ i, L.variance (fun ω => estimate ω i))/ε^2) := by
  apply le_min (L.prob_le_one _)
  calc
    _ ≤ ∑ i, L.prob (fun ω => ε < |estimate ω i-f i|) := L.prob_exists_le _
    _ ≤ ∑ i, L.variance (fun ω => estimate ω i)/ε^2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ L.prob (fun ω => ε ≤ |estimate ω i-L.expect (fun ω => estimate ω i)|) :=
          L.prob_mono (fun ω hω => by simpa [hunbiased i] using hω.le)
        _ ≤ _ := L.chebyshev _ hε
    _ = _ := by rw [Finset.sum_div]

/-- Doc A B5.3b, with the finite variance error allowance.  For the
experiment's stated parameters, its n ≤ 36 boards specialization is vacuous,
as the referee found. -/
theorem noisy_top_variance_bound {Ω : Type*} [Fintype Ω] (L : Law Ω)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (A : Finset ι)
    (hA : A.Nonempty) (htrue : IsTopSet f A) (hproper : A.card < Fintype.card ι)
    (B : Ω → Finset ι) (estimate : Ω → ι → ℝ)
    (hcard : ∀ ω, A.card=(B ω).card) (htop : ∀ ω, IsTopSet (estimate ω) (B ω))
    (hunbiased : ∀ i, L.expect (fun ω => estimate ω i) = f i)
    (ε : ℝ) (hε : 0 < ε) :
    min (1:ℝ) (((Fintype.card ι : ℝ)-A.card)/A.card)*(uniformLaw ι).variance f -
      2*ε-min 1 ((∑ i, L.variance (fun ω => estimate ω i))/ε^2) ≤
      L.expect (fun ω => setMean f (B ω))-(uniformLaw ι).expect f := by
  have ht := true_top_variance_bound f hf A hA htrue hproper
  have hn := noisy_topSet_regret L f hf A hA B estimate hcard htop ε hε.le
  have hp := bad_score_probability L f estimate hunbiased ε hε
  change _ ≤ setMean f A-(uniformLaw ι).expect f at ht
  linarith

theorem topSet_eq_of_strict_cross (estimate : ι → ℝ) (A B : Finset ι)
    (hcard : A.card=B.card) (htop : IsTopSet estimate B)
    (hcross : ∀ i ∈ A, ∀ j ∉ A, estimate j < estimate i) : B=A := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    by_contra hjA
    have hex : ∃ i ∈ A, i ∉ B := by
      by_contra hn
      have hAB : A ⊆ B := by simpa [Finset.subset_iff] using hn
      have heq := Finset.eq_of_subset_of_card_le hAB (by omega)
      exact hjA (heq ▸ hj)
    obtain ⟨i,hiA,hiB⟩ := hex
    exact (not_le_of_gt (hcross i hiA j hjA)) (htop j hj i hiB)
  · omega

/-- Doc B B5.5's finite alternative: sum the actual finite cross-pair
misranking bounds.  It does not require independence between different pairs.
For the experiment's stated parameters, the exponential n ≤ 36 specialization is vacuous. -/
theorem topSet_recovery_probability {Ω : Type*} [Fintype Ω] (L : Law Ω)
    (A : Finset ι) (B : Ω → Finset ι) (estimate : Ω → ι → ℝ)
    (hcard : ∀ ω, A.card=(B ω).card) (htop : ∀ ω, IsTopSet (estimate ω) (B ω))
    (error : {i : ι // i ∈ A} → {j : ι // j ∉ A} → ℝ)
    (herr : ∀ (i : {i : ι // i ∈ A}) (j : {j : ι // j ∉ A}),
      L.prob (fun ω => estimate ω i ≤ estimate ω j) ≤ error i j) :
    L.prob (fun ω => B ω ≠ A) ≤ min 1
      (∑ i : {i : ι // i ∈ A}, ∑ j : {j : ι // j ∉ A}, error i j) := by
  classical
  apply le_min (L.prob_le_one _)
  calc
    _ ≤ L.prob (fun ω => ∃ i : {i : ι // i ∈ A}, ∃ j : {j : ι // j ∉ A},
        estimate ω i ≤ estimate ω j) := by
      apply L.prob_mono
      intro ω hω
      by_contra hn
      apply hω
      apply topSet_eq_of_strict_cross (estimate ω) A (B ω) (hcard ω) (htop ω)
      intro i hi j hj
      exact lt_of_not_ge (fun h => hn ⟨⟨i,hi⟩,⟨j,hj⟩,h⟩)
    _ ≤ ∑ i : {i : ι // i ∈ A},
        L.prob (fun ω => ∃ j : {j : ι // j ∉ A}, estimate ω i ≤ estimate ω j) :=
      L.prob_exists_le _
    _ ≤ ∑ i : {i : ι // i ∈ A}, ∑ j : {j : ι // j ∉ A},
        L.prob (fun ω => estimate ω i ≤ estimate ω j) := by
      apply Finset.sum_le_sum
      intro i _
      exact L.prob_exists_le _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => herr i j))

theorem recovered_topSet_mean {Ω : Type*} [Fintype Ω] (L : Law Ω)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (A : Finset ι) (hA : A.Nonempty)
    (B : Ω → Finset ι) (hcard : ∀ ω, A.card=(B ω).card) :
    setMean f A-L.prob (fun ω => B ω ≠ A) ≤ L.expect (fun ω => setMean f (B ω)) := by
  classical
  have hp (ω : Ω) : setMean f A-(if B ω≠A then 1 else 0) ≤ setMean f (B ω) := by
    by_cases he : B ω=A
    · simp [he]
    · rw [if_pos he]
      have hB : (B ω).Nonempty := by
        apply Finset.card_pos.mp
        rw [← hcard ω]
        exact A.card_pos.mpr hA
      have ha := setMean_bounds f hf A hA
      have hb := setMean_bounds f hf (B ω) hB
      linarith
  have h := L.expect_mono hp
  simpa only [L.expect_sub, L.expect_const, L.expect_indicator] using h

end Truncation

section ScoreReliability
variable {Ω : Type*} [Fintype Ω]

noncomputable def fairWinWeight (z : ℝ) : ℝ := if 0<z then 1 else if z=0 then 1/2 else 0
noncomputable def fairWin (L : Law Ω) (Z : Ω → ℝ) : ℝ := L.expect (fun ω => fairWinWeight (Z ω))

theorem fairWinWeight_monotone : Monotone fairWinWeight := by
  intro x y hxy
  by_cases hx : 0<x
  · have hy : 0<y := lt_of_lt_of_le hx hxy
    simp [fairWinWeight,hx,hy]
  · by_cases hx0 : x=0
    · subst x
      by_cases hy : 0<y
      · norm_num [fairWinWeight,hy]
      · have hy0 : y=0 := le_antisymm (le_of_not_gt hy) hxy
        simp [hy0]
    · have hnon : 0≤fairWinWeight y := by unfold fairWinWeight; split_ifs <;> norm_num
      simpa [fairWinWeight,hx,hx0] using hnon

theorem fairWinWeight_reflect (z : ℝ) : fairWinWeight z+fairWinWeight (-z)=1 := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · simp [fairWinWeight, hz, not_lt_of_ge hz.le, ne_of_lt hz, ne_of_gt (neg_pos.mpr hz)]
  · subst z; norm_num [fairWinWeight]
  · simp [fairWinWeight, hz, not_lt_of_ge (neg_nonpos.mpr hz.le), ne_of_lt (neg_neg_of_pos hz)]

theorem fairWin_error_le_nonpositive (L : Law Ω) (Z : Ω → ℝ) :
    1-fairWin L Z ≤ L.prob (fun ω => Z ω≤0) := by
  classical
  have hp (ω : Ω) : 1-fairWinWeight (Z ω) ≤ if Z ω≤0 then 1 else 0 := by
    unfold fairWinWeight
    split_ifs <;> norm_num at * <;> linarith
  have h := L.expect_mono hp
  simpa only [L.expect_sub, L.expect_const, L.expect_indicator, fairWin] using h

/-- The lower-tail Cantelli theorem uses the actual variance, so dependent
estimates and covariance terms are covered. -/
theorem score_error_cantelli (L : Law Ω) (Z : Ω → ℝ) (hmean : 0 < L.expect Z) :
    L.prob (fun ω => Z ω≤0) ≤ L.variance Z/(L.variance Z+(L.expect Z)^2) := by
  have he : L.expect (fun ω => (-1)*Z ω) = -L.expect Z := by
    rw [L.expect_const_mul]; ring
  have hv : L.variance (fun ω => (-1)*Z ω) = L.variance Z := by
    rw [L.variance_const_mul]; norm_num
  have h := L.cantelli (fun ω => (-1)*Z ω) hmean
  rw [he,hv] at h
  have hp : (fun ω => -L.expect Z+L.expect Z≤(-1)*Z ω) = (fun ω => Z ω≤0) := by
    funext ω; apply propext; constructor <;> intro hh <;> linarith
  rwa [hp] at h

theorem fairWin_variance_guarantee (L : Law Ω) (Z : Ω → ℝ) (hmean : 0 < L.expect Z) :
    (L.expect Z)^2/(L.variance Z+(L.expect Z)^2) ≤ fairWin L Z := by
  have he := (fairWin_error_le_nonpositive L Z).trans (score_error_cantelli L Z hmean)
  have hd : 0 < L.variance Z+(L.expect Z)^2 :=
    add_pos_of_nonneg_of_pos (L.variance_nonneg Z) (sq_pos_of_pos hmean)
  have hid : 1-L.variance Z/(L.variance Z+(L.expect Z)^2) =
      (L.expect Z)^2/(L.variance Z+(L.expect Z)^2) := by field_simp; ring
  rw [← hid]
  linarith

theorem expect_equiv (L : Law Ω) (e : Ω ≃ Ω) (hmass : ∀ ω, L.mass (e ω)=L.mass ω)
    (f : Ω → ℝ) : L.expect (fun ω => f (e ω))=L.expect f := by
  unfold Law.expect Law1.mean
  calc
    (∑ ω, L.mass ω*f (e ω)) = ∑ ω, L.mass (e ω)*f (e ω) := by simp_rw [hmass]
    _ = _ := e.sum_comp (fun ω => L.mass ω*f ω)

/-- Fixed location noise is a real additional hypothesis: its reflected
finite states retain equal mass. -/
theorem symmetric_fairWin_zero (L : Law Ω) (Z : Ω → ℝ) (e : Ω ≃ Ω)
    (hmass : ∀ ω, L.mass (e ω)=L.mass ω) (hneg : ∀ ω, Z (e ω)=-Z ω) :
    fairWin L Z=1/2 := by
  have hsym := expect_equiv L e hmass (fun ω => fairWinWeight (Z ω))
  simp only [hneg] at hsym
  have hpoint : (fun ω => fairWinWeight (Z ω)+fairWinWeight (-Z ω))=(fun _ => (1:ℝ)) := by
    funext ω; exact fairWinWeight_reflect _
  have h := congrArg L.expect hpoint
  rw [L.expect_add,L.expect_const,hsym] at h
  unfold fairWin
  linarith

/-- A fixed finite location-noise family is monotone in its shift. -/
theorem location_fairWin_monotone (L : Law Ω) (Z : Ω → ℝ) {a b : ℝ} (hab : a≤b) :
    fairWin L (fun ω => a+Z ω) ≤ fairWin L (fun ω => b+Z ω) :=
  L.expect_mono (fun ω => fairWinWeight_monotone (by dsimp only; linarith))

theorem shifted_fairWin_reflect {a : ℝ} (ha : 0<a) (z : ℝ) :
    fairWinWeight (a+z)+fairWinWeight (a-z)-1 =
      (if |z|<a then 1 else 0)+(1/2)*(if |z|=a then 1 else 0) := by
  by_cases hlo : z< -a
  · have hl : ¬0<a+z := by linarith
    have hl0 : a+z≠0 := by linarith
    have hr : 0<a-z := by linarith
    have habs : a < |z| := by rw [abs_of_neg (by linarith : z<0)]; linarith
    simp [fairWinWeight,hl,hl0,hr,not_lt_of_ge habs.le,ne_of_gt habs]
  · by_cases helo : z= -a
    · subst z
      have hr : 0<a- -a := by linarith
      norm_num [fairWinWeight,ha,abs_of_nonpos (neg_nonpos.mpr ha.le)]
    · have hlow : -a<z := by
        rcases lt_or_eq_of_le (le_of_not_gt hlo) with h | h
        · exact h
        · exact False.elim (helo h.symm)
      by_cases hhi : a<z
      · have hl : 0<a+z := by linarith
        have hr : ¬0<a-z := by linarith
        have hr0 : a-z≠0 := by linarith
        have habs : a < |z| := by rw [abs_of_pos (by linarith : 0<z)]; exact hhi
        simp [fairWinWeight,hl,hr,hr0,not_lt_of_ge habs.le,ne_of_gt habs]
      · by_cases hehi : z=a
        · subst z
          have hl : 0<a+a := by linarith
          norm_num [fairWinWeight,hl,abs_of_pos ha]
        · have hupp : z<a := by
            rcases lt_or_eq_of_le (le_of_not_gt hhi) with h | h
            · exact h
            · exact False.elim (hehi h)
          have hl : 0<a+z := by linarith
          have hr : 0<a-z := by linarith
          have habs : |z|<a := abs_lt.mpr ⟨hlow,hupp⟩
          simp [fairWinWeight,hl,hr,habs,ne_of_lt habs]

/-- Doc A B6.1's exact signal-to-noise identity, including boundary atoms.
The shift is a=Δ/σ; a fixed symmetric law is an explicit structural input. -/
theorem signal_to_noise_identity (L : Law Ω) (Z : Ω → ℝ) (e : Ω ≃ Ω)
    (hmass : ∀ ω, L.mass (e ω)=L.mass ω) (hneg : ∀ ω, Z (e ω)=-Z ω)
    {a : ℝ} (ha : 0<a) :
    fairWin L (fun ω => a+Z ω)-1/2 =
      (1/2)*L.prob (fun ω => |Z ω|<a)+(1/4)*L.prob (fun ω => |Z ω|=a) := by
  classical
  have hsym := expect_equiv L e hmass (fun ω => fairWinWeight (a+Z ω))
  simp only [hneg] at hsym
  change (L.expect fun ω => fairWinWeight (a-Z ω))=
    L.expect (fun ω => fairWinWeight (a+Z ω)) at hsym
  have hp : (fun ω => fairWinWeight (a+Z ω)+fairWinWeight (a-Z ω)-1) =
      (fun ω => (if |Z ω|<a then 1 else 0)+(1/2)*(if |Z ω|=a then 1 else 0)) := by
    funext ω; exact shifted_fairWin_reflect ha _
  have h := congrArg L.expect hp
  rw [L.expect_sub,L.expect_add,L.expect_const,L.expect_add,
    L.expect_const_mul,L.expect_indicator,L.expect_indicator,hsym] at h
  unfold fairWin
  linarith

noncomputable def varianceCounterexampleLaw : Law Bool where
  mass b := if b then 4/5 else 1/5
  nonneg b := by cases b <;> norm_num
  total := by norm_num [Fintype.sum_bool]

noncomputable def varianceCounterexampleFairLaw : Law Bool where
  mass _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_bool]

noncomputable def varianceCounterexampleU (b : Bool) : ℝ := if b then 1/5 else -3/10
noncomputable def varianceCounterexampleV (b : Bool) : ℝ := if b then 8/25 else -2/25

/-- Doc B B6.2 on two actual finite laws, with exact means, variances,
and positive-event probabilities. -/
theorem same_variance_larger_mean_fewer_wins :
    varianceCounterexampleLaw.expect varianceCounterexampleU=1/10 ∧
    varianceCounterexampleFairLaw.expect varianceCounterexampleV=3/25 ∧
    varianceCounterexampleLaw.variance varianceCounterexampleU=1/25 ∧
    varianceCounterexampleFairLaw.variance varianceCounterexampleV=1/25 ∧
    varianceCounterexampleLaw.prob (fun b => 0<varianceCounterexampleU b)=4/5 ∧
    varianceCounterexampleFairLaw.prob (fun b => 0<varianceCounterexampleV b)=1/2 := by
  norm_num [Law.expect,Law.variance,Law1.mean,Law1.variance,Law.prob,
    varianceCounterexampleLaw,varianceCounterexampleFairLaw,
    varianceCounterexampleU,varianceCounterexampleV,Fintype.sum_bool]

end ScoreReliability

end SEKernel.NoisySelection
