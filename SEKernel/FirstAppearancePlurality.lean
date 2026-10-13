/-
Finite ordered first-appearance plurality for the Chile epistemic extension.
The index convention includes N = 0 and an empty posted prefix.  None is
abstention; it is never a readable candidate.  No answer-label order is used.
-/
import SEKernel.FiniteProbability

namespace SEKernel.Epistemic

open Finset
open SEKernel.FiniteProbability

abbrev OrderedWord (N : ℕ) (A : Type*) := Fin N → Option A

/-- The number of positions occupied by one label, including abstention. -/
noncomputable def labelCount {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : Option A) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => z i = a).card

theorem labelCount_eq_sum {N : ℕ} {A : Type*} [DecidableEq A]
    (z : OrderedWord N A) (a : Option A) :
    labelCount z a = ∑ i, if z i = a then 1 else 0 := by
  classical
  unfold labelCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z i = a <;> simp [hi]

theorem labelCount_pos_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : Option A) :
    0 < labelCount z a ↔ ∃ i, z i = a := by
  classical
  rw [labelCount, Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

/-- Readable candidates whose counts dominate every readable occurrence. -/
noncomputable def candidatePositions {N : ℕ} {A : Type*}
    (z : OrderedWord N A) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun i => z i ≠ none ∧
    ∀ j, z j ≠ none → labelCount z (z j) ≤ labelCount z (z i)

/-- Total plurality: the label of the least maximal-count readable position. -/
noncomputable def plurality {N : ℕ} {A : Type*}
    (z : OrderedWord N A) : Option A := by
  classical
  exact if h : (candidatePositions z).Nonempty then
    z ((candidatePositions z).min' h) else none

theorem labelCount_relabel {N : ℕ} {A B : Type*}
    (z : OrderedWord N A) (σ : Option A ≃ Option B) (a : Option A) :
    labelCount (fun i => σ (z i)) (σ a) = labelCount z a := by
  classical
  simp only [labelCount, σ.injective.eq_iff]

theorem candidatePositions_relabel {N : ℕ} {A B : Type*}
    (z : OrderedWord N A) (σ : Option A ≃ Option B) (hσ : σ none = none) :
    candidatePositions (fun i => σ (z i)) = candidatePositions z := by
  classical
  have hn (a : Option A) : σ a ≠ none ↔ a ≠ none := by
    rw [← hσ]
    exact σ.injective.ne_iff
  ext i
  simp only [candidatePositions, Finset.mem_filter, Finset.mem_univ, true_and,
    hn, labelCount_relabel]

/-- Relabelling preserves the ordered tie rule, including the empty word. -/
theorem plurality_relabel {N : ℕ} {A B : Type*}
    (z : OrderedWord N A) (σ : Option A ≃ Option B) (hσ : σ none = none) :
    plurality (fun i => σ (z i)) = σ (plurality z) := by
  classical
  have hs := candidatePositions_relabel z σ hσ
  unfold plurality
  simp only [hs]
  split_ifs
  · rfl
  · exact hσ.symm

theorem candidatePositions_nonempty_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) :
    (candidatePositions z).Nonempty ↔ ∃ i, z i ≠ none := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2.1⟩
  · rintro ⟨i, hi⟩
    let s := Finset.univ.filter fun j => z j ≠ none
    have hs : s.Nonempty := ⟨i, by simp [s, hi]⟩
    obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun j => labelCount z (z j)) hs
    refine ⟨j, ?_⟩
    simp only [candidatePositions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(Finset.mem_filter.mp hj).2,
      fun k hk => hmax k (by simp [s, hk])⟩

theorem plurality_eq_none_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) : plurality z = none ↔ ∀ i, z i = none := by
  classical
  unfold plurality
  split_ifs with h
  · have hm := (Finset.mem_filter.mp ((candidatePositions z).min'_mem h)).2.1
    constructor
    · intro he
      exact (hm he).elim
    · intro he
      exact (hm (he _)).elim
  · rw [candidatePositions_nonempty_iff] at h
    simp only [not_exists, not_not] at h
    exact ⟨fun _ => h, fun _ => rfl⟩

theorem plurality_empty {A : Type*} (z : OrderedWord 0 A) :
    plurality z = none := by
  apply (plurality_eq_none_iff z).2
  intro i
  exact Fin.elim0 i

theorem plurality_mem_word {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : A) (h : plurality z = some a) :
    ∃ i, z i = some a := by
  classical
  unfold plurality at h
  split_ifs at h with hc
  · exact ⟨_, h⟩

theorem plurality_maximal_count {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : A) (h : plurality z = some a)
    (j : Fin N) (hj : z j ≠ none) :
    labelCount z (z j) ≤ labelCount z (some a) := by
  classical
  unfold plurality at h
  split_ifs at h with hc
  · have hm := (Finset.mem_filter.mp ((candidatePositions z).min'_mem hc)).2.2 j hj
    simpa only [h] using hm

theorem plurality_dominates_readable {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : A) (h : plurality z = some a) (b : A) :
    labelCount z (some b) ≤ labelCount z (some a) := by
  by_cases hb : 0 < labelCount z (some b)
  · obtain ⟨j, hj⟩ := (labelCount_pos_iff z (some b)).1 hb
    simpa [hj] using plurality_maximal_count z a h j (by simp [hj])
  · omega

/-- The retained winner is the first position among all maximal readable positions. -/
theorem plurality_first_maximal {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : A) (h : plurality z = some a) :
    ∃ i, z i = some a ∧ i ∈ candidatePositions z ∧
      ∀ j ∈ candidatePositions z, i ≤ j := by
  classical
  unfold plurality at h
  split_ifs at h with hc
  refine ⟨_, h, (candidatePositions z).min'_mem hc, ?_⟩
  intro j hj
  exact (candidatePositions z).min'_le j hj

theorem plurality_unique_readable {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : A) (hex : ∃ i, z i = some a)
    (hlabels : ∀ i, z i = none ∨ z i = some a) : plurality z = some a := by
  classical
  have hc : (candidatePositions z).Nonempty := by
    apply (candidatePositions_nonempty_iff z).2
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [hi]⟩
  unfold plurality
  rw [dif_pos hc]
  have hm := (Finset.mem_filter.mp ((candidatePositions z).min'_mem hc)).2.1
  exact (hlabels _).resolve_left hm

/-- Prefix reach, with zero allowed and with k ≤ N kept at interfaces. -/
def reaches {N : ℕ} {A : Type*} (z : OrderedWord N A) (k : ℕ) (a : A) : Prop :=
  ∃ i : Fin N, i.val < k ∧ z i = some a

/-- The actual ordered posted prefix, retaining its k positions. -/
def postedWord {N : ℕ} {A : Type*} (z : OrderedWord N A) (k : ℕ) (hk : k ≤ N) :
    OrderedWord k A := fun i => z ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

theorem postedWord_reaches_full {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (hk : k ≤ N) (a : A) :
    reaches (postedWord z k hk) k a ↔ reaches z k a := by
  constructor
  · rintro ⟨i, hi, hz⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, hi, hz⟩
  · rintro ⟨i, hi, hz⟩
    exact ⟨⟨i.val, hi⟩, hi, hz⟩

theorem postedWord_labelCount {N : ℕ} {A : Type*} [DecidableEq A]
    (z : OrderedWord N A) (k : ℕ) (hk : k ≤ N) (a : Option A) :
    labelCount (postedWord z k hk) a =
      (Finset.univ.filter (fun i : Fin N => i.val < k ∧ z i = a)).card := by
  classical
  unfold labelCount
  apply Finset.card_bij (fun i _ => (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin N))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨i.isLt, hi⟩
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun v : Fin N => v.val) hij)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨i.val, hi.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi.2
    · rfl

def correctVote {N : ℕ} {A : Type*} (z : OrderedWord N A) (a : A) : Prop :=
  plurality z = some a

inductive ComparatorCell
  | keep | posted | absent
  deriving DecidableEq, Fintype

/-- The three exhaustive comparator cells retain the ordered word. -/
noncomputable def comparatorCell {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (a : A) : ComparatorCell := by
  classical
  exact if correctVote z a then .keep else if reaches z k a then .posted else .absent

theorem comparatorCell_keep_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (a : A) :
    comparatorCell z k a = .keep ↔ correctVote z a := by
  classical
  by_cases hv : correctVote z a <;> by_cases hr : reaches z k a <;>
    simp [comparatorCell, hv, hr]

theorem comparatorCell_posted_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (a : A) :
    comparatorCell z k a = .posted ↔ ¬ correctVote z a ∧ reaches z k a := by
  classical
  by_cases hv : correctVote z a <;> by_cases hr : reaches z k a <;>
    simp [comparatorCell, hv, hr]

theorem comparatorCell_absent_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (a : A) :
    comparatorCell z k a = .absent ↔ ¬ correctVote z a ∧ ¬ reaches z k a := by
  classical
  by_cases hv : correctVote z a <;> by_cases hr : reaches z k a <;>
    simp [comparatorCell, hv, hr]

theorem reaches_zero {N : ℕ} {A : Type*} (z : OrderedWord N A) (a : A) :
    ¬ reaches z 0 a := by
  rintro ⟨i, hi, _⟩
  omega

theorem correctVote_reaches_full {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : A) (h : correctVote z a) : reaches z N a := by
  obtain ⟨i, hi⟩ := plurality_mem_word z a h
  exact ⟨i, i.isLt, hi⟩

/-- A correct comparator may rely entirely on an unposted suffix. -/
theorem correctVote_need_not_reach_prefix :
    ∃ z : OrderedWord 2 Unit, correctVote z () ∧ ¬ reaches z 1 () := by
  classical
  let z : OrderedWord 2 Unit := fun i => if i.val = 0 then none else some ()
  refine ⟨z, ?_, ?_⟩
  · apply plurality_unique_readable z ()
    · exact ⟨⟨1, by omega⟩, by simp [z]⟩
    · intro i
      exact (em (i = 0)).elim
        (fun hi => Or.inl (by simp [z, hi]))
        (fun hi => Or.inr (by simp [z, hi]))
  · rintro ⟨i, hi, hz⟩
    have hi0 : i.val = 0 := by omega
    have hieq : i = 0 := Fin.ext hi0
    simp [z, hieq] at hz

/-- A readable label has a strict-majority consensus at the declared threshold. -/
def consensusAt {N : ℕ} {A : Type*} (z : OrderedWord N A) (threshold : ℕ)
    (a : A) : Prop := threshold ≤ labelCount z (some a)

theorem labelCount_le_length {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a : Option A) : labelCount z a ≤ N := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem labelCount_disjoint_sum_le_length {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (a b : Option A) (hab : a ≠ b) :
    labelCount z a + labelCount z b ≤ N := by
  classical
  let s := Finset.univ.filter fun i => z i = a
  let t := Finset.univ.filter fun i => z i = b
  have hd : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact hab ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
  have hcard := Finset.card_le_card (show s ∪ t ⊆ Finset.univ from Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hd] at hcard
  simpa [s, t, labelCount] using hcard

theorem consensus_unique {N threshold : ℕ} {A : Type*}
    (z : OrderedWord N A) (hthreshold : N < 2 * threshold)
    (a b : A) (ha : consensusAt z threshold a) (hb : consensusAt z threshold b) :
    a = b := by
  by_contra hab
  have h := labelCount_disjoint_sum_le_length z (some a) (some b) (by simpa using hab)
  unfold consensusAt at ha hb
  omega

def falseConsensus {N : ℕ} {A : Type*} (z : OrderedWord N A)
    (threshold : ℕ) (correct : A) : Prop :=
  ∃ b, b ≠ correct ∧ consensusAt z threshold b

theorem falseConsensus_not_correct {N threshold : ℕ} {A : Type*}
    (z : OrderedWord N A) (hthreshold : N < 2 * threshold) (correct : A)
    (h : falseConsensus z threshold correct) : ¬ consensusAt z threshold correct := by
  obtain ⟨b, hbc, hb⟩ := h
  intro hc
  exact hbc (consensus_unique z hthreshold b correct hb hc)

inductive ConsensusCell
  | correct | wrongPosted | wrongAbsent | noConsensus
  deriving DecidableEq, Fintype

/-- Consensus counts all positions of z; k controls only the correct-answer
reach cutoff. `prefixConsensusCell` below counts the posted prefix itself. -/
noncomputable def consensusCell {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k threshold : ℕ) (correct : A) : ConsensusCell := by
  classical
  exact if consensusAt z threshold correct then .correct
    else if falseConsensus z threshold correct then
      if reaches z k correct then .wrongPosted else .wrongAbsent
    else .noConsensus

theorem consensusCell_correct_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k threshold : ℕ) (correct : A) :
    consensusCell z k threshold correct = .correct ↔ consensusAt z threshold correct := by
  classical
  by_cases hc : consensusAt z threshold correct <;>
    by_cases hf : falseConsensus z threshold correct <;>
    by_cases hr : reaches z k correct <;> simp [consensusCell, hc, hf, hr]

theorem consensusCell_wrongPosted_iff {N threshold : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (hthreshold : N < 2 * threshold) (correct : A) :
    consensusCell z k threshold correct = .wrongPosted ↔
      falseConsensus z threshold correct ∧ reaches z k correct := by
  classical
  by_cases hf : falseConsensus z threshold correct
  · have hc := falseConsensus_not_correct z hthreshold correct hf
    by_cases hr : reaches z k correct <;> simp [consensusCell, hc, hf, hr]
  · by_cases hc : consensusAt z threshold correct <;> simp [consensusCell, hc, hf]

theorem consensusCell_wrongAbsent_iff {N threshold : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (hthreshold : N < 2 * threshold) (correct : A) :
    consensusCell z k threshold correct = .wrongAbsent ↔
      falseConsensus z threshold correct ∧ ¬ reaches z k correct := by
  classical
  by_cases hf : falseConsensus z threshold correct
  · have hc := falseConsensus_not_correct z hthreshold correct hf
    by_cases hr : reaches z k correct <;> simp [consensusCell, hc, hf, hr]
  · by_cases hc : consensusAt z threshold correct <;> simp [consensusCell, hc, hf]

theorem consensusCell_noConsensus_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k threshold : ℕ) (correct : A) :
    consensusCell z k threshold correct = .noConsensus ↔
      ¬ ∃ b, consensusAt z threshold b := by
  classical
  have he : (∃ b, consensusAt z threshold b) ↔
      consensusAt z threshold correct ∨ falseConsensus z threshold correct := by
    constructor
    · rintro ⟨b, hb⟩
      by_cases hbc : b = correct
      · exact Or.inl (hbc ▸ hb)
      · exact Or.inr ⟨b, hbc, hb⟩
    · rintro (hc | ⟨b, _, hb⟩)
      · exact ⟨correct, hc⟩
      · exact ⟨b, hb⟩
  rw [he]
  by_cases hc : consensusAt z threshold correct <;>
    by_cases hf : falseConsensus z threshold correct <;>
    by_cases hr : reaches z k correct <;> simp [consensusCell, hc, hf, hr]

noncomputable def consensusCellProbability {N : ℕ} {A : Type*} [Fintype A]
    (L : Law (OrderedWord N A)) (k threshold : ℕ) (correct : A) (c : ConsensusCell) : ℝ :=
  L.prob (fun z => consensusCell z k threshold correct = c)

theorem consensusCellProbability_total {N : ℕ} {A : Type*} [Fintype A]
    (L : Law (OrderedWord N A)) (k threshold : ℕ) (correct : A) :
    consensusCellProbability L k threshold correct .correct +
      consensusCellProbability L k threshold correct .wrongPosted +
      consensusCellProbability L k threshold correct .wrongAbsent +
      consensusCellProbability L k threshold correct .noConsensus = 1 := by
  classical
  unfold consensusCellProbability Law.prob
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ z, L.mass z := by
      apply Finset.sum_congr rfl
      intro z _
      cases hc : consensusCell z k threshold correct <;> simp [hc]
    _ = 1 := L.total

/-- Consensus among exactly the k posted positions of a full comparator word. -/
noncomputable def prefixConsensusCell {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (hk : k ≤ N) (threshold : ℕ) (correct : A) :
    ConsensusCell := consensusCell (postedWord z k hk) k threshold correct

theorem prefix_consensus_unique {N k threshold : ℕ} {A : Type*}
    (z : OrderedWord N A) (hk : k ≤ N) (hthreshold : k < 2 * threshold)
    (a b : A) (ha : consensusAt (postedWord z k hk) threshold a)
    (hb : consensusAt (postedWord z k hk) threshold b) : a = b :=
  consensus_unique (postedWord z k hk) hthreshold a b ha hb

theorem prefixConsensusCell_correct_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (hk : k ≤ N) (threshold : ℕ) (correct : A) :
    prefixConsensusCell z k hk threshold correct = .correct ↔
      consensusAt (postedWord z k hk) threshold correct :=
  consensusCell_correct_iff (postedWord z k hk) k threshold correct

theorem prefixConsensusCell_wrongPosted_iff {N k threshold : ℕ} {A : Type*}
    (z : OrderedWord N A) (hk : k ≤ N) (hthreshold : k < 2 * threshold) (correct : A) :
    prefixConsensusCell z k hk threshold correct = .wrongPosted ↔
      falseConsensus (postedWord z k hk) threshold correct ∧ reaches z k correct := by
  unfold prefixConsensusCell
  rw [consensusCell_wrongPosted_iff _ _ hthreshold, postedWord_reaches_full]

theorem prefixConsensusCell_wrongAbsent_iff {N k threshold : ℕ} {A : Type*}
    (z : OrderedWord N A) (hk : k ≤ N) (hthreshold : k < 2 * threshold) (correct : A) :
    prefixConsensusCell z k hk threshold correct = .wrongAbsent ↔
      falseConsensus (postedWord z k hk) threshold correct ∧ ¬ reaches z k correct := by
  unfold prefixConsensusCell
  rw [consensusCell_wrongAbsent_iff _ _ hthreshold, postedWord_reaches_full]

theorem prefixConsensusCell_noConsensus_iff {N : ℕ} {A : Type*}
    (z : OrderedWord N A) (k : ℕ) (hk : k ≤ N) (threshold : ℕ) (correct : A) :
    prefixConsensusCell z k hk threshold correct = .noConsensus ↔
      ¬ ∃ b, consensusAt (postedWord z k hk) threshold b :=
  consensusCell_noConsensus_iff (postedWord z k hk) k threshold correct

/-- Prefix-consensus probabilities under the law of the full ordered word. -/
noncomputable def prefixConsensusCellProbability {N : ℕ} {A : Type*} [Fintype A]
    (L : Law (OrderedWord N A)) (k : ℕ) (hk : k ≤ N) (threshold : ℕ)
    (correct : A) (c : ConsensusCell) : ℝ :=
  L.prob (fun z => prefixConsensusCell z k hk threshold correct = c)

theorem prefixConsensusCellProbability_total {N : ℕ} {A : Type*} [Fintype A]
    (L : Law (OrderedWord N A)) (k : ℕ) (hk : k ≤ N) (threshold : ℕ) (correct : A) :
    prefixConsensusCellProbability L k hk threshold correct .correct +
      prefixConsensusCellProbability L k hk threshold correct .wrongPosted +
      prefixConsensusCellProbability L k hk threshold correct .wrongAbsent +
      prefixConsensusCellProbability L k hk threshold correct .noConsensus = 1 := by
  classical
  unfold prefixConsensusCellProbability Law.prob
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ z, L.mass z := by
      apply Finset.sum_congr rfl
      intro z _
      cases hc : prefixConsensusCell z k hk threshold correct <;> simp [hc]
    _ = 1 := L.total

theorem prefix_falseConsensus_probability_cells {N k threshold : ℕ} {A : Type*}
    [Fintype A] (L : Law (OrderedWord N A)) (hk : k ≤ N)
    (hthreshold : k < 2 * threshold) (correct : A) :
    L.prob (fun z => falseConsensus (postedWord z k hk) threshold correct) =
      prefixConsensusCellProbability L k hk threshold correct .wrongPosted +
      prefixConsensusCellProbability L k hk threshold correct .wrongAbsent := by
  classical
  unfold prefixConsensusCellProbability Law.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  rw [prefixConsensusCell_wrongPosted_iff z hk hthreshold correct,
    prefixConsensusCell_wrongAbsent_iff z hk hthreshold correct]
  by_cases hf : falseConsensus (postedWord z k hk) threshold correct <;>
    by_cases hr : reaches z k correct <;> simp [hf, hr]

theorem falseConsensus_probability_cells {N threshold : ℕ} {A : Type*} [Fintype A]
    (L : Law (OrderedWord N A)) (k : ℕ) (hthreshold : N < 2 * threshold) (correct : A) :
    L.prob (fun z => falseConsensus z threshold correct) =
      consensusCellProbability L k threshold correct .wrongPosted +
      consensusCellProbability L k threshold correct .wrongAbsent := by
  classical
  unfold consensusCellProbability Law.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  rw [consensusCell_wrongPosted_iff z k hthreshold correct,
    consensusCell_wrongAbsent_iff z k hthreshold correct]
  by_cases hf : falseConsensus z threshold correct <;>
    by_cases hr : reaches z k correct <;> simp [hf, hr]

/-- Strict-majority false consensus is a disjoint sum over wrong readable labels. -/
theorem falseConsensus_probability_eq_sum {N threshold : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (L : Law (OrderedWord N A))
    (hthreshold : N < 2 * threshold) (correct : A) :
    L.prob (fun z => falseConsensus z threshold correct) =
      ∑ b, if b = correct then 0 else L.prob (fun z => consensusAt z threshold b) := by
  classical
  unfold Law.prob
  have hsum : (∑ b, if b = correct then (0 : ℝ) else
      ∑ z, if consensusAt z threshold b then L.mass z else 0) =
      ∑ z, ∑ b, if b = correct then 0 else
        if consensusAt z threshold b then L.mass z else 0 := by
    calc
      _ = ∑ b, ∑ z, if b = correct then (0 : ℝ) else
          if consensusAt z threshold b then L.mass z else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : b = correct <;> simp [hb]
      _ = _ := Finset.sum_comm
  rw [hsum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases he : falseConsensus z threshold correct
  · obtain ⟨b, hbc, hb⟩ := he
    simp only [show falseConsensus z threshold correct from ⟨b, hbc, hb⟩, ↓reduceIte]
    symm
    rw [Finset.sum_eq_single b]
    · simp [hbc, hb]
    · intro c _ hcb
      by_cases hca : c = correct
      · simp [hca]
      · have hc : ¬ consensusAt z threshold c := by
          intro hc
          exact hcb (consensus_unique z hthreshold c b hc hb)
        simp [hca, hc]
    · simp
  · simp only [he, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro b _
    by_cases hbc : b = correct
    · simp [hbc]
    · have hb : ¬ consensusAt z threshold b := fun hb => he ⟨b, hbc, hb⟩
      simp [hbc, hb]

/-- The IID law is a genuine finite product on ordered coordinates. -/
noncomputable def iidWordLaw {A : Type*} [Fintype A] (π : Law (Option A)) (N : ℕ) :
    Law (OrderedWord N A) := Law.pi (fun _ : Fin N => π)

noncomputable def voteAccuracy {A : Type*} [Fintype A]
    (π : Law (Option A)) (N : ℕ) (a : A) : ℝ :=
  (iidWordLaw π N).prob (fun z => correctVote z a)

noncomputable def reachProbability {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) : ℝ :=
  (iidWordLaw π N).prob (fun z => reaches z k a)

/-- Rectangle probabilities factor over separate product coordinates. -/
theorem prob_pi_forall {ι : Type*} [Fintype ι] [DecidableEq ι] {Ωs : ι → Type*}
    [∀ i, Fintype (Ωs i)] (Ls : ∀ i, Law (Ωs i)) (E : ∀ i, Ωs i → Prop) :
    (Law.pi Ls).prob (fun ω => ∀ i, E i (ω i)) = ∏ i, (Ls i).prob (E i) := by
  classical
  unfold Law.prob Law.pi
  dsimp only
  calc
    _ = ∑ ω : ∀ i, Ωs i, ∏ i, if E i (ω i) then (Ls i).mass (ω i) else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : ∀ i, E i (ω i)
      · simp [he]
      · obtain ⟨i, hi⟩ := not_forall.mp he
        simp only [he, ↓reduceIte]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    _ = _ := (Fintype.prod_sum (fun i x => if E i x then (Ls i).mass x else 0)).symm

theorem prob_single_label_compl {A : Type*} [Fintype A]
    (π : Law (Option A)) (a : Option A) :
    π.prob (fun x => x ≠ a) = 1 - π.mass a := by
  classical
  rw [π.prob_compl (fun x => x = a)]
  have hs : π.prob (fun x => x = a) = π.mass a := by
    unfold Law.prob
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hs]

theorem no_appearance_probability {A : Type*} [Fintype A]
    (π : Law (Option A)) (N : ℕ) (a : Option A) :
    (iidWordLaw π N).prob (fun z => ∀ i, z i ≠ a) = (1 - π.mass a) ^ N := by
  rw [iidWordLaw, prob_pi_forall (fun _ : Fin N => π) (fun _ x => x ≠ a)]
  simp [prob_single_label_compl]

theorem reach_full_probability {A : Type*} [Fintype A]
    (π : Law (Option A)) (N : ℕ) (a : A) :
    reachProbability π N N a = 1 - (1 - π.mass (some a)) ^ N := by
  have he : (fun z : OrderedWord N A => reaches z N a) =
      (fun z => ¬ ∀ i, z i ≠ some a) := by
    funext z
    apply propext
    simp [reaches]
  unfold reachProbability
  rw [he, Law.prob_compl, no_appearance_probability]

theorem prefixPositions_card {N k : ℕ} (hk : k ≤ N) :
    (Finset.univ.filter (fun i : Fin N => i.val < k)).card = k := by
  classical
  let s := Finset.univ.filter (fun i : Fin N => i.val < k)
  let e : Fin k ≃ s := {
    toFun := fun i => ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, by simp [s, i.isLt]⟩
    invFun := fun i => ⟨i.val.val, (Finset.mem_filter.mp i.property).2⟩
    left_inv := fun i => rfl
    right_inv := fun i => by apply Subtype.ext; rfl }
  simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr e).symm

/-- IID reach for any possibly empty prefix of the comparator word. -/
theorem reach_prefix_probability {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (hk : k ≤ N) (a : A) :
    reachProbability π N k a = 1 - (1 - π.mass (some a)) ^ k := by
  classical
  have he : (fun z : OrderedWord N A => reaches z k a) =
      (fun z => ¬ ∀ i, i.val < k → z i ≠ some a) := by
    funext z
    apply propext
    simp [reaches]
  have hcoord (i : Fin N) :
      π.prob (fun x => i.val < k → x ≠ some a) =
        if i.val < k then 1 - π.mass (some a) else 1 := by
    by_cases hi : i.val < k
    · simpa only [hi, true_implies, ↓reduceIte] using prob_single_label_compl π (some a)
    · simp [hi]
  unfold reachProbability
  rw [he, Law.prob_compl, iidWordLaw,
    prob_pi_forall (fun _ : Fin N => π) (fun i x => i.val < k → x ≠ some a)]
  simp_rw [hcoord]
  rw [Finset.prod_ite]
  simp [prefixPositions_card hk]

theorem voteAccuracy_zero {A : Type*} [Fintype A]
    (π : Law (Option A)) (a : A) : voteAccuracy π 0 a = 0 := by
  unfold voteAccuracy correctVote
  simp [plurality_empty]

theorem voteAccuracy_le_reach_full {A : Type*} [Fintype A]
    (π : Law (Option A)) (N : ℕ) (a : A) :
    voteAccuracy π N a ≤ reachProbability π N N a :=
  (iidWordLaw π N).prob_mono (fun z hz => correctVote_reaches_full z a hz)

/-- A readable label of zero mass has zero probability of appearing. -/
theorem zero_mass_reach {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (hk : k ≤ N) (a : A)
    (ha : π.mass (some a) = 0) : reachProbability π N k a = 0 := by
  rw [reach_prefix_probability π N k hk a, ha]
  simp

theorem zero_mass_voteAccuracy {A : Type*} [Fintype A]
    (π : Law (Option A)) (N : ℕ) (a : A) (ha : π.mass (some a) = 0) :
    voteAccuracy π N a = 0 := by
  have h := voteAccuracy_le_reach_full π N a
  rw [zero_mass_reach π N N le_rfl a ha] at h
  exact le_antisymm h ((iidWordLaw π N).prob_nonneg _)

/-- Exact comparator-cell probabilities; these are defined on the ordered experiment. -/
noncomputable def cellProbability {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) (c : ComparatorCell) : ℝ :=
  (iidWordLaw π N).prob (fun z => comparatorCell z k a = c)

theorem cellProbability_total {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) :
    cellProbability π N k a .keep + cellProbability π N k a .posted +
      cellProbability π N k a .absent = 1 := by
  classical
  unfold cellProbability Law.prob
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ z, (iidWordLaw π N).mass z := by
      apply Finset.sum_congr rfl
      intro z _
      cases hc : comparatorCell z k a <;> simp [hc]
    _ = 1 := (iidWordLaw π N).total

theorem cellProbability_keep {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) :
    cellProbability π N k a .keep = voteAccuracy π N a := by
  unfold cellProbability voteAccuracy
  congr 1
  funext z
  exact propext (comparatorCell_keep_iff z k a)

noncomputable def jointVoteReach {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) : ℝ :=
  (iidWordLaw π N).prob (fun z => correctVote z a ∧ reaches z k a)

noncomputable def jointVoteAbsent {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) : ℝ :=
  (iidWordLaw π N).prob (fun z => correctVote z a ∧ ¬ reaches z k a)

theorem jointVote_partition {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) :
    voteAccuracy π N a = jointVoteReach π N k a + jointVoteAbsent π N k a := by
  classical
  unfold voteAccuracy jointVoteReach jointVoteAbsent Law.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hv : correctVote z a <;> by_cases hr : reaches z k a <;> simp [hv, hr]

theorem cellProbability_posted {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) :
    cellProbability π N k a .posted =
      reachProbability π N k a - jointVoteReach π N k a := by
  classical
  unfold cellProbability reachProbability jointVoteReach Law.prob
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  rw [comparatorCell_posted_iff]
  by_cases hv : correctVote z a <;> by_cases hr : reaches z k a <;> simp [hv, hr]

theorem cellProbability_absent {A : Type*} [Fintype A]
    (π : Law (Option A)) (N k : ℕ) (a : A) :
    cellProbability π N k a .absent =
      1 - reachProbability π N k a - jointVoteAbsent π N k a := by
  classical
  have hsum := cellProbability_total π N k a
  rw [cellProbability_keep, jointVote_partition, cellProbability_posted] at hsum
  linarith

end SEKernel.Epistemic
