import SEKernel.EpistemicPayoff
import SEKernel.NoisySelection
import SEKernel.Law2_ESDI
import SEKernel.PluralityCountExamples
import SEKernel.SilentGene
import SEKernel.MutationBaseline

/-! Finite spawning, marginal-slot certificates, and complete-allocation policies.
Indices start at zero.  An allocation is an actual prefix-closed set of finite
call slots, with cardinality at most the natural-number budget. -/
namespace SEKernel.SpawnAllocation

open Finset FiniteProbability
open scoped Classical BigOperators
noncomputable section

/-- Reach-only accuracy with fixed uptake constants. -/
def reachPayoff (alpha beta p : ℝ) (k : ℕ) : ℝ :=
  alpha-(alpha-beta)*(1-p)^k

def reachMarginal (alpha beta p : ℝ) (k : ℕ) : ℝ :=
  (alpha-beta)*p*(1-p)^k

theorem reach_marginal_identity (alpha beta p : ℝ) (k : ℕ) :
    reachPayoff alpha beta p (k+1)-reachPayoff alpha beta p k =
      reachMarginal alpha beta p k := by
  unfold reachPayoff reachMarginal
  rw [pow_succ]
  ring

theorem reach_zero (alpha beta p : ℝ) : reachPayoff alpha beta p 0=beta := by
  simp [reachPayoff]

theorem reach_endpoint_zero (alpha beta : ℝ) (k : ℕ) :
    reachPayoff alpha beta 0 k=beta ∧ reachMarginal alpha beta 0 k=0 := by
  simp [reachPayoff,reachMarginal]

theorem reach_endpoint_one (alpha beta : ℝ) :
    reachPayoff alpha beta 1 0=beta ∧
      (∀ k, reachPayoff alpha beta 1 (k+1)=alpha) ∧
      reachMarginal alpha beta 1 0=alpha-beta ∧
      (∀ k, reachMarginal alpha beta 1 (k+1)=0) := by
  simp [reachPayoff,reachMarginal]

theorem reach_marginals_nonneg {alpha beta p : ℝ} (hab : beta ≤ alpha)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (k : ℕ) : 0 ≤ reachMarginal alpha beta p k := by
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) hp) (pow_nonneg (by linarith) _)

theorem reach_marginals_decreasing {alpha beta p : ℝ} (hab : beta ≤ alpha)
    (hp : 0 ≤ p) (hp' : p ≤ 1) : Antitone (reachMarginal alpha beta p) := by
  apply antitone_nat_of_succ_le
  intro k
  have hn := reach_marginals_nonneg hab hp hp' k
  change (alpha-beta)*p*(1-p)^(k+1) ≤ _
  rw [pow_succ, ← mul_assoc]
  change reachMarginal alpha beta p k*(1-p) ≤ reachMarginal alpha beta p k
  nlinarith

theorem reach_telescoping (alpha beta p : ℝ) (k : ℕ) :
    reachPayoff alpha beta p k=beta+∑ r∈Finset.range k,reachMarginal alpha beta p r := by
  induction k with
  | zero => simp [reach_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    linarith [reach_marginal_identity alpha beta p k]

/-- The finite wedge is a new discrete expression; no continuous envelope
or `PriceMarket.replication_wedge` theorem is invoked. -/
theorem finite_spawning_wedge (alpha beta p W : ℝ) (cost : ℕ→ℝ) (k : ℕ) :
    (W*reachPayoff alpha beta p (k+1)-cost (k+1))-
      (W*reachPayoff alpha beta p k-cost k)=
      W*reachMarginal alpha beta p k-(cost (k+1)-cost k) := by
  rw [← reach_marginal_identity alpha beta p k]
  ring

section Slots
variable {ι : Type*} [Fintype ι]

/-- Explicit per-item dual multiplier for the unit-capacity constraint. -/
def itemMultiplier (d lambda : ℝ) : ℝ := max (d-lambda) 0

theorem itemMultiplier_nonneg (d lambda : ℝ) : 0 ≤ itemMultiplier d lambda := le_max_right _ _

theorem item_dual_feasible (d lambda : ℝ) : d ≤ lambda+itemMultiplier d lambda := by
  have h := le_max_left (d-lambda) 0
  unfold itemMultiplier
  linarith

/-- The slot LP has a separate unit upper bound for EVERY item. -/
theorem slot_lp_dual (d z : ι→ℝ) (B : ℕ) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hz : ∀ i,0 ≤ z i ∧ z i ≤ 1) (hB : ∑ i,z i ≤ B) :
    (∑ i,d i*z i) ≤ lambda*B+∑ i,itemMultiplier (d i) lambda := by
  have ht (i : ι) : d i*z i ≤ lambda*z i+itemMultiplier (d i) lambda := by
    have h1 := mul_le_mul_of_nonneg_right (item_dual_feasible (d i) lambda) (hz i).1
    have h2 := mul_le_mul_of_nonneg_left (hz i).2 (itemMultiplier_nonneg (d i) lambda)
    nlinarith
  calc
    _  ≤  ∑ i,(lambda*z i+itemMultiplier (d i) lambda) := Finset.sum_le_sum (fun i _=>ht i)
    _ = lambda*(∑ i,z i)+∑ i,itemMultiplier (d i) lambda := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- A certificate states selected/unused marginal inequalities and actual
budget saturation when the price is positive. -/
structure SlotCertificate (d : ι→ℝ) (B : ℕ) (A : Finset ι) (lambda : ℝ) : Prop where
  nonneg : 0 ≤ lambda
  budget : A.card ≤ B
  selected : ∀ i∈A, lambda ≤ d i
  unselected : ∀ i∉A, d i ≤ lambda
  slack : lambda*((B:ℝ)-A.card)=0

theorem slot_certificate_value {d : ι→ℝ} {B : ℕ} {A : Finset ι} {lambda : ℝ}
    (h : SlotCertificate d B A lambda) :
    (∑ i∈A,d i)=lambda*B+∑ i,itemMultiplier (d i) lambda := by
  classical
  have hi (i : ι) : itemMultiplier (d i) lambda=if i∈A then d i-lambda else 0 := by
    by_cases ha : i∈A
    · simp [itemMultiplier,ha,max_eq_left (sub_nonneg.mpr (h.selected i ha))]
    · simp [itemMultiplier,ha,max_eq_right (sub_nonpos.mpr (h.unselected i ha))]
  simp_rw [hi]
  rw [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul]
  nlinarith [h.slack]

/-- Every certified set is optimal against fractional slot choices. -/
theorem slot_certificate_optimal {d : ι→ℝ} {B : ℕ} {A : Finset ι} {lambda : ℝ}
    (h : SlotCertificate d B A lambda) (z : ι→ℝ)
    (hz : ∀ i,0 ≤ z i ∧ z i ≤ 1) (hB : ∑ i,z i ≤ B) :
    (∑ i,d i*z i) ≤ ∑ i∈A,d i := by
  rw [slot_certificate_value h]
  exact slot_lp_dual d z B lambda h.nonneg hz hB

/-- G6's first lemma: the actual maximum-image choice dominates every
remaining item.  The finite choice is constructed, not supplied. -/
def greedyPick (d : ι→ℝ) (remaining : Finset ι) (hne : remaining.Nonempty) : ι :=
  Classical.choose (Finset.exists_max_image remaining d hne)

theorem greedy_pick_dominates_unpicked (d : ι→ℝ) (remaining : Finset ι)
    (hne : remaining.Nonempty) : greedyPick d remaining hne∈remaining ∧
      ∀ j∈remaining,d j ≤ d (greedyPick d remaining hne) :=
  Classical.choose_spec (Finset.exists_max_image remaining d hne)

/-- G6's second lemma.  Nonnegativity permits comparisons with FEWER than b
items as well as comparisons with b-sets. -/
theorem dominating_bset_maximum (d : ι→ℝ) (hd : ∀ i,0 ≤ d i)
    (A : Finset ι) (hdom : ∀ i∈A,∀ j∉A,d j ≤ d i)
    (C : Finset ι) (hcard : C.card ≤ A.card) : (∑ i∈C,d i) ≤ ∑ i∈A,d i := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image A d hA
    let lambda := d i
    have hc : SlotCertificate d A.card A lambda := by
      refine ⟨hd i,le_rfl,?_,?_,by simp⟩
      · intro j hj; exact hmin j hj
      · intro j hj; exact hdom i hi j hj
    have hz : ∀ j,0 ≤ (if j∈C then (1:ℝ) else 0) ∧ (if j∈C then (1:ℝ) else 0) ≤ 1 := by
      intro j; split_ifs <;> norm_num
    have hb : (∑ j,if j∈C then (1:ℝ) else 0) ≤ A.card := by
      simpa using (show (C.card:ℝ) ≤ A.card by exact_mod_cast hcard)
    have h := slot_certificate_optimal hc (fun j=>if j∈C then 1 else 0) hz hb
    simpa using h
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hC : C=∅ := Finset.card_eq_zero.mp (by simpa [he] using hcard)
    simp [he,hC]

end Slots

/-- Marginal slots carry task identity and the call's zero-based index. -/
abbrev CallSlot {J : Type*} (K : J→ℕ) := Sigma (fun j=>Fin (K j))

def PrefixClosed {J : Type*} {K : J→ℕ} (A : Finset (CallSlot K)) : Prop :=
  ∀ j (r s : Fin (K j)),s ≤ r → Sigma.mk j r∈A → Sigma.mk j s∈A

/-- A complete allocation is a concrete feasible set of prefix slots. -/
abbrev FeasibleAllocation {J : Type*} (K : J→ℕ) (B : ℕ) :=
  {A : Finset (CallSlot K) // PrefixClosed A ∧ A.card ≤ B}

section Existence
variable {J : Type*} [Fintype J] (K : J→ℕ)

/-- The tie key is the within-task call index, so equal-valued earlier calls
precede later calls. Slot identity is preserved by the finite equivalence. -/
def rankedSlotSet (d : CallSlot K→ℝ) (B : ℕ) : Finset (CallSlot K) :=
  let e := Fintype.equivFin (CallSlot K)
  (NoisySelection.lexSurvivors (Nat.min_le_right B (Fintype.card (CallSlot K)))
    (fun i=>d (e.symm i)) (fun i=>(e.symm i).2.val)).val.map e.symm.toEmbedding

theorem rankedSlotSet_card (d : CallSlot K→ℝ) (B : ℕ) :
    (rankedSlotSet K d B).card=min B (Fintype.card (CallSlot K)) := by
  unfold rankedSlotSet
  rw [Finset.card_map]
  exact (NoisySelection.lexSurvivors (Nat.min_le_right B (Fintype.card (CallSlot K)))
    (fun i=>d ((Fintype.equivFin (CallSlot K)).symm i))
    (fun i=>((Fintype.equivFin (CallSlot K)).symm i).2.val)).property

theorem rankedSlotSet_dominates (d : CallSlot K→ℝ) (B : ℕ) :
    ∀ i∈rankedSlotSet K d B,∀ j∉rankedSlotSet K d B,d j ≤ d i := by
  classical
  intro i hi j hj
  let e := Fintype.equivFin (CallSlot K)
  have hi' : e i∈(NoisySelection.lexSurvivors
      (Nat.min_le_right B (Fintype.card (CallSlot K)))
      (fun r=>d (e.symm r)) (fun r=>(e.symm r).2.val)).val := by
    simpa [rankedSlotSet,e] using hi
  have hj' : e j∉(NoisySelection.lexSurvivors
      (Nat.min_le_right B (Fintype.card (CallSlot K)))
      (fun r=>d (e.symm r)) (fun r=>(e.symm r).2.val)).val := by
    simpa [rankedSlotSet,e] using hj
  simpa using NoisySelection.lexSurvivors_topSet
    (Nat.min_le_right B (Fintype.card (CallSlot K)))
    (fun r=>d (e.symm r)) (fun r=>(e.symm r).2.val) (e i) hi' (e j) hj'

/-- Record order, including the tie key, crosses the take/drop boundary. -/
theorem selected_record_le_unselected {P S : ℕ} (hSP : S ≤ P)
    (score : Fin P→ℝ) (key : Fin P→ℤ) (i j : Fin P)
    (hi : i∈(NoisySelection.lexSurvivors hSP score key).val)
    (hj : j∉(NoisySelection.lexSurvivors hSP score key).val) :
    NoisySelection.rankRecord score key i ≤ NoisySelection.rankRecord score key j := by
  have hi' : i∈(NoisySelection.rankingList score key).take S := by
    simpa [NoisySelection.lexSurvivors] using hi
  have hj' : j∉(NoisySelection.rankingList score key).take S := by
    simpa [NoisySelection.lexSurvivors] using hj
  have hjdrop : j∈(NoisySelection.rankingList score key).drop S := by
    have h := NoisySelection.rankingList_mem score key j
    rw [← List.take_append_drop S (NoisySelection.rankingList score key),List.mem_append] at h
    exact h.resolve_left hj'
  have h := NoisySelection.rankingList_lexicographic score key
  rw [← List.take_append_drop S (NoisySelection.rankingList score key),List.pairwise_append] at h
  exact h.2.2 i hi' j hjdrop

theorem rankedSlotSet_prefix (d : CallSlot K→ℝ) (B : ℕ)
    (hdec : ∀ j,Antitone (fun r : Fin (K j)=>d ⟨j,r⟩)) :
    PrefixClosed (rankedSlotSet K d B) := by
  classical
  intro j r q hqr hr
  by_contra hq
  have hne : q≠r := by intro h; subst q; exact hq hr
  have hlt : q<r := lt_of_le_of_ne hqr hne
  let e := Fintype.equivFin (CallSlot K)
  let score := fun i=>d (e.symm i)
  let key : Fin (Fintype.card (CallSlot K))→ℤ := fun i=>(e.symm i).2.val
  have hr' : e ⟨j,r⟩∈(NoisySelection.lexSurvivors
      (Nat.min_le_right B (Fintype.card (CallSlot K))) score key).val := by
    simpa [rankedSlotSet,e,score,key] using hr
  have hq' : e ⟨j,q⟩∉(NoisySelection.lexSurvivors
      (Nat.min_le_right B (Fintype.card (CallSlot K))) score key).val := by
    simpa [rankedSlotSet,e,score,key] using hq
  have hrel := selected_record_le_unselected
    (Nat.min_le_right B (Fintype.card (CallSlot K))) score key (e ⟨j,r⟩) (e ⟨j,q⟩) hr' hq'
  have hd := hdec j hqr
  simp only [NoisySelection.rankRecord,score,key,Equiv.symm_apply_apply,
    Prod.Lex.toLex_le_toLex] at hrel
  have hkr : key (e ⟨j,r⟩)=(r.val:ℤ) := congrArg (fun s : CallSlot K=>(s.2.val:ℤ)) (e.symm_apply_apply ⟨j,r⟩)
  have hkq : key (e ⟨j,q⟩)=(q.val:ℤ) := congrArg (fun s : CallSlot K=>(s.2.val:ℤ)) (e.symm_apply_apply ⟨j,q⟩)
  have hcast : (q.val:ℤ)<r.val := by exact_mod_cast hlt
  rcases hrel with hscore | ⟨_,hkey⟩
  · linarith
  · rcases hkey with hkey | ⟨hkey,_⟩
    · change key (e ⟨j,r⟩)<key (e ⟨j,q⟩) at hkey
      rw [hkr,hkq] at hkey
      omega
    · change key (e ⟨j,r⟩)=key (e ⟨j,q⟩) at hkey
      rw [hkr,hkq] at hkey
      omega

end Existence

section Certificates
variable {ι : Type*} [Fintype ι]

/-- A largest-value b-set, b=min(B,item count), always has a nonnegative
threshold certificate, including an empty item set and B=0. -/
theorem dominating_set_has_certificate (d : ι→ℝ) (hd : ∀ i,0 ≤ d i)
    (B : ℕ) (A : Finset ι) (hsize : A.card=min B (Fintype.card ι))
    (hdom : ∀ i∈A,∀ j∉A,d j ≤ d i) : ∃ lambda,SlotCertificate d B A lambda := by
  classical
  by_cases hfull : A.card=B
  · by_cases hne : A.Nonempty
    · obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image A d hne
      refine ⟨d i,hd i,by omega,?_,?_,by simp [hfull]⟩
      · exact fun j hj=>hmin j hj
      · exact fun j hj=>hdom i hi j hj
    · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hB : B=0 := by simpa [he] using hfull.symm
      refine ⟨∑ i,d i,Finset.sum_nonneg (fun i _=>hd i),by omega,?_,?_,by simp [hB,he]⟩
      · simp [he]
      · intro i _
        exact Finset.single_le_sum (fun j _=>hd j) (Finset.mem_univ i)
  · have hall : A=Finset.univ := by
      apply Finset.eq_univ_of_card
      have hbound := Finset.card_le_univ A
      omega
    refine ⟨0,le_rfl,by omega,?_,?_,by simp⟩
    · exact fun i _=>hd i
    · simp [hall]

/-- The effective budget for the unit-capacity LP is min(B,item count). -/
theorem slot_lp_dual_min (d z : ι→ℝ) (B : ℕ) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hz : ∀ i,0 ≤ z i ∧ z i ≤ 1) (hB : ∑ i,z i ≤ B) :
    (∑ i,d i*z i) ≤ lambda*(min B (Fintype.card ι):ℕ)+∑ i,itemMultiplier (d i) lambda := by
  apply slot_lp_dual d z (min B (Fintype.card ι)) lambda hlambda hz
  have hcount : (∑ i,z i) ≤ Fintype.card ι := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(hz i).2)
  rw [Nat.cast_min]
  exact le_min hB hcount

end Certificates

/-- Existence, not just certificate sufficiency: sorting finite marginal slots
constructs a prefix allocation and its shadow price for every natural budget. -/
theorem exists_certified_allocation {J : Type*} [Fintype J] (K : J→ℕ)
    (d : CallSlot K→ℝ) (hd : ∀ i,0 ≤ d i)
    (hdec : ∀ j,Antitone (fun r : Fin (K j)=>d ⟨j,r⟩)) (B : ℕ) :
    ∃ (A : FeasibleAllocation K B) (lambda : ℝ),
      A.val.card=min B (Fintype.card (CallSlot K)) ∧ SlotCertificate d B A.val lambda := by
  let A := rankedSlotSet K d B
  have hcard := rankedSlotSet_card K d B
  have hprefix := rankedSlotSet_prefix K d B hdec
  obtain ⟨lambda,hcert⟩ := dominating_set_has_certificate d hd B A hcard
    (rankedSlotSet_dominates K d B)
  exact ⟨⟨A,hprefix,hcert.budget⟩,lambda,hcard,hcert⟩

section AllocationLift
variable {J : Type*} [Fintype J] (K : J→ℕ) (B : ℕ)

theorem feasible_allocation_nonempty : Nonempty (FeasibleAllocation K B) := by
  classical
  refine ⟨⟨∅,?_,by simp⟩⟩
  intro j r q _ h
  simp at h

def allocationReturn (baseline : ℝ) (d : CallSlot K→ℝ)
    (A : FeasibleAllocation K B) : ℝ := baseline+∑ i∈A.val,d i

/-- Exact Law2 lift on the SUBTYPE of complete feasible allocations.  The
constructed vector has full mass one and is supported within the argmax.
Slot-cap constraints are already encoded in the type, not folded into Law2. -/
theorem whole_allocation_kkt (f : FeasibleAllocation K B→ℝ)
    (hf : ∀ A,0<f A) :
    ∃ (x : FeasibleAllocation K B→ℝ) (mu : ℝ),
      (∀ A,0 ≤ x A) ∧ (∑ A,x A=1) ∧
      (∀ A,f A ≤ mu) ∧ (∀ A,0<x A→f A=mu) ∧
      Law2.KKT f (fun _=>1) (fun _=>0) 1 0 x mu 0 := by
  classical
  letI := feasible_allocation_nonempty K B
  obtain ⟨x,hx,hsum,hsupport,hmax⟩ := Law2.esdi_exists_const f
  have hmu := Law1.mean_pos hx hsum hf
  refine ⟨x,Law1.mean x f,hx,hsum,hmax,hsupport,?_,hmu.le,le_rfl,?_,?_,?_,?_⟩
  · refine ⟨hx,?_,by simp⟩
    simpa using hsum.le
  · simpa using hmax
  · simpa using hsupport
  · intro _; simpa using hsum
  · intro h; linarith

/-- The lift consumes the actual existing Law2 optimality/reduced-return
results, with no new strong-duality or continuous-envelope premise. -/
theorem whole_allocation_kkt_consequences
    {f x : FeasibleAllocation K B→ℝ} {mu : ℝ}
    (h : Law2.KKT f (fun _=>1) (fun _=>0) 1 0 x mu 0) :
    Law2.IsLPOptimal f (fun _=>1) (fun _=>0) 1 0 x ∧
      Law2.NashEquilibrium f (fun _=>1) (fun _=>0) 1 0 x ∧
      (∀ A,f A-mu ≤ 0) ∧ (∀ A,0<x A→f A-mu=0) := by
  have ho := h.isLPOptimal
  refine ⟨ho,(Law2.nash_iff_lpOptimal).2 ho,?_,?_⟩
  · simpa using h.reduced_return.1
  · simpa using h.reduced_return.2

/-- A certified allocation beats every other concrete feasible allocation. -/
theorem certified_allocation_optimal (baseline : ℝ) (d : CallSlot K→ℝ)
    (A : FeasibleAllocation K B) (lambda : ℝ) (h : SlotCertificate d B A.val lambda)
    (C : FeasibleAllocation K B) :
    allocationReturn K B baseline d C ≤ allocationReturn K B baseline d A := by
  classical
  have hz : ∀ i,0 ≤ (if i∈C.val then (1:ℝ) else 0) ∧
      (if i∈C.val then (1:ℝ) else 0) ≤ 1 := by intro i; split_ifs <;> norm_num
  have hb : (∑ i,if i∈C.val then (1:ℝ) else 0) ≤ B := by
    simpa using (show (C.val.card:ℝ) ≤ B by exact_mod_cast C.property.2)
  have ho := slot_certificate_optimal h (fun i=>if i∈C.val then 1 else 0) hz hb
  have ho' : (∑ i∈C.val,d i) ≤ ∑ i∈A.val,d i := by simpa using ho
  simpa [allocationReturn,add_comm] using add_le_add_left ho' baseline

end AllocationLift

/-- Uniform forecast error bounds the regret of ANY forecast maximizer. -/
theorem forecast_regret {ι : Type*} (R forecast : ι→ℝ) (best chosen : ι)
    (eps : ℝ) (herr : ∀ i,|forecast i-R i| ≤ eps)
    (hchoice : ∀ i,forecast i ≤ forecast chosen) : R best-R chosen ≤ 2*eps := by
  have h1 := (abs_le.mp (herr best)).1
  have h2 := (abs_le.mp (herr chosen)).2
  have h3 := hchoice best
  linarith

theorem forecast_gap_identifies {ι : Type*} (R forecast : ι→ℝ) (best chosen : ι)
    (eps : ℝ) (herr : ∀ i,|forecast i-R i| ≤ eps)
    (hchoice : ∀ i,forecast i ≤ forecast chosen)
    (hgap : ∀ i,R i<R best→2*eps<R best-R i) : R chosen ≥ R best := by
  have hreg := forecast_regret R forecast best chosen eps herr hchoice
  by_contra hn
  exact not_lt_of_ge hreg (hgap chosen (lt_of_not_ge hn))

/-- Doc B E.5: the additional call is chosen before observing proposals. -/
theorem biased_forecast_two_task_B :
    reachMarginal 1 0 (1/5) 1=4/25 ∧ reachMarginal 1 0 (9/10) 1=9/100 ∧
    reachPayoff 1 0 (1/5) 2+reachPayoff 1 0 (9/10) 1=63/50 ∧
    reachPayoff 1 0 (1/5) 1+reachPayoff 1 0 (9/10) 2=119/100 ∧
    reachMarginal 1 0 (99/100) 1=99/10000 ∧ (99/10000:ℝ)<9/100 ∧
    (63/50:ℝ)-119/100=7/100 := by norm_num [reachMarginal,reachPayoff]

/-- Doc A E3: both tasks start with five calls, followed by one ex ante call. -/
theorem biased_forecast_two_task_A :
    reachMarginal 1 0 (1/5) 5=1024/15625 ∧
    reachMarginal 1 0 (4/5) 5=4/15625 ∧
    reachMarginal 1 0 (1/5) 5-reachMarginal 1 0 (4/5) 5=1020/15625 ∧
    (0:ℝ)<4/15625 := by norm_num [reachMarginal]

section Policies
variable {ι : Type*} [Fintype ι]

/-- Absence is preserved by every finite clonal generation. -/
theorem clonal_policy_support (x : Law ι) {f : ι→ℝ} (hf : ∀ i,0<f i) (t : ℕ) (i : ι) :
    SilentGene.clonalTrajectory x f t i=0 ↔ x.mass i=0 := by
  simp only [SilentGene.clonalTrajectory,div_eq_zero_iff,
    ne_of_gt (SilentGene.clonalNormalizer_pos x hf t),or_false,mul_eq_zero,
    pow_ne_zero _ (ne_of_gt (hf i)),or_false]

/-- Heritable policy ratios are computed on an actual Law1 clonal orbit. -/
theorem clonal_policy_ratio (x : Law ι) {f : ι→ℝ} (hf : ∀ i,0<f i)
    (good bad : ι) (hgood : 0<x.mass good) (t : ℕ) :
    SilentGene.clonalTrajectory x f t bad/SilentGene.clonalTrajectory x f t good=
      (x.mass bad/x.mass good)*(f bad/f good)^t := by
  unfold SilentGene.clonalTrajectory
  rw [div_pow]
  field_simp [ne_of_gt (SilentGene.clonalNormalizer_pos x hf t),ne_of_gt hgood,
    pow_ne_zero t (ne_of_gt (hf good))]

/-- Equality level set f=fmax. It is the argmax only when a separate
certificate proves every f i <= fmax. -/
def maximizers (f : ι→ℝ) (fmax : ℝ) : Finset ι := Finset.univ.filter (fun i=>f i=fmax)

/-- G8 accounting: a probability vector supported WITHIN the equality level
set f=fmax has mean fmax. Its optimal-payoff interpretation additionally
requires fmax to be certified as a true maximum. No equality of supports is
claimed. -/
theorem supported_within_maximizers_equal_payoff (x : Law ι) (f : ι→ℝ) (fmax : ℝ)
    (hsupport : ∀ i,0<x.mass i→i∈maximizers f fmax) : x.expect f=fmax := by
  have h (i : ι) : x.mass i*f i=x.mass i*fmax := by
    rcases lt_or_eq_of_le (x.nonneg i) with hi | hi
    · have he : f i=fmax := (Finset.mem_filter.mp (hsupport i hi)).2
      rw [he]
    · rw [← hi]; ring
  unfold Law.expect Law1.mean
  simp_rw [h]
  rw [← Finset.sum_mul,x.total,one_mul]

/-- No inherited correction when every offspring redraws its policy from
one fixed finite law, independently of the selected parent's policy. -/
theorem redrawn_policy_unchanged (selected nu : Law ι) :
    selected.bind (fun _=>nu)=nu := by
  apply SEKernel.Epistemic.law_eq_of_mass_eq
  funext i
  change (∑ j,selected.mass j*nu.mass i)=nu.mass i
  rw [← Finset.sum_mul,selected.total,one_mul]

/-- The reset law can still be mixed with retained elites. -/
theorem redrawn_with_elites (selected nu : Law ι) (elite : ℝ) (i : ι) :
    elite*selected.mass i+(1-elite)*(selected.bind (fun _=>nu)).mass i=
      elite*selected.mass i+(1-elite)*nu.mass i := by rw [redrawn_policy_unchanged]

end Policies

def forecastPolicyFitness (biased : Bool) : ℝ := if biased then 119/100 else 63/50

theorem biased_policy_fitness_pos (b : Bool) : 0<forecastPolicyFitness b := by
  cases b <;> norm_num [forecastPolicyFitness]

/-- The exact B E.5 factor 119/126 for stable, inherited forecast policies. -/
theorem biased_policy_ratio (x : Law Bool) (hgood : 0<x.mass false) (t : ℕ) :
    SilentGene.clonalTrajectory x forecastPolicyFitness t true/
      SilentGene.clonalTrajectory x forecastPolicyFitness t false=
      (x.mass true/x.mass false)*(119/126)^t := by
  rw [clonal_policy_ratio x biased_policy_fitness_pos false true hgood t]
  norm_num [forecastPolicyFitness]

section ReachLaw
variable {A : Type*} [Fintype A]

/-- An actual finite response law: reach selects the fixed alpha Bernoulli
response, absence selects beta. -/
def reachResponseLaw (pi : Law (Option A)) (a : A) (k : ℕ)
    (alpha beta : ℝ) (ha : 0 ≤ alpha) (ha' : alpha ≤ 1) (hb : 0 ≤ beta) (hb' : beta ≤ 1) : Law Bool :=
  (SEKernel.Epistemic.iidWordLaw pi k).bind (fun z=>
    if SEKernel.Epistemic.reaches z k a then MutationBaseline.bernoulli alpha ha ha'
      else MutationBaseline.bernoulli beta hb hb')

/-- The reach-only formula is connected to an actual IID experiment and a
normalized response kernel, including k=0 and endpoint success masses. -/
theorem actual_reach_payoff (pi : Law (Option A)) (a : A) (k : ℕ)
    (alpha beta : ℝ) (ha : 0 ≤ alpha) (ha' : alpha ≤ 1) (hb : 0 ≤ beta) (hb' : beta ≤ 1) :
    (reachResponseLaw pi a k alpha beta ha ha' hb hb').expect
      (fun b=>if b then (1:ℝ) else 0)=reachPayoff alpha beta (pi.mass (some a)) k := by
  classical
  unfold reachResponseLaw
  rw [Law.expect_bind]
  have hp (z : SEKernel.Epistemic.OrderedWord k A) :
      (if SEKernel.Epistemic.reaches z k a then MutationBaseline.bernoulli alpha ha ha'
        else MutationBaseline.bernoulli beta hb hb').expect (fun b=>if b then (1:ℝ) else 0)=
        beta+(alpha-beta)*(if SEKernel.Epistemic.reaches z k a then 1 else 0) := by
    split_ifs <;> simp [MutationBaseline.bernoulli_mean] <;> ring
  simp_rw [hp]
  rw [Law.expect_add,Law.expect_const,Law.expect_const_mul,Law.expect_indicator]
  change beta+(alpha-beta)*SEKernel.Epistemic.reachProbability pi k k a=_
  rw [SEKernel.Epistemic.reach_full_probability]
  unfold reachPayoff
  ring

end ReachLaw

/-- Per-slot forecast errors sum over the actual finite selected slots. -/
theorem marginal_forecast_error {ι : Type*} [Fintype ι] (d forecast : ι→ℝ)
    (A : Finset ι) (B : ℕ) (hB : A.card ≤ B) (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ i,|forecast i-d i| ≤ eps) :
    |(∑ i∈A,forecast i)-(∑ i∈A,d i)| ≤ B*eps := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i∈A,|forecast i-d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈A,eps := Finset.sum_le_sum (fun i _=>herr i)
    _ = A.card*eps := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hB) heps

section FiniteSelection
variable {ι : Type*} [Fintype ι]

/-- Doc B E.4 / Doc A E3 finite mass bound. M is the actual equality argmax;
the ratio bound is explicit and no analytic limit is imported. -/
theorem suboptimal_mass_bound (x : Law ι) {f : ι→ℝ} (hf : ∀ i,0<f i)
    (fmax rho : ℝ) (hmax : ∀ i,f i ≤ fmax) (hfmax : 0<fmax)
    (hrho : 0 ≤ rho) (hrho' : rho<1)
    (hgap : ∀ i∉maximizers f fmax,f i ≤ rho*fmax)
    (hstart : 0<∑ i∈maximizers f fmax,x.mass i) (t : ℕ) :
    (∑ i∈(maximizers f fmax)ᶜ,SilentGene.clonalTrajectory x f t i) ≤
      ((1-(∑ i∈maximizers f fmax,x.mass i))/(∑ i∈maximizers f fmax,x.mass i))*rho^t := by
  classical
  let M := maximizers f fmax
  let s0 := ∑ i∈M,x.mass i
  have hs0 : 0<s0 := hstart
  have hpart : (∑ i∈M,x.mass i)+(∑ i∈Mᶜ,x.mass i)=1 := by
    rw [Finset.sum_add_sum_compl]
    exact x.total
  have hcomp : (∑ i∈Mᶜ,x.mass i)=1-s0 := by dsimp [s0]; linarith
  have hnum : (∑ i∈Mᶜ,x.mass i*f i^t) ≤ (1-s0)*(rho*fmax)^t := by
    calc
      _ ≤ ∑ i∈Mᶜ,x.mass i*(rho*fmax)^t := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hf i).le (hgap i (Finset.mem_compl.mp hi)) t) (x.nonneg i)
      _ = _ := by rw [← Finset.sum_mul,hcomp]
  have hM : (∑ i∈M,x.mass i*f i^t)=s0*fmax^t := by
    have he (i : ι) (hi : i∈M) : f i=fmax := (Finset.mem_filter.mp hi).2
    calc
      _ = ∑ i∈M,x.mass i*fmax^t := Finset.sum_congr rfl (fun i hi=>by rw [he i hi])
      _ = _ := by rw [← Finset.sum_mul]
  have hden : s0*fmax^t ≤ SilentGene.clonalNormalizer x f t := by
    rw [← hM]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      (fun i _ _=>mul_nonneg (x.nonneg i) (pow_nonneg (hf i).le t))
  have hsmall : 0<s0*fmax^t := mul_pos hs0 (pow_pos hfmax t)
  have hn : 0 ≤ ∑ i∈Mᶜ,x.mass i*f i^t :=
    Finset.sum_nonneg (fun i _=>mul_nonneg (x.nonneg i) (pow_nonneg (hf i).le t))
  change (∑ i∈Mᶜ,x.mass i*f i^t/SilentGene.clonalNormalizer x f t) ≤ _
  rw [← Finset.sum_div]
  calc
    _ ≤ (∑ i∈Mᶜ,x.mass i*f i^t)/(s0*fmax^t) :=
      div_le_div_of_nonneg_left hn hsmall hden
    _ ≤ ((1-s0)*(rho*fmax)^t)/(s0*fmax^t) :=
      div_le_div_of_nonneg_right hnum hsmall.le
    _ = ((1-s0)/s0)*rho^t := by
      rw [mul_pow]
      field_simp [ne_of_gt hs0,pow_ne_zero t (ne_of_gt hfmax)]
      <;> ring

end FiniteSelection

section TaskCounts
variable {J : Type*} [Fintype J] {K : J→ℕ}

def taskSlots (A : Finset (CallSlot K)) (j : J) : Finset (Fin (K j)) :=
  Finset.univ.filter (fun r=>Sigma.mk j r∈A)

def taskCount (A : Finset (CallSlot K)) (j : J) : ℕ := (taskSlots A j).card

theorem initial_segment_mem_iff {n : ℕ} (S : Finset (Fin n))
    (hdown : ∀ r∈S,∀ q,q ≤ r→q∈S) (r : Fin n) : r∈S ↔ r.val<S.card := by
  classical
  constructor
  · intro hr
    have hsub : Finset.Iic r⊆S := fun q hq=>hdown r hr q (Finset.mem_Iic.mp hq)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro hr
    by_contra hn
    have hsub : S⊆Finset.Iio r := by
      intro q hq
      apply Finset.mem_Iio.mpr
      by_contra h
      exact hn (hdown q hq r (le_of_not_gt h))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

theorem prefix_mem_iff_taskCount (A : Finset (CallSlot K)) (hA : PrefixClosed A)
    (j : J) (r : Fin (K j)) : Sigma.mk j r∈A ↔ r.val<taskCount A j := by
  have hdown : ∀ r∈taskSlots A j,∀ q,q ≤ r→q∈taskSlots A j := by
    intro r hr q hqr
    simpa [taskSlots] using hA j r q hqr (by simpa [taskSlots] using hr)
  simpa [taskSlots,taskCount] using initial_segment_mem_iff (taskSlots A j) hdown r

theorem taskCount_le_cap (A : Finset (CallSlot K)) (j : J) : taskCount A j ≤ K j := by
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

theorem slot_sum_by_task (A : Finset (CallSlot K)) (d : CallSlot K→ℝ) :
    (∑ i∈A,d i)=∑ j,∑ r∈taskSlots A j,d ⟨j,r⟩ := by
  classical
  calc
    _ = ∑ i : CallSlot K,if i∈A then d i else 0 := by simp
    _ = ∑ j,∑ r : Fin (K j),if Sigma.mk j r∈A then d ⟨j,r⟩ else 0 := Fintype.sum_sigma _
    _ = _ := by simp only [taskSlots,Finset.sum_filter]

theorem taskCount_sum (A : Finset (CallSlot K)) : (∑ j,taskCount A j)=A.card := by
  have h := slot_sum_by_task A (fun _=>(1:ℝ))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at h
  exact_mod_cast h.symm

/-- Prefix task counts retain all allocation identity. -/
theorem prefix_allocation_ext (A C : Finset (CallSlot K))
    (hA : PrefixClosed A) (hC : PrefixClosed C) (hcounts : ∀ j,taskCount A j=taskCount C j) : A=C := by
  ext i
  rcases i with ⟨j,r⟩
  rw [prefix_mem_iff_taskCount A hA j,prefix_mem_iff_taskCount C hC j,hcounts j]

theorem sum_finite_prefix {n k : ℕ} (hk : k ≤ n) (g : ℕ→ℝ) :
    (∑ r : Fin n,if r.val<k then g r.val else 0)=∑ r∈Finset.range k,g r := by
  classical
  calc
    _ = ∑ r∈Finset.range n,if r<k then g r else 0 := Fin.sum_univ_eq_sum_range (fun r : ℕ=>if r<k then g r else 0) n
    _ = _ := by
      rw [← Finset.sum_filter]
      have he : (Finset.range n).filter (fun r=>r<k)=Finset.range k := by ext r; simp; omega
      rw [he]

/-- Lossless payoff bridge from a prefix-slot allocation to its actual task
call counts. This identifies the slot-expanded objective with Doc B (E3a). -/
theorem reach_allocation_objective (A : Finset (CallSlot K)) (hA : PrefixClosed A)
    (weight alpha beta p : J→ℝ) :
    (∑ j,weight j*reachPayoff (alpha j) (beta j) (p j) (taskCount A j))=
      (∑ j,weight j*beta j)+
        ∑ i∈A,weight i.1*reachMarginal (alpha i.1) (beta i.1) (p i.1) i.2.val := by
  rw [slot_sum_by_task]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : (taskSlots A j).sum (fun r=>weight j*reachMarginal (alpha j) (beta j) (p j) r.val)=
      ∑ r∈Finset.range (taskCount A j),weight j*reachMarginal (alpha j) (beta j) (p j) r := by
    simp only [taskSlots,Finset.sum_filter]
    simp_rw [prefix_mem_iff_taskCount A hA j]
    convert sum_finite_prefix (n:=K j) (k:=taskCount A j) (taskCount_le_cap A j)
      (fun r=>weight j*reachMarginal (alpha j) (beta j) (p j) r) using 1
  rw [he,reach_telescoping,mul_add,Finset.mul_sum]

/-- The constructed certificate specializes to the requested diminishing
reach marginal values, including zero weights and p=0 or p=1. -/
theorem exists_reach_certified_allocation (K : J→ℕ) (B : ℕ)
    (weight alpha beta p : J→ℝ) (hw : ∀ j,0 ≤ weight j)
    (hab : ∀ j,beta j ≤ alpha j) (hp : ∀ j,0 ≤ p j ∧ p j ≤ 1) :
    ∃ (A : FeasibleAllocation K B) (lambda : ℝ),
      A.val.card=min B (Fintype.card (CallSlot K)) ∧
      SlotCertificate (fun i=>weight i.1*reachMarginal (alpha i.1) (beta i.1) (p i.1) i.2.val)
        B A.val lambda := by
  apply exists_certified_allocation
  · intro i
    exact mul_nonneg (hw i.1) (reach_marginals_nonneg (hab i.1) (hp i.1).1 (hp i.1).2 i.2.val)
  · intro j r q hrq
    exact mul_le_mul_of_nonneg_left
      (reach_marginals_decreasing (hab j) (hp j).1 (hp j).2 hrq) (hw j)

theorem callSlot_card (K : J→ℕ) : Fintype.card (CallSlot K)=∑ j,K j := by
  simp [CallSlot,Fintype.card_sigma]

/-- The certificate is consumed at the actual sum of task reach payoffs. -/
theorem certified_reach_optimal (B : ℕ) (weight alpha beta p : J→ℝ)
    (A C : FeasibleAllocation K B) (lambda : ℝ)
    (h : SlotCertificate
      (fun i=>weight i.1*reachMarginal (alpha i.1) (beta i.1) (p i.1) i.2.val) B A.val lambda) :
    (∑ j,weight j*reachPayoff (alpha j) (beta j) (p j) (taskCount C.val j)) ≤
      ∑ j,weight j*reachPayoff (alpha j) (beta j) (p j) (taskCount A.val j) := by
  rw [reach_allocation_objective C.val C.property.1,
    reach_allocation_objective A.val A.property.1]
  exact certified_allocation_optimal K B (∑ j,weight j*beta j) _ A lambda h C

/-- Full reach-model existence and global optimality, with the specified
nonnegative task weights and bounded, ordered uptake probabilities. -/
theorem exists_optimal_reach_allocation (K : J→ℕ) (B : ℕ)
    (weight alpha beta p : J→ℝ) (hw : ∀ j,0 ≤ weight j)
    (hresponse : ∀ j,0 ≤ beta j ∧ beta j ≤ alpha j ∧ alpha j ≤ 1)
    (hp : ∀ j,0 ≤ p j ∧ p j ≤ 1) :
    ∃ (A : FeasibleAllocation K B) (lambda : ℝ),
      A.val.card=min B (∑ j,K j) ∧
      SlotCertificate (fun i=>weight i.1*reachMarginal (alpha i.1) (beta i.1) (p i.1) i.2.val)
        B A.val lambda ∧
      ∀ C : FeasibleAllocation K B,
        (∑ j,weight j*reachPayoff (alpha j) (beta j) (p j) (taskCount C.val j)) ≤
          ∑ j,weight j*reachPayoff (alpha j) (beta j) (p j) (taskCount A.val j) := by
  obtain ⟨A,lambda,hsize,hcert⟩ := exists_reach_certified_allocation K B weight alpha beta p hw
    (fun j=>(hresponse j).2.1) hp
  refine ⟨A,lambda,?_,hcert,fun C=>certified_reach_optimal B weight alpha beta p A C lambda hcert⟩
  simpa only [callSlot_card K] using hsize

end TaskCounts

section PostedVoteCounterexamples
open SEKernel.Epistemic

/-- A candidate at position zero is necessarily the first-appearance winner. -/
theorem plurality_at_zero {N : ℕ} (z : OrderedWord (N+1) Bool)
    (h : (0 : Fin (N+1))∈candidatePositions z) : plurality z=z 0 := by
  classical
  have hne : (candidatePositions z).Nonempty := ⟨0,h⟩
  unfold plurality
  rw [dif_pos hne]
  have hi := (candidatePositions z).min'_le 0 h
  have he : (candidatePositions z).min' hne=0 := le_antisymm hi (Fin.zero_le _)
  rw [he]

theorem binary_two_first (x y : Bool) : plurality ![some x,some y]=some x := by
  apply plurality_at_zero
  have hu : (Finset.univ : Finset (Fin 2))={0,1} := by ext i; fin_cases i <;> simp
  cases x <;> cases y <;>
    norm_num [candidatePositions,labelCount,hu,Fin.forall_fin_succ]
    <;> simp [Finset.filter_insert,Finset.filter_singleton]
    <;> norm_num [Fin.ext_iff]

/-- Strict readable count dominance suffices for the actual ordered winner. -/
theorem strict_readable_winner {N : ℕ} (z : OrderedWord N Bool) (a : Bool)
    (hpos : 0<labelCount z (some a))
    (hstrict : ∀ b : Bool,b≠a→labelCount z (some b)<labelCount z (some a)) :
    plurality z=some a := by
  classical
  cases he : plurality z with
  | none =>
    have hall := (plurality_eq_none_iff z).1 he
    obtain ⟨i,hi⟩ := (labelCount_pos_iff z (some a)).1 hpos
    have h := hall i
    simp [h] at hi
  | some b =>
    by_cases h : b=a
    · simpa [h] using he
    · have hd := plurality_dominates_readable z b he a
      have hs := hstrict b h
      omega

theorem some_label_count {N : ℕ} (z : Fin N→Bool) (b : Bool) :
    labelCount (fun i=>some (z i)) (some b)=wordCount z b := by
  unfold labelCount wordCount
  apply congrArg Finset.card
  ext i
  simp

theorem binary_three_majority (z : Fin 3→Bool) :
    correctVote (fun i=>some (z i)) true ↔ 2 ≤ wordCount z true := by
  classical
  have hc := some_label_count z true
  have ht : labelCount (fun i=>some (z i)) (some false)+wordCount z true=3 := by
    rw [some_label_count]
    simpa [Fintype.sum_bool,add_comm] using sum_wordCount z
  constructor
  · intro h
    have hd := plurality_dominates_readable (fun i=>some (z i)) true h false
    omega
  · intro h
    apply strict_readable_winner
    · omega
    · intro b hb
      cases b
      · omega
      · exact (hb rfl).elim

/-- IID binary readable law; abstention mass is explicitly zero. -/
def readableBernoulli (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : Law (Option Bool) :=
  (MutationBaseline.bernoulli p hp hp').map some

theorem readableBernoulli_no_abstention (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (readableBernoulli p hp hp').mass none=0 := by simp [readableBernoulli,Law.map]

/-- Actual three-voter probability via the already proved binomial count law. -/
theorem binary_vote_three_probability (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    voteAccuracy (readableBernoulli p hp hp') 3 true=3*p^2-2*p^3 := by
  classical
  have hmap := iid_map_event_probability (N:=3) (MutationBaseline.bernoulli p hp hp')
    some (fun w=>correctVote w true)
  have he : (fun z : Fin 3→Bool=>correctVote (fun i=>some (z i)) true)=
      (fun z=>2 ≤ wordCount z true) := by funext z; exact propext (binary_three_majority z)
  rw [he] at hmap
  change _=voteAccuracy (readableBernoulli p hp hp') 3 true at hmap
  rw [← hmap,iid_single_label_tail_probability]
  have hi : Finset.Icc 2 3={2,3} := by ext n; simp; omega
  rw [hi]
  norm_num [MutationBaseline.bernoulli]
  ring

/-- A proved first-position winner identity induces the actual IID accuracy. -/
theorem binary_vote_first_probability (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (N : ℕ) (hN : 0<N)
    (hfirst : ∀ z : Fin N→Bool,plurality (fun i=>some (z i))=some (z ⟨0,hN⟩)) :
    voteAccuracy (readableBernoulli p hp hp') N true=p := by
  classical
  have hmap := iid_map_event_probability (N:=N) (MutationBaseline.bernoulli p hp hp')
    some (fun w=>correctVote w true)
  have he : (fun z : Fin N→Bool=>correctVote (fun i=>some (z i)) true)=
      (fun z=>z ⟨0,hN⟩=true) := by
    funext z; apply propext; simp [correctVote,hfirst z]
  rw [he] at hmap
  change _=voteAccuracy (readableBernoulli p hp hp') N true at hmap
  rw [← hmap,← Law.expect_indicator]
  change (Law.pi (fun _ : Fin N=>MutationBaseline.bernoulli p hp hp')).expect
    (fun z=>if z ⟨0,hN⟩=true then (1:ℝ) else 0)=p
  have hc := Law.expect_pi_coord (fun _ : Fin N=>MutationBaseline.bernoulli p hp hp')
    (⟨0,hN⟩ : Fin N) (fun b=>if b=true then (1:ℝ) else 0)
  calc
    _ = (MutationBaseline.bernoulli p hp hp').expect (fun b=>if b=true then (1:ℝ) else 0) := hc
    _ = _ := by norm_num [Law.expect,Law1.mean,MutationBaseline.bernoulli,Fintype.sum_bool]

theorem binary_vote_one_probability (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    voteAccuracy (readableBernoulli p hp hp') 1 true=p := by
  apply binary_vote_first_probability p hp hp' 1 (by omega)
  intro z
  apply plurality_unique_readable
  · exact ⟨0,rfl⟩
  · intro i
    fin_cases i
    simp

theorem binary_vote_two_probability (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    voteAccuracy (readableBernoulli p hp hp') 2 true=p := by
  apply binary_vote_first_probability p hp hp' 2 (by omega)
  intro z
  have he : (fun i : Fin 2=>some (z i))=![some (z 0),some (z 1)] := by
    funext i; fin_cases i <;> rfl
  rw [he,binary_two_first]
  rfl

/-- G5: an actual IID word-law counterexample; abstention has mass ZERO. -/
theorem posted_vote_increasing_marginals :
    (readableBernoulli (3/5) (by norm_num) (by norm_num)).mass none=0 ∧
    voteAccuracy (readableBernoulli (3/5) (by norm_num) (by norm_num)) 1 true=3/5 ∧
    voteAccuracy (readableBernoulli (3/5) (by norm_num) (by norm_num)) 2 true=3/5 ∧
    voteAccuracy (readableBernoulli (3/5) (by norm_num) (by norm_num)) 3 true=81/125 ∧
    (0:ℝ)<81/125-3/5 := by
  rw [readableBernoulli_no_abstention,binary_vote_one_probability,
    binary_vote_two_probability,binary_vote_three_probability]
  norm_num

/-- A fixed two-voter benchmark with keep=0, post=1, none=0. -/
def fixedTwoRescuePayoff (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (k : ℕ) : ℝ :=
  (iidWordLaw (readableBernoulli p hp hp') 2).prob
    (fun z=>¬correctVote z true ∧ reaches z k true)

def fixedTwoRescueLaw (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (k : ℕ) : Law Bool :=
  (iidWordLaw (readableBernoulli p hp hp') 2).map
    (fun z=>if ¬correctVote z true ∧ reaches z k true then true else false)

theorem fixedTwoRescueLaw_correctness (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (k : ℕ) :
    (fixedTwoRescueLaw p hp hp' k).mass true=fixedTwoRescuePayoff p hp hp' k := by
  unfold fixedTwoRescueLaw fixedTwoRescuePayoff Law.map
  dsimp only
  apply congrArg ((iidWordLaw (readableBernoulli p hp hp') 2).prob)
  funext z
  apply propext
  by_cases h : ¬correctVote z true ∧ reaches z k true <;> simp [h]

theorem binary_prefix_two (z : Fin 2→Bool) (k : ℕ) :
    reaches (fun i=>some (z i)) k true ↔
      (0<k ∧ z 0=true) ∨ (1<k ∧ z 1=true) := by
  simp [reaches,Fin.exists_fin_succ]

theorem fixed_two_rescue_zero (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    fixedTwoRescuePayoff p hp hp' 0=0 := by simp [fixedTwoRescuePayoff,reaches_zero]

theorem fixed_two_rescue_one (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    fixedTwoRescuePayoff p hp hp' 1=0 := by
  have hmap := iid_map_event_probability (N:=2) (MutationBaseline.bernoulli p hp hp')
    some (fun w=>¬correctVote w true ∧ reaches w 1 true)
  change _=fixedTwoRescuePayoff p hp hp' 1 at hmap
  rw [← hmap]
  have he (z : Fin 2→Bool) : ¬correctVote (fun i=>some (z i)) true ∧
      reaches (fun i=>some (z i)) 1 true ↔ False := by
    have hw : plurality (fun i=>some (z i))=some (z 0) := by
      have he : (fun i : Fin 2=>some (z i))=![some (z 0),some (z 1)] := by
        funext i; fin_cases i <;> rfl
      rw [he,binary_two_first]
    simp [correctVote,hw,binary_prefix_two]
  simp only [he,Law.prob_false]

theorem fixed_two_rescue_two (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    fixedTwoRescuePayoff p hp hp' 2=p*(1-p) := by
  have hmap := iid_map_event_probability (N:=2) (MutationBaseline.bernoulli p hp hp')
    some (fun w=>¬correctVote w true ∧ reaches w 2 true)
  change _=fixedTwoRescuePayoff p hp hp' 2 at hmap
  rw [← hmap]
  have he : (fun z : Fin 2→Bool=>¬correctVote (fun i=>some (z i)) true ∧
      reaches (fun i=>some (z i)) 2 true)=
      (fun z=>∀ i,z i=(![false,true] : Fin 2→Bool) i) := by
    funext z
    apply propext
    have hw : plurality (fun i=>some (z i))=some (z 0) := by
      have he : (fun i : Fin 2=>some (z i))=![some (z 0),some (z 1)] := by
        funext i; fin_cases i <;> rfl
      rw [he,binary_two_first]
    cases h0 : z 0 <;> cases h1 : z 1 <;>
      simp [correctVote,hw,binary_prefix_two,Fin.forall_fin_succ,h0,h1]
  rw [he]
  change (Law.pi (fun _ : Fin 2=>MutationBaseline.bernoulli p hp hp')).prob _ = _
  have hpi := prob_pi_forall (fun _ : Fin 2=>MutationBaseline.bernoulli p hp hp')
    (fun i b=>b=(![false,true] : Fin 2→Bool) i)
  calc
    _ = ∏ i : Fin 2,(MutationBaseline.bernoulli p hp hp').prob
      (fun b=>b=(![false,true] : Fin 2→Bool) i) := hpi
    _ = _ := by
      norm_num [Fin.prod_univ_two,Law.prob,MutationBaseline.bernoulli,Fintype.sum_bool]
      ring

/-- G5's second actual payoff witness: the fixed common-pool benchmark is
unchanged, and revealing the second answer creates a positive marginal. -/
theorem fixed_benchmark_increasing_marginals (p : ℝ) (hp : 0<p) (hp' : p<1) :
    (readableBernoulli p hp.le hp'.le).mass none=0 ∧
    (fixedTwoRescueLaw p hp.le hp'.le 0).mass true=0 ∧
    (fixedTwoRescueLaw p hp.le hp'.le 1).mass true=0 ∧
    (fixedTwoRescueLaw p hp.le hp'.le 2).mass true=p*(1-p) ∧ 0<p*(1-p) := by
  rw [readableBernoulli_no_abstention,fixedTwoRescueLaw_correctness,
    fixedTwoRescueLaw_correctness,fixedTwoRescueLaw_correctness,
    fixed_two_rescue_zero,fixed_two_rescue_one,fixed_two_rescue_two]
  exact ⟨rfl,rfl,rfl,rfl,mul_pos hp (sub_pos.mpr hp')⟩

end PostedVoteCounterexamples

end
end SEKernel.SpawnAllocation
