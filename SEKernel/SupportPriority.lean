/-
SEKernel / SupportPriority.lean
The owner-aware support-priority collapse: the arbitrary-alternative
classification of clone-proof anonymous rules (referee program, round 3).

Setting.  `A` is any type of alternatives with decidable equality (finiteness
is NOT assumed).  A rule takes the multiset of votes (anonymity by domain) and
returns an alternative.  Two structural axioms:

* `SingletonFaithful` — a lone voter gets its vote: `F {a} = a`.
* `EntryLocal` — an entrant preserves the outcome or installs its own vote:
  `F (a ::ₘ R) ∈ {F R, a}` for nonempty `R`.  HONEST NAMING: for two
  alternatives this is exactly Boolean participation (`SpawnMonotone`); for
  three or more it is strictly stronger than participation — it forbids an
  entrant favoring `a` from moving the outcome from `b` to a third
  alternative `c`.  It is a locality axiom, not ordinary participation.

Main results (the five-way equivalence, split into consumable pieces):

* `oneCloneProof_iff_duplicateIdempotent` — immunity to one duplicate of an
  incumbent's own vote is exactly outcome-invariance under duplicates.
* `duplicateIdempotent_iff_supportFactors` — duplicate-invariance collapses
  ALL multiplicity: the rule factors through the support.  One-person-one-vote
  degenerates into one-present-alternative-one-bit.
* `support_priority_representation` — under one-clone-proofness the rule IS a
  fixed-priority selector: `F R` is the maximum of `supp R` under the
  extensional pairwise order `prio F a b ↔ a ≠ b ∧ F {a, b} = a`, which is
  total (`prio_total`), asymmetric (`prio_asymm`), and transitive
  (`prio_trans`; no-directed-triangle argument).
* `oneCloneProof_iff_strongOwnerFNP` — the surprise: immunity to ONE truthful
  clone already yields immunity to ANY finite block of arbitrary fake votes.
* `ownerAware_supportPriority_collapse` — the packaged TFAE.
* `neutrality_impossible` — no neutral rule exists once `A` has two
  alternatives.  STRENGTHENING of the referee's corollary: singleton
  faithfulness + entry locality alone already contradict neutrality;
  clone-proofness is not needed.
* `bool_ownerCloneProof_iff_and_or` — the Boolean classification: exactly two
  survivors, OR (`orRule`) and AND (`andRule` — the `unanimity` witness of
  `RosterSchema`, now revealed as one of precisely two Boolean survivors,
  with OR as its dual).

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace SupportPriority

variable {A : Type*} [DecidableEq A]

/-- Aggregation rules over anonymous rosters of alternatives. -/
abbrev Rule (A : Type*) := Multiset A → A

/-- A lone voter gets its vote. -/
def SingletonFaithful (F : Rule A) : Prop := ∀ a : A, F {a} = a

/-- An entrant preserves the outcome or installs its own vote (see the module
docstring: stronger than participation once `3 ≤ |A|`). -/
def EntryLocal (F : Rule A) : Prop :=
  ∀ (R : Multiset A) (a : A), R ≠ 0 → F (a ::ₘ R) = F R ∨ F (a ::ₘ R) = a

/-- An incumbent cannot install its own alternative by minting one duplicate
of its vote. -/
def OneCloneProof (F : Rule A) : Prop :=
  ∀ (R : Multiset A) (a : A), a ∈ R → F R ≠ a → F (a ::ₘ R) ≠ a

/-- Adding a duplicate of a present vote never changes the outcome. -/
def DuplicateIdempotent (F : Rule A) : Prop :=
  ∀ (R : Multiset A) (a : A), a ∈ R → F (a ::ₘ R) = F R

/-- The rule reads only the support: equal supports, equal outcomes. -/
def SupportFactors (F : Rule A) : Prop :=
  ∀ R S : Multiset A, R.toFinset = S.toFinset → F R = F S

/-- No finite block of arbitrary fake votes can turn a losing incumbent
alternative into the winner. -/
def StrongOwnerFNP (F : Rule A) : Prop :=
  ∀ (R T : Multiset A) (a : A), a ∈ R → F R ≠ a → F (R + T) ≠ a

/-- The priority order extracted from pairwise contests (extensional form,
per the referee's Lean advice: a canonical relation, not a bundled order). -/
def prio (F : Rule A) (a b : A) : Prop := a ≠ b ∧ F (a ::ₘ {b}) = a

/-- `m` is the priority maximum of the finite set `s`. -/
def IsPrioMax (F : Rule A) (s : Finset A) (m : A) : Prop :=
  m ∈ s ∧ ∀ b ∈ s, b ≠ m → prio F m b

/-- Neutrality: the rule commutes with every relabeling of alternatives. -/
def Neutral (F : Rule A) : Prop :=
  ∀ (σ : Equiv.Perm A) (R : Multiset A), F (R.map σ) = σ (F R)

/-! ## Step 1: one-clone-proofness ⟺ duplicate idempotence -/

theorem oneCloneProof_iff_duplicateIdempotent (F : Rule A)
    (hEL : EntryLocal F) : OneCloneProof F ↔ DuplicateIdempotent F := by
  constructor
  · intro h1 R a ha
    have hne : R ≠ 0 := by
      rintro rfl
      exact Multiset.notMem_zero a ha
    by_cases hFa : F R = a
    · rcases hEL R a hne with h | h
      · exact h
      · rw [h, hFa]
    · rcases hEL R a hne with h | h
      · exact h
      · exact absurd h (h1 R a ha hFa)
  · intro hDI R a ha hFa
    rw [hDI R a ha]
    exact hFa

/-! ## Step 2: duplicate idempotence ⟺ support factorization -/

theorem eq_dedup_of_duplicateIdempotent (F : Rule A)
    (hDI : DuplicateIdempotent F) (R : Multiset A) : F R = F R.dedup := by
  obtain ⟨n, hn⟩ : ∃ n, R.card = n := ⟨R.card, rfl⟩
  induction n generalizing R with
  | zero =>
      rw [Multiset.card_eq_zero.mp hn, Multiset.dedup_zero]
  | succ n ih =>
      by_cases hnd : R.Nodup
      · rw [Multiset.dedup_eq_self.mpr hnd]
      · obtain ⟨a, ha2⟩ : ∃ a, 2 ≤ R.count a := by
          by_contra hc
          push_neg at hc
          exact hnd (Multiset.nodup_iff_count_le_one.mpr fun a => by
            have := hc a; omega)
        have haR : a ∈ R := by
          rw [← Multiset.count_pos]; omega
        have haE : a ∈ R.erase a := by
          rw [← Multiset.count_pos, Multiset.count_erase_self]; omega
        have hcons : a ::ₘ R.erase a = R := Multiset.cons_erase haR
        have hcard : (R.erase a).card = n := by
          have h := Multiset.card_erase_of_mem haR
          rw [hn] at h
          simpa using h
        calc F R = F (a ::ₘ R.erase a) := by rw [hcons]
          _ = F (R.erase a) := hDI (R.erase a) a haE
          _ = F (R.erase a).dedup := ih (R.erase a) hcard
          _ = F (a ::ₘ R.erase a).dedup := by
              rw [Multiset.dedup_cons_of_mem haE]
          _ = F R.dedup := by rw [hcons]

theorem duplicateIdempotent_iff_supportFactors (F : Rule A) :
    DuplicateIdempotent F ↔ SupportFactors F := by
  constructor
  · intro hDI R S hRS
    have hd : R.dedup = S.dedup := by
      have h := congrArg Finset.val hRS
      simpa [Multiset.toFinset_val] using h
    rw [eq_dedup_of_duplicateIdempotent F hDI R, hd,
        ← eq_dedup_of_duplicateIdempotent F hDI S]
  · intro hSQ R a ha
    apply hSQ
    rw [Multiset.toFinset_cons]
    exact Finset.insert_eq_self.mpr (Multiset.mem_toFinset.mpr ha)

/-! ## Step 3: the finite-set choice layer -/

theorem pair_val {a b : A} (hab : a ≠ b) :
    ({a, b} : Finset A).val = a ::ₘ {b} := by
  rw [Finset.insert_val_of_notMem (by simp [hab]), Finset.singleton_val]

/-- The single-valued adjunction property: adjoining `a` either preserves the
choice or selects `a`. -/
theorem choice_insert (F : Rule A) (hEL : EntryLocal F)
    (S : Finset A) (hS : S.Nonempty) (a : A) :
    F (insert a S).val = F S.val ∨ F (insert a S).val = a := by
  by_cases haS : a ∈ S
  · left
    rw [Finset.insert_eq_self.mpr haS]
  · have hne : S.val ≠ 0 := fun h => hS.ne_empty (Finset.val_eq_zero.mp h)
    rw [Finset.insert_val_of_notMem haS]
    exact hEL S.val a hne

/-- The choice lands in the set. -/
theorem choice_mem (F : Rule A) (hSF : SingletonFaithful F)
    (hEL : EntryLocal F) (S : Finset A) : S.Nonempty → F S.val ∈ S := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS
    obtain ⟨x, hx⟩ := hS
    by_cases hxe : S.erase x = ∅
    · have hSx : S = {x} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hx, fun y hy => ?_⟩
        by_contra hyx
        have hbe : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
        rw [hxe] at hbe
        exact Finset.notMem_empty y hbe
      rw [hSx, Finset.singleton_val, hSF x]
      exact Finset.mem_singleton_self x
    · have hne : (S.erase x).Nonempty := Finset.nonempty_iff_ne_empty.mpr hxe
      have hmem := ih _ (Finset.erase_ssubset hx) hne
      rcases choice_insert F hEL (S.erase x) hne x with h | h
      · rw [Finset.insert_erase hx] at h
        rw [h]
        exact Finset.mem_of_mem_erase hmem
      · rw [Finset.insert_erase hx] at h
        rw [h]
        exact hx

/-! ## Step 4: the priority order — total, asymmetric, transitive -/

theorem prio_total (F : Rule A) (hSF : SingletonFaithful F)
    (hEL : EntryLocal F) {a b : A} (hab : a ≠ b) :
    prio F a b ∨ prio F b a := by
  have hpair : F (a ::ₘ {b}) = F {b} ∨ F (a ::ₘ {b}) = a := hEL {b} a (by simp)
  rw [hSF b] at hpair
  rcases hpair with h | h
  · right
    refine ⟨hab.symm, ?_⟩
    have hcomm : (b ::ₘ ({a} : Multiset A)) = (a ::ₘ ({b} : Multiset A)) :=
      Multiset.cons_swap b a 0
    rw [hcomm]
    exact h
  · left
    exact ⟨hab, h⟩

theorem prio_asymm (F : Rule A) {a b : A} (h : prio F a b) : ¬ prio F b a := by
  rintro ⟨hba, hFba⟩
  obtain ⟨hab, hFab⟩ := h
  have hcomm : (b ::ₘ ({a} : Multiset A)) = (a ::ₘ ({b} : Multiset A)) :=
    Multiset.cons_swap b a 0
  rw [hcomm, hFab] at hFba
  exact hab hFba

theorem prio_trans (F : Rule A) (hSF : SingletonFaithful F)
    (hEL : EntryLocal F) {a b c : A}
    (hab : prio F a b) (hbc : prio F b c) : prio F a c := by
  obtain ⟨hab', hFab⟩ := hab
  obtain ⟨hbc', hFbc⟩ := hbc
  have hac' : a ≠ c := by
    rintro rfl
    exact prio_asymm F ⟨hab', hFab⟩ ⟨hbc', hFbc⟩
  rcases prio_total F hSF hEL hac' with h | h
  · exact h
  · exfalso
    obtain ⟨hca', hFca⟩ := h
    -- three decompositions of the triangle {a, b, c}
    have e1 : ({a, b, c} : Finset A) = insert c ({a, b} : Finset A) := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have e2 : ({a, b, c} : Finset A) = insert a ({b, c} : Finset A) := rfl
    have e3 : ({a, b, c} : Finset A) = insert b ({c, a} : Finset A) := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have d1 := choice_insert F hEL ({a, b} : Finset A) ⟨a, by simp⟩ c
    rw [← e1, pair_val hab', hFab] at d1
    have d2 := choice_insert F hEL ({b, c} : Finset A) ⟨b, by simp⟩ a
    rw [← e2, pair_val hbc', hFbc] at d2
    have d3 := choice_insert F hEL ({c, a} : Finset A) ⟨c, by simp⟩ b
    rw [← e3, pair_val hca', hFca] at d3
    rcases d1 with hx | hx
    · rcases d3 with hy | hy
      · exact hac' (hx.symm.trans hy)
      · exact hab' (hx.symm.trans hy)
    · rcases d2 with hy | hy
      · exact hbc' (hy.symm.trans hx)
      · exact hca' (hx.symm.trans hy)

theorem prio_max_unique (F : Rule A) {S : Finset A} {m₁ m₂ : A}
    (h1 : IsPrioMax F S m₁) (h2 : IsPrioMax F S m₂) : m₁ = m₂ := by
  by_contra hne
  exact prio_asymm F (h2.2 m₁ h1.1 hne) (h1.2 m₂ h2.1 (Ne.symm hne))

/-! ## Step 5: existence of the maximum, and the choice selects it -/

theorem exists_prio_max (F : Rule A) (hSF : SingletonFaithful F)
    (hEL : EntryLocal F) (S : Finset A) :
    S.Nonempty → ∃ m, IsPrioMax F S m := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS
    obtain ⟨x, hx⟩ := hS
    by_cases hxe : S.erase x = ∅
    · refine ⟨x, hx, fun b hb hbx => ?_⟩
      exfalso
      have hbe : b ∈ S.erase x := Finset.mem_erase.mpr ⟨hbx, hb⟩
      rw [hxe] at hbe
      exact Finset.notMem_empty b hbe
    · have hne : (S.erase x).Nonempty := Finset.nonempty_iff_ne_empty.mpr hxe
      obtain ⟨m, hm, hdom⟩ := ih _ (Finset.erase_ssubset hx) hne
      have hmS : m ∈ S := Finset.mem_of_mem_erase hm
      have hmx : m ≠ x := (Finset.mem_erase.mp hm).1
      rcases prio_total F hSF hEL hmx.symm with hxm | hmx'
      · refine ⟨x, hx, fun b hb hbx => ?_⟩
        by_cases hbm : b = m
        · rw [hbm]; exact hxm
        · exact prio_trans F hSF hEL hxm
            (hdom b (Finset.mem_erase.mpr ⟨hbx, hb⟩) hbm)
      · refine ⟨m, hmS, fun b hb hbm => ?_⟩
        by_cases hbx : b = x
        · rw [hbx]; exact hmx'
        · exact hdom b (Finset.mem_erase.mpr ⟨hbx, hb⟩) hbm

theorem choice_eq_prio_max (F : Rule A) (hSF : SingletonFaithful F)
    (hEL : EntryLocal F) (S : Finset A) :
    ∀ m, IsPrioMax F S m → F S.val = m := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rintro m ⟨hm, hdom⟩
    by_cases hc1 : S.card = 1
    · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hc1
      subst hy
      have hmy : m = y := Finset.mem_singleton.mp hm
      subst hmy
      rw [Finset.singleton_val]
      exact hSF m
    · by_cases hc2 : S.card = 2
      · obtain ⟨x, y, hxy, hSxy⟩ := Finset.card_eq_two.mp hc2
        subst hSxy
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · have hprio := hdom y (by simp) (Ne.symm hxy)
          rw [pair_val hxy]
          exact hprio.2
        · have hmy : m = y := Finset.mem_singleton.mp hm'
          subst hmy
          have hprio := hdom x (by simp) hxy
          rw [Finset.pair_comm x m, pair_val (Ne.symm hxy)]
          exact hprio.2
      · have hc3 : 3 ≤ S.card := by
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨m, hm⟩
          omega
        have herase : 1 < (S.erase m).card := by
          rw [Finset.card_erase_of_mem hm]
          omega
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp herase
        have hxS : x ∈ S := Finset.mem_of_mem_erase hx
        have hxm : x ≠ m := (Finset.mem_erase.mp hx).1
        have hyS : y ∈ S := Finset.mem_of_mem_erase hy
        have hym : y ≠ m := (Finset.mem_erase.mp hy).1
        have hmax_ex : IsPrioMax F (S.erase x) m :=
          ⟨Finset.mem_erase.mpr ⟨Ne.symm hxm, hm⟩,
           fun b hb hbm => hdom b (Finset.mem_of_mem_erase hb) hbm⟩
        have hmax_ey : IsPrioMax F (S.erase y) m :=
          ⟨Finset.mem_erase.mpr ⟨Ne.symm hym, hm⟩,
           fun b hb hbm => hdom b (Finset.mem_of_mem_erase hb) hbm⟩
        have hchx := ih _ (Finset.erase_ssubset hxS) m hmax_ex
        have hchy := ih _ (Finset.erase_ssubset hyS) m hmax_ey
        have hins_x := choice_insert F hEL (S.erase x) ⟨m, hmax_ex.1⟩ x
        have hins_y := choice_insert F hEL (S.erase y) ⟨m, hmax_ey.1⟩ y
        rw [Finset.insert_erase hxS, hchx] at hins_x
        rw [Finset.insert_erase hyS, hchy] at hins_y
        rcases hins_x with h | h
        · exact h
        · rcases hins_y with h' | h'
          · exact h'
          · exact absurd (h.symm.trans h') hxy

/-! ## The representation and the strong-FNP upgrade -/

/-- **Support-priority representation.**  Under singleton faithfulness, entry
locality, and one-clone-proofness, the outcome is the priority maximum of the
support: multiplicity is institutionally inert, and the rule is a fixed
alternative-priority selector. -/
theorem support_priority_representation (F : Rule A)
    (hSF : SingletonFaithful F) (hEL : EntryLocal F) (h1 : OneCloneProof F)
    (R : Multiset A) (hR : R ≠ 0) : IsPrioMax F R.toFinset (F R) := by
  have hSQ : SupportFactors F :=
    (duplicateIdempotent_iff_supportFactors F).mp
      ((oneCloneProof_iff_duplicateIdempotent F hEL).mp h1)
  have hval : F R = F R.toFinset.val := hSQ R R.toFinset.val (by simp)
  have hne : R.toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    simpa [Multiset.toFinset_eq_empty] using hR
  obtain ⟨m, hmax⟩ := exists_prio_max F hSF hEL R.toFinset hne
  rw [hval, choice_eq_prio_max F hSF hEL R.toFinset m hmax]
  exact hmax

/-- **One truthful clone ⟺ arbitrary Sybil armies.**  Immunity to a single
duplicate of the incumbent's own vote already yields immunity to every finite
block of arbitrary (heterogeneous) fake votes. -/
theorem oneCloneProof_iff_strongOwnerFNP (F : Rule A)
    (hSF : SingletonFaithful F) (hEL : EntryLocal F) :
    OneCloneProof F ↔ StrongOwnerFNP F := by
  constructor
  · intro h1 R T a haR hFa hcon
    have hR : R ≠ 0 := by
      rintro rfl
      exact Multiset.notMem_zero a haR
    have hRT : R + T ≠ 0 := fun h =>
      hR (Multiset.le_zero.mp (h ▸ Multiset.le_add_right R T))
    have hrepRT := support_priority_representation F hSF hEL h1 (R + T) hRT
    rw [hcon] at hrepRT
    have hrepR := support_priority_representation F hSF hEL h1 R hR
    have hmaxR : IsPrioMax F R.toFinset a := by
      refine ⟨Multiset.mem_toFinset.mpr haR, fun b hb hba => ?_⟩
      refine hrepRT.2 b ?_ hba
      rw [Multiset.toFinset_add]
      exact Finset.mem_union_left _ hb
    exact hFa (prio_max_unique F hrepR hmaxR)
  · intro hS R a haR hFa hcon
    have h := hS R {a} a haR hFa
    rw [show R + {a} = a ::ₘ R by
      rw [Multiset.add_comm, Multiset.singleton_add]] at h
    exact h hcon

/-- **The owner-aware support-priority collapse** (packaged equivalence). -/
theorem ownerAware_supportPriority_collapse (F : Rule A)
    (hSF : SingletonFaithful F) (hEL : EntryLocal F) :
    List.TFAE [OneCloneProof F, DuplicateIdempotent F, SupportFactors F,
      StrongOwnerFNP F] := by
  tfae_have 1 ↔ 2 := oneCloneProof_iff_duplicateIdempotent F hEL
  tfae_have 2 ↔ 3 := duplicateIdempotent_iff_supportFactors F
  tfae_have 1 ↔ 4 := oneCloneProof_iff_strongOwnerFNP F hSF hEL
  tfae_finish

/-! ## Neutrality is impossible -/

/-- **No neutral rule exists** once there are two alternatives — and this
needs only singleton faithfulness and entry locality (a strengthening of the
referee's corollary, which assumed clone-proofness as well). -/
theorem neutrality_impossible (F : Rule A) (hSF : SingletonFaithful F)
    (hEL : EntryLocal F) (hN : Neutral F) {a b : A} (hab : a ≠ b) : False := by
  have hpair : F (a ::ₘ {b}) = F {b} ∨ F (a ::ₘ {b}) = a := hEL {b} a (by simp)
  rw [hSF b] at hpair
  have hmap : (a ::ₘ ({b} : Multiset A)).map (Equiv.swap a b) = a ::ₘ {b} := by
    rw [Multiset.map_cons, Multiset.map_singleton, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
    exact Multiset.cons_swap b a 0
  have hswap := hN (Equiv.swap a b) (a ::ₘ {b})
  rw [hmap] at hswap
  rcases hpair with h | h <;> rw [h] at hswap
  · rw [Equiv.swap_apply_right] at hswap
    exact hab hswap.symm
  · rw [Equiv.swap_apply_left] at hswap
    exact hab hswap

/-! ## The Boolean classification: AND and OR are the only survivors -/

/-- The OR rule: `true` iff some `true` vote is present. -/
def orRule : Rule Bool := fun R => decide (true ∈ R)

/-- The AND (unanimity) rule: `true` iff no `false` vote is present — the
`unanimity` witness of `RosterSchema`, revealed as one of exactly two Boolean
survivors. -/
def andRule : Rule Bool := fun R => decide (false ∉ R)

theorem mem_cons_self_iff {a x : A} {R : Multiset A} (haR : a ∈ R) :
    x ∈ a ::ₘ R ↔ x ∈ R := by
  rw [Multiset.mem_cons]
  constructor
  · rintro (rfl | h)
    · exact haR
    · exact h
  · exact Or.inr

/-- **Boolean classification.**  Over `Bool`, under singleton faithfulness and
entry locality, one-clone-proofness holds exactly for the two fixed-priority
rules: OR (priority `true ≻ false`) and AND (priority `false ≻ true`). -/
theorem bool_ownerCloneProof_iff_and_or (F : Rule Bool)
    (hSF : SingletonFaithful F) (hEL : EntryLocal F) :
    OneCloneProof F ↔
      ((∀ R : Multiset Bool, R ≠ 0 → F R = orRule R) ∨
       (∀ R : Multiset Bool, R ≠ 0 → F R = andRule R)) := by
  constructor
  · intro h1
    rcases prio_total F hSF hEL (show (true : Bool) ≠ false by decide)
      with hTF | hFT
    · left
      intro R hR
      have hrep := support_priority_representation F hSF hEL h1 R hR
      by_cases ht : true ∈ R
      · have hmax : IsPrioMax F R.toFinset true := by
          refine ⟨Multiset.mem_toFinset.mpr ht, fun b hb hbt => ?_⟩
          have hb' : b = false := by
            cases b
            · rfl
            · exact absurd rfl hbt
          rw [hb']
          exact hTF
        have hFR : F R = true := prio_max_unique F hrep hmax
        simp [orRule, hFR, ht]
      · have hmem : F R ∈ R := Multiset.mem_toFinset.mp hrep.1
        have hFR : F R = false := by
          cases hcase : F R
          · rfl
          · rw [hcase] at hmem
            exact absurd hmem ht
        simp [orRule, hFR, ht]
    · right
      intro R hR
      have hrep := support_priority_representation F hSF hEL h1 R hR
      by_cases hf : false ∈ R
      · have hmax : IsPrioMax F R.toFinset false := by
          refine ⟨Multiset.mem_toFinset.mpr hf, fun b hb hbf => ?_⟩
          have hb' : b = true := by
            cases b
            · exact absurd rfl hbf
            · rfl
          rw [hb']
          exact hFT
        have hFR : F R = false := prio_max_unique F hrep hmax
        simp [andRule, hFR, hf]
      · have hmem : F R ∈ R := Multiset.mem_toFinset.mp hrep.1
        have hFR : F R = true := by
          cases hcase : F R
          · rw [hcase] at hmem
            exact absurd hmem hf
          · rfl
        simp [andRule, hFR, hf]
  · rintro (hOR | hAND) R a haR hFa hcon
    · have hR : R ≠ 0 := by
        rintro rfl
        exact Multiset.notMem_zero a haR
      have hiff : (true ∈ a ::ₘ R) ↔ (true ∈ R) := mem_cons_self_iff haR
      have hstep : F (a ::ₘ R) = F R := by
        rw [hOR R hR, hOR (a ::ₘ R) (Multiset.cons_ne_zero)]
        simp only [orRule]
        exact decide_eq_decide.mpr hiff
      rw [hstep] at hcon
      exact hFa hcon
    · have hR : R ≠ 0 := by
        rintro rfl
        exact Multiset.notMem_zero a haR
      have hiff : (false ∈ a ::ₘ R) ↔ (false ∈ R) := mem_cons_self_iff haR
      have hstep : F (a ::ₘ R) = F R := by
        rw [hAND R hR, hAND (a ::ₘ R) (Multiset.cons_ne_zero)]
        simp only [andRule]
        exact decide_eq_decide.mpr (not_congr hiff)
      rw [hstep] at hcon
      exact hFa hcon

end SupportPriority
end SEKernel
