/-
SEKernel / RosterSchema.lean
The Roster impossibility, general form: any anonymous, spawn-monotone,
non-constant binary rule over an endogenous electorate is spawn-manipulable.

Setting.  A binary social rule takes the multiset of votes (so anonymity over
identities is built into the domain) and returns an outcome in `Bool`; each
identity's vote is the outcome it favors.  Two axioms:

* `SpawnMonotone` — minting one identity voting `v` either leaves the outcome
  unchanged or moves it to `v` (the endogenous-population form of May's
  positive responsiveness: an added supporter never moves the outcome away
  from its own side).
* `Nonconstant` — the rule responds to something.

`roster_impossibility`: every such rule has a profile at which minting a
single identity flips the outcome to the minted vote — spawn-manipulation.
The proof walks any two profiles with different outcomes toward each other one
spawn at a time (`exists_flip`); somewhere a single mint flips the outcome,
and monotonicity forces the flip to land on the minted side.

This is the impossibility half of the Roster Schema at full generality (any
electorate size, any rule).  The possibility half is
`StakeMedian.measure_rule_split_invariant`: rules that read only the stake
measure are immune, because a stake split — unlike a head-count mint — leaves
the measure unchanged.  Head-counting is exactly the design choice that makes
the manufactured identity a fresh full unit.

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace RosterSchema

/-- A binary social rule over anonymous electorates: the domain is the
multiset of votes, each identity's vote being the outcome it favors. -/
abbrev Rule := Multiset Bool → Bool

/-- Minting one identity voting `v` either leaves the outcome unchanged or
moves it to `v`. -/
def SpawnMonotone (F : Rule) : Prop :=
  ∀ (R : Multiset Bool) (v : Bool), F (v ::ₘ R) = F R ∨ F (v ::ₘ R) = v

/-- The rule is not constant. -/
def Nonconstant (F : Rule) : Prop := ∃ P Q, F P ≠ F Q

/-- If a rule changes value between `P` and `P + Q`, it flips at some single
spawn step along the chain from `P` to `P + Q`. -/
theorem exists_flip (F : Rule) (P Q : Multiset Bool) :
    F P ≠ F (P + Q) →
    ∃ (R : Multiset Bool) (v : Bool), F R ≠ F (v ::ₘ R) := by
  induction Q using Multiset.induction_on generalizing P with
  | empty =>
      intro h
      simp at h
  | cons v Q' ih =>
      intro h
      rw [Multiset.add_cons] at h
      by_cases hstep : F (P + Q') = F (v ::ₘ (P + Q'))
      · rw [← hstep] at h
        exact ih P h
      · exact ⟨P + Q', v, hstep⟩

/-- **The Roster impossibility (general form).**  Any anonymous,
spawn-monotone, non-constant binary rule is spawn-manipulable: at some
profile, minting one identity with vote `v` changes the outcome to `v`. -/
theorem roster_impossibility (F : Rule) (hmono : SpawnMonotone F)
    (hnc : Nonconstant F) :
    ∃ (R : Multiset Bool) (v : Bool), F R ≠ v ∧ F (v ::ₘ R) = v := by
  obtain ⟨P, Q, hPQ⟩ := hnc
  have key : ∃ (R : Multiset Bool) (v : Bool), F R ≠ F (v ::ₘ R) := by
    by_cases h : F P = F (P + Q)
    · apply exists_flip F Q P
      rw [add_comm Q P, ← h]
      exact hPQ.symm
    · exact exists_flip F P Q h
  obtain ⟨R, v, hflip⟩ := key
  rcases hmono R v with heq | hv
  · exact absurd heq (Ne.symm hflip)
  · exact ⟨R, v, fun hRv => hflip (hRv.trans hv.symm), hv⟩

/-- Reading of the conclusion: the minted identity favors the new outcome, so
the spawn is strictly outcome-improving for the lineage that mints it — the
manipulation is always in the manipulator's favor. -/
theorem roster_manipulation_favors_spawner (F : Rule) (hmono : SpawnMonotone F)
    (hnc : Nonconstant F) :
    ∃ (R : Multiset Bool) (v : Bool), F R ≠ v ∧ F (v ::ₘ R) = v :=
  roster_impossibility F hmono hnc

/-! ## The owner-aware theorem (referee-hardened form)

`roster_impossibility` above is honestly an *entrant-pivotality* result: its
witness need not contain an incumbent of the minted type, so at boundary
profiles it exhibits entry responsiveness, not identity cloning.  The
unanimity rule below is the exact counterexample to the naive strengthening
(demanding `v ∈ R` under mere global non-constancy).  The correct hypothesis
is non-constancy on MIXED (contested) rosters, and with it the theorem
becomes a sharp dichotomy: an incumbent on a contested roster can profit by
minting one duplicate of its own vote **iff** the rule responds at all on the
contested region. -/

/-- Both vote types are present: a contested electorate. -/
def Mixed (R : Multiset Bool) : Prop := false ∈ R ∧ true ∈ R

theorem Mixed.mem {R : Multiset Bool} (h : Mixed R) (v : Bool) : v ∈ R := by
  cases v
  · exact h.1
  · exact h.2

theorem Mixed.mono {P R : Multiset Bool} (h : Mixed P) (hle : P ≤ R) :
    Mixed R :=
  ⟨Multiset.mem_of_le hle h.1, Multiset.mem_of_le hle h.2⟩

/-- Strengthened flip lemma: the flip roster contains the starting profile. -/
theorem exists_flip_le (F : Rule) (P Q : Multiset Bool) :
    F P ≠ F (P + Q) →
    ∃ (R : Multiset Bool) (v : Bool), P ≤ R ∧ F R ≠ F (v ::ₘ R) := by
  induction Q using Multiset.induction_on generalizing P with
  | empty =>
      intro h
      simp at h
  | cons v Q' ih =>
      intro h
      rw [Multiset.add_cons] at h
      by_cases hstep : F (P + Q') = F (v ::ₘ (P + Q'))
      · rw [← hstep] at h
        exact ih P h
      · exact ⟨P + Q', v, Multiset.le_add_right _ _, hstep⟩

/-- **Owner-aware Roster theorem, impossibility direction.**  If a
spawn-monotone rule distinguishes two contested rosters, then some INCUMBENT
on a contested roster manipulates by minting one duplicate of its own vote:
`v ∈ R`, `F R ≠ v`, and `F (v ::ₘ R) = v`.  (Mixedness of the flip roster is
what turns the entrant of `roster_impossibility` into an incumbent: on a
contested roster every vote type already has an owner.) -/
theorem mixed_roster_manipulable (F : Rule) (hmono : SpawnMonotone F)
    (P Q : Multiset Bool) (hP : Mixed P) (hQ : Mixed Q) (hPQ : F P ≠ F Q) :
    ∃ (R : Multiset Bool) (v : Bool),
      Mixed R ∧ v ∈ R ∧ F R ≠ v ∧ F (v ::ₘ R) = v := by
  have key : ∃ (R : Multiset Bool) (v : Bool),
      Mixed R ∧ F R ≠ F (v ::ₘ R) := by
    by_cases h : F P = F (P + Q)
    · have hQU : F Q ≠ F (Q + P) := by
        rw [add_comm Q P, ← h]
        exact hPQ.symm
      obtain ⟨R, v, hle, hflip⟩ := exists_flip_le F Q P hQU
      exact ⟨R, v, hQ.mono hle, hflip⟩
    · obtain ⟨R, v, hle, hflip⟩ := exists_flip_le F P Q h
      exact ⟨R, v, hP.mono hle, hflip⟩
  obtain ⟨R, v, hmix, hflip⟩ := key
  rcases hmono R v with heq | hv
  · exact absurd heq (Ne.symm hflip)
  · exact ⟨R, v, hmix, hmix.mem v,
      fun hRv => hflip (hRv.trans hv.symm), hv⟩

/-- Possibility direction: a rule constant on contested rosters allows no
incumbent clone manipulation there. -/
theorem cloneProof_of_mixed_constant (F : Rule)
    (hconst : ∀ P Q, Mixed P → Mixed Q → F P = F Q) :
    ∀ R v, Mixed R → v ∈ R → ¬(F R ≠ v ∧ F (v ::ₘ R) = v) := by
  rintro R v hmix _ ⟨hne, hflip⟩
  have hmix' : Mixed (v ::ₘ R) :=
    ⟨Multiset.mem_cons_of_mem hmix.1, Multiset.mem_cons_of_mem hmix.2⟩
  exact hne ((hconst R (v ::ₘ R) hmix hmix').trans hflip)

/-- **The sharp dichotomy.**  For any spawn-monotone binary rule: constancy on
contested rosters is EXACTLY incumbent-clone-proofness on contested rosters.
A rule either ignores the contested region entirely, or an incumbent
somewhere profits by minting one duplicate. -/
theorem mixed_roster_dichotomy (F : Rule) (hmono : SpawnMonotone F) :
    (∀ P Q, Mixed P → Mixed Q → F P = F Q) ↔
    (∀ R v, Mixed R → v ∈ R → ¬(F R ≠ v ∧ F (v ::ₘ R) = v)) := by
  constructor
  · exact cloneProof_of_mixed_constant F
  · intro hproof
    by_contra hnc
    push_neg at hnc
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := hnc
    obtain ⟨R, v, hmix, hvR, hne, hflip⟩ :=
      mixed_roster_manipulable F hmono P Q hP hQ hPQ
    exact hproof R v hmix hvR ⟨hne, hflip⟩

/-! ### Sharpness: the unanimity counterexample -/

/-- The unanimity rule: `true` iff no dissenting vote is present (the empty
roster counts as unanimous). -/
def unanimity : Rule := fun R => decide (false ∉ R)

theorem unanimity_spawnMonotone : SpawnMonotone unanimity := by
  intro R v
  cases v
  · right
    simp [unanimity, Multiset.mem_cons]
  · left
    simp [unanimity, Multiset.mem_cons]

theorem unanimity_nonconstant : Nonconstant unanimity :=
  ⟨0, false ::ₘ 0, by simp [unanimity]⟩

theorem unanimity_eq_false_of_mixed {R : Multiset Bool} (h : Mixed R) :
    unanimity R = false := by
  simp [unanimity, h.1]

theorem unanimity_mixed_constant :
    ∀ P Q, Mixed P → Mixed Q → unanimity P = unanimity Q := by
  intro P Q hP hQ
  rw [unanimity_eq_false_of_mixed hP, unanimity_eq_false_of_mixed hQ]

/-- **Sharpness of the dichotomy.**  Unanimity is spawn-monotone and globally
non-constant, yet constant on contested rosters — so it allows no incumbent
clone manipulation.  Hence the naive strengthening of `roster_impossibility`
(demanding `v ∈ R` under mere global non-constancy) is false: contested-region
non-constancy is the exact hypothesis. -/
theorem unanimity_cloneProof :
    ∀ R v, Mixed R → v ∈ R →
      ¬(unanimity R ≠ v ∧ unanimity (v ::ₘ R) = v) :=
  cloneProof_of_mixed_constant unanimity unanimity_mixed_constant

end RosterSchema
end SEKernel
