/-
SEKernel / StakeMedian.lean
The Moulin collapse and the stake-metered repair: spawn-manipulability of the
head-counted median, split-invariance of the stake-weighted median.

Median voting on single-peaked preferences is the classical escape from
Gibbard–Satterthwaite: strategyproof, anonymous, non-dictatorial.  This file
shows the escape does not survive endogenous populations, and exhibits the
repair.

* Head-counting (each identity carries unit weight): `median_spawn_manipulable`
  — in the three-voter profile with peaks {0, 5, 10} the unique median is 5;
  after the agent at 0 mints two fresh identities at its own peak, the unique
  median of the five-voter profile is 0.  The spawner drags the outcome onto
  its own peak: distance 5 → 0.
* Stake-metering: `wmedian_split_invariant` — splitting one participant of
  stake `s` into `k` co-located identities of stake `s / k` leaves the stake
  measure, and therefore the entire weighted-median set, unchanged.  The
  maneuver that captures the head-counted median moves the stake-weighted
  median not at all (`stake_median_spawn_proof`).
* `measure_rule_split_invariant` is the possibility half of the Roster Schema
  in miniature: ANY outcome rule that reads a profile only through its stake
  measure is split-invariant.
* `wmedian_partition_invariant` (referee strengthening): equal splits are a
  special case — ANY finite partition of a stake into co-located parts leaves
  the weighted-median set unchanged.

Prior art and scope (external referee, 2026-07-29).  The head-count median
attack is anticipated by Todo–Iwasaki–Yokoo, "False-name-proof Mechanism
Design without Money" (AAMAS 2011), which studies exactly false-name-proof
facility location on the line; this file's attack instance should be read as
a motivating benchmark, and the invariance results as the quotient lemma
(rules factoring through an additive measure ignore re-representations of a
fixed mass).  The intended semantics takes stakes nonnegative with positive
total; the algebra does not need this, but the reading of `IsWMedian` does.
Splits across DIFFERENT peaks change the measure and are an incentive
question, not an invariance question — deliberately out of scope here.

Zero custom axioms.
-/
import Mathlib

namespace SEKernel
namespace StakeMedian

/-- A profile is a finite multiset of (stake, peak) pairs. -/
abbrev Profile := Multiset (ℝ × ℝ)

/-- Stake mass at or below the point `m`. -/
noncomputable def massLe (P : Profile) (m : ℝ) : ℝ :=
  (P.map fun wp => if wp.2 ≤ m then wp.1 else 0).sum

/-- Stake mass at or above the point `m`. -/
noncomputable def massGe (P : Profile) (m : ℝ) : ℝ :=
  (P.map fun wp => if m ≤ wp.2 then wp.1 else 0).sum

/-- Total stake of the profile. -/
noncomputable def total (P : Profile) : ℝ := (P.map Prod.fst).sum

/-- `m` is a weighted median of `P`: at least half the stake lies at or below
`m`, and at least half at or above. -/
def IsWMedian (P : Profile) (m : ℝ) : Prop :=
  total P ≤ 2 * massLe P m ∧ total P ≤ 2 * massGe P m

/-- Split one participant of stake `s` at peak `p` into `k` identities, each
carrying stake `s / k` at the same peak, alongside the rest of the profile. -/
noncomputable def split (s p : ℝ) (k : ℕ) (rest : Profile) : Profile :=
  Multiset.replicate k (s / (k : ℝ), p) + rest

/-! ## The stake measure is split-invariant -/

theorem massLe_split (s p : ℝ) (k : ℕ) (hk : 1 ≤ k) (rest : Profile) (m : ℝ) :
    massLe (split s p k rest) m = massLe ((s, p) ::ₘ rest) m := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold massLe split
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_cons, Multiset.sum_cons]
  congr 1
  show k • (if p ≤ m then s / (k : ℝ) else 0) = if p ≤ m then s else 0
  split_ifs
  · rw [nsmul_eq_mul]; field_simp
  · simp

theorem massGe_split (s p : ℝ) (k : ℕ) (hk : 1 ≤ k) (rest : Profile) (m : ℝ) :
    massGe (split s p k rest) m = massGe ((s, p) ::ₘ rest) m := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold massGe split
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_cons, Multiset.sum_cons]
  congr 1
  show k • (if m ≤ p then s / (k : ℝ) else 0) = if m ≤ p then s else 0
  split_ifs
  · rw [nsmul_eq_mul]; field_simp
  · simp

theorem total_split (s p : ℝ) (k : ℕ) (hk : 1 ≤ k) (rest : Profile) :
    total (split s p k rest) = total ((s, p) ::ₘ rest) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold total split
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_cons, Multiset.sum_cons]
  congr 1
  show k • (s / (k : ℝ)) = s
  rw [nsmul_eq_mul]; field_simp

/-- **Stake-metered medians cannot be moved by splitting.**  Splitting a stake
into `k` co-located identities leaves the weighted-median set unchanged. -/
theorem wmedian_split_invariant (s p : ℝ) (k : ℕ) (hk : 1 ≤ k) (rest : Profile)
    (m : ℝ) :
    IsWMedian (split s p k rest) m ↔ IsWMedian ((s, p) ::ₘ rest) m := by
  unfold IsWMedian
  rw [massLe_split s p k hk rest m, massGe_split s p k hk rest m,
      total_split s p k hk rest]

/-- **Stake-metered medians are spawn-proof** (the median-mechanism analogue of
`spawnProof_iff_fnp`): no split is ever outcome-improving, because no split
changes the outcome set at all. -/
theorem stake_median_spawn_proof (s p : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (rest : Profile) :
    ∀ m, IsWMedian (split s p k rest) m ↔ IsWMedian ((s, p) ::ₘ rest) m :=
  fun m => wmedian_split_invariant s p k hk rest m

/-- **Possibility half of the Roster Schema, in miniature.**  Any outcome rule
`F` that reads a profile only through its stake measure — the functions
`massLe`, `massGe`, and the total — is invariant under stake splits. -/
theorem measure_rule_split_invariant
    (F : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop)
    (s p : ℝ) (k : ℕ) (hk : 1 ≤ k) (rest : Profile) :
    F (massLe (split s p k rest)) (massGe (split s p k rest))
        (total (split s p k rest)) ↔
      F (massLe ((s, p) ::ₘ rest)) (massGe ((s, p) ::ₘ rest))
        (total ((s, p) ::ₘ rest)) := by
  have hLe : massLe (split s p k rest) = massLe ((s, p) ::ₘ rest) :=
    funext fun m => massLe_split s p k hk rest m
  have hGe : massGe (split s p k rest) = massGe ((s, p) ::ₘ rest) :=
    funext fun m => massGe_split s p k hk rest m
  rw [hLe, hGe, total_split s p k hk rest]

/-! ## General partitions (referee strengthening): any finite division of a
stake among co-located identities, not merely equal `s / k` splits. -/

/-- Replace one participant by an arbitrary finite family of stakes `S` at the
same peak `p`; the represented participant is `(S.sum, p)`. -/
noncomputable def partitionAt (S : Multiset ℝ) (p : ℝ) (rest : Profile) :
    Profile :=
  S.map (fun s => (s, p)) + rest

theorem massLe_partition (S : Multiset ℝ) (p : ℝ) (rest : Profile) (m : ℝ) :
    massLe (partitionAt S p rest) m = massLe ((S.sum, p) ::ₘ rest) m := by
  unfold massLe partitionAt
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_cons,
      Multiset.sum_cons]
  congr 1
  by_cases h : p ≤ m
  · simp [Function.comp, h]
  · simp [Function.comp, h]

theorem massGe_partition (S : Multiset ℝ) (p : ℝ) (rest : Profile) (m : ℝ) :
    massGe (partitionAt S p rest) m = massGe ((S.sum, p) ::ₘ rest) m := by
  unfold massGe partitionAt
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_cons,
      Multiset.sum_cons]
  congr 1
  by_cases h : m ≤ p
  · simp [Function.comp, h]
  · simp [Function.comp, h]

theorem total_partition (S : Multiset ℝ) (p : ℝ) (rest : Profile) :
    total (partitionAt S p rest) = total ((S.sum, p) ::ₘ rest) := by
  unfold total partitionAt
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_cons,
      Multiset.sum_cons]
  congr 1
  simp [Function.comp]

/-- **Partition invariance.**  ANY finite division of a stake among co-located
identities leaves the weighted-median set unchanged — equal splits
(`wmedian_split_invariant`) are the special case `S = replicate k (s / k)`. -/
theorem wmedian_partition_invariant (S : Multiset ℝ) (p : ℝ) (rest : Profile)
    (m : ℝ) :
    IsWMedian (partitionAt S p rest) m ↔ IsWMedian ((S.sum, p) ::ₘ rest) m := by
  unfold IsWMedian
  rw [massLe_partition, massGe_partition, total_partition]

/-! ## Head-counting is spawn-manipulable -/

/-- Three head-counted voters with peaks 0, 5, 10 — every identity weight 1. -/
noncomputable def headP3 : Profile :=
  ((1 : ℝ), (0 : ℝ)) ::ₘ ((1 : ℝ), (5 : ℝ)) ::ₘ {((1 : ℝ), (10 : ℝ))}

/-- The same electorate after the agent at 0 mints two fresh identities at its
own peak — head-counting hands each clone a full unit of weight. -/
noncomputable def headP5 : Profile :=
  ((1 : ℝ), (0 : ℝ)) ::ₘ ((1 : ℝ), (0 : ℝ)) ::ₘ headP3

/-- In the three-voter head-counted profile the median is unique: it is 5. -/
theorem headP3_median (m : ℝ) : IsWMedian headP3 m ↔ m = 5 := by
  unfold IsWMedian massLe massGe total headP3
  simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
    Multiset.sum_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hm | hm
    · split_ifs at h1 <;> linarith
    · split_ifs at h2 <;> linarith
  · rintro rfl
    norm_num

/-- After the spawn, the median of the five-voter head-counted profile is
unique: it is 0 — the spawner's own peak. -/
theorem headP5_median (m : ℝ) : IsWMedian headP5 m ↔ m = 0 := by
  unfold IsWMedian massLe massGe total headP5 headP3
  simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
    Multiset.sum_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hm | hm
    · split_ifs at h1 <;> linarith
    · split_ifs at h2 <;> linarith
  · rintro rfl
    norm_num

/-- **The Moulin collapse: head-counted medians are spawn-manipulable.**
In the unit-weight profile with peaks {0, 5, 10} the unique median is 5.  After
the agent at 0 mints two fresh unit-weight identities at its own peak, the
unique median is 0: the outcome lands exactly on the spawner's peak, cutting
its distance from the outcome from 5 to 0.  Contrast
`stake_median_spawn_proof`: under stake metering the same maneuver cannot move
the outcome at all.  Single-peakedness, the classical escape from
Gibbard–Satterthwaite, does not survive endogenous populations. -/
theorem median_spawn_manipulable :
    (∀ m, IsWMedian headP3 m ↔ m = 5) ∧
    (∀ m, IsWMedian headP5 m ↔ m = 0) ∧
    |(0 : ℝ) - 0| < |(5 : ℝ) - 0| :=
  ⟨headP3_median, headP5_median, by norm_num⟩

end StakeMedian
end SEKernel
