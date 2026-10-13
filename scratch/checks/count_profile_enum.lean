import SEKernel.PluralityCountFormula
namespace SEKernel.Epistemic.CountTest
open Finset
open scoped Nat Classical
open SEKernel.FiniteProbability
noncomputable def triProfile (nx n0 n1 n2 : ℕ) : Option (Fin 3) → ℕ :=
  fun x => match x with | none => nx | some i => ![n0,n1,n2] i
@[simp] theorem triProfile_eq_iff (c : Option (Fin 3) → ℕ) (nx n0 n1 n2 : ℕ) :
    c = triProfile nx n0 n1 n2 ↔
      c none = nx ∧ c (some 0) = n0 ∧ c (some 1) = n1 ∧ c (some 2) = n2 := by
  simp [funext_iff, triProfile, Fin.forall_fin_succ]
theorem valid_tri_profiles_2 : validCountProfiles (Fin 3) 2 =
    {triProfile 0 0 0 2, triProfile 0 0 1 1, triProfile 0 0 2 0, triProfile 0 1 0 1, triProfile 0 1 1 0, triProfile 0 2 0 0, triProfile 1 0 0 1, triProfile 1 0 1 0, triProfile 1 1 0 0, triProfile 2 0 0 0} := by
  ext c
  simp only [validCountProfiles, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
    and_true, Fintype.sum_option, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Finset.mem_insert, Finset.mem_singleton, triProfile_eq_iff]
  omega
theorem valid_tri_profiles_3 : validCountProfiles (Fin 3) 3 =
    {triProfile 0 0 0 3, triProfile 0 0 1 2, triProfile 0 0 2 1, triProfile 0 0 3 0, triProfile 0 1 0 2, triProfile 0 1 1 1, triProfile 0 1 2 0, triProfile 0 2 0 1, triProfile 0 2 1 0, triProfile 0 3 0 0, triProfile 1 0 0 2, triProfile 1 0 1 1, triProfile 1 0 2 0, triProfile 1 1 0 1, triProfile 1 1 1 0, triProfile 1 2 0 0, triProfile 2 0 0 1, triProfile 2 0 1 0, triProfile 2 1 0 0, triProfile 3 0 0 0} := by
  ext c
  simp only [validCountProfiles, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
    and_true, Fintype.sum_option, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Finset.mem_insert, Finset.mem_singleton, triProfile_eq_iff]
  omega
theorem valid_tri_profiles_4 : validCountProfiles (Fin 3) 4 =
    {triProfile 0 0 0 4, triProfile 0 0 1 3, triProfile 0 0 2 2, triProfile 0 0 3 1, triProfile 0 0 4 0, triProfile 0 1 0 3, triProfile 0 1 1 2, triProfile 0 1 2 1, triProfile 0 1 3 0, triProfile 0 2 0 2, triProfile 0 2 1 1, triProfile 0 2 2 0, triProfile 0 3 0 1, triProfile 0 3 1 0, triProfile 0 4 0 0, triProfile 1 0 0 3, triProfile 1 0 1 2, triProfile 1 0 2 1, triProfile 1 0 3 0, triProfile 1 1 0 2, triProfile 1 1 1 1, triProfile 1 1 2 0, triProfile 1 2 0 1, triProfile 1 2 1 0, triProfile 1 3 0 0, triProfile 2 0 0 2, triProfile 2 0 1 1, triProfile 2 0 2 0, triProfile 2 1 0 1, triProfile 2 1 1 0, triProfile 2 2 0 0, triProfile 3 0 0 1, triProfile 3 0 1 0, triProfile 3 1 0 0, triProfile 4 0 0 0} := by
  ext c
  simp only [validCountProfiles, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
    and_true, Fintype.sum_option, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Finset.mem_insert, Finset.mem_singleton, triProfile_eq_iff]
  omega
end SEKernel.Epistemic.CountTest
