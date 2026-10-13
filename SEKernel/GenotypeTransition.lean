/-
Finite two-locus transmission conditional on the actual survivor roster.
Board and advocate bits are retained separately. All generations in the
numerical statements below are one-step statements, conditional on survivors.
-/
import SEKernel.PluralityCountExamples
import SEKernel.MutationBaseline
import SEKernel.NoisySelection

namespace SEKernel.GenotypeTransition

open Finset FiniteProbability
open scoped BigOperators Classical
noncomputable section

abbrev Genotype := Bool × Bool

/-- Mixture weight `t` is the weight of the second law. -/
def mixture {Ω : Type*} [Fintype Ω] (L K : Law Ω) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : Law Ω where
  mass ω := (1-t)*L.mass ω+t*K.mass ω
  nonneg ω := add_nonneg (mul_nonneg (by linarith) (L.nonneg ω))
    (mul_nonneg ht (K.nonneg ω))
  total := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, L.total, K.total]; ring

def boardMass (q : Law Genotype) : ℝ := q.mass (true,false)+q.mass (true,true)
def advocateMass (q : Law Genotype) : ℝ := q.mass (false,true)+q.mass (true,true)
def voterMass (q : Law Genotype) : ℝ := q.mass (false,false)+q.mass (false,true)
def linkage (q : Law Genotype) : ℝ := q.mass (true,true)-boardMass q*advocateMass q

theorem four_masses_sum (q : Law Genotype) :
    q.mass (false,false)+q.mass (false,true)+q.mass (true,false)+q.mass (true,true)=1 := by
  have h := q.total
  simpa [Fintype.sum_prod_type, Fintype.sum_bool, add_assoc, add_comm, add_left_comm] using h

theorem voterMass_eq_one_sub_boardMass (q : Law Genotype) : voterMass q=1-boardMass q := by
  have h := four_masses_sum q
  unfold voterMass boardMass
  linarith

theorem linkage_determinant (q : Law Genotype) :
    linkage q=q.mass (false,false)*q.mass (true,true)-q.mass (false,true)*q.mass (true,false) := by
  have h := congrArg (fun x : ℝ => x*q.mass (true,true)) (four_masses_sum q)
  unfold linkage boardMass advocateMass
  nlinarith only [h]

/-- General recombination operator. The actual parent protocols are linked below. -/
def recombine (q : Law Genotype) (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) : Law Genotype :=
  mixture q ((q.map Prod.fst).prod (q.map Prod.snd)) rho hrho hrho1

theorem marginal_fst_mass (q : Law Genotype) (b : Bool) :
    (q.map Prod.fst).mass b=q.mass (b,false)+q.mass (b,true) := by
  cases b <;> simp [Law.map, Law.prob, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]

theorem marginal_snd_mass (q : Law Genotype) (a : Bool) :
    (q.map Prod.snd).mass a=q.mass (false,a)+q.mass (true,a) := by
  cases a <;> simp [Law.map, Law.prob, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]

theorem recombine_mass (q : Law Genotype) (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1)
    (g : Genotype) :
    (recombine q rho h0 h1).mass g=(1-rho)*q.mass g+
      rho*(q.mass (g.1,false)+q.mass (g.1,true))*(q.mass (false,g.2)+q.mass (true,g.2)) := by
  simp only [recombine, mixture, Law.prod, marginal_fst_mass, marginal_snd_mass]
  ring

theorem recombine_boardMass (q : Law Genotype) (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    boardMass (recombine q rho h0 h1)=boardMass q := by
  have h := four_masses_sum q
  unfold boardMass
  simp only [recombine_mass]
  nlinarith only [congrArg (fun x : ℝ => rho*(q.mass (true,false)+q.mass (true,true))*x) h]

theorem recombine_advocateMass (q : Law Genotype) (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    advocateMass (recombine q rho h0 h1)=advocateMass q := by
  have h := four_masses_sum q
  unfold advocateMass
  simp only [recombine_mass]
  nlinarith only [congrArg (fun x : ℝ => rho*(q.mass (false,true)+q.mass (true,true))*x) h]

theorem recombine_linkage (q : Law Genotype) (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    linkage (recombine q rho h0 h1)=(1-rho)*linkage q := by
  unfold linkage
  rw [recombine_boardMass, recombine_advocateMass, recombine_mass]
  unfold boardMass advocateMass
  ring

/-- Each of the two locus-choice coins independently chooses either parent. -/
def pairCrossover (p q : Genotype) : Law Genotype :=
  (NoisySelection.uniformLaw (Bool×Bool)).map (fun c =>
    (if c.1 then p.1 else q.1, if c.2 then p.2 else q.2))

theorem pairCrossover_mass (p q g : Genotype) :
    (pairCrossover p q).mass g=(1/4 : ℝ)*
      ((if p=g then 1 else 0)+(if q=g then 1 else 0)+
       (if (p.1,q.2)=g then 1 else 0)+(if (q.1,p.2)=g then 1 else 0)) := by
  simp only [pairCrossover, Law.map, Law.prob, NoisySelection.uniformLaw,
    Fintype.sum_prod_type, Fintype.sum_bool, Fintype.card_prod, Fintype.card_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.eta]
  split_ifs <;> norm_num

/-- Actual independent parent sampling from a genotype law. -/
def independentCrossover (q : Law Genotype) : Law Genotype :=
  (q.prod q).bind (fun p => pairCrossover p.1 p.2)

theorem independentCrossover_mass (q : Law Genotype) (g : Genotype) :
    (independentCrossover q).mass g=
      (recombine q (1/2) (by norm_num) (by norm_num)).mass g := by
  have h := four_masses_sum q
  rcases g with ⟨b,a⟩
  cases b <;> cases a <;>
    simp [independentCrossover, Law.bind, Law.prod, pairCrossover_mass,
      Fintype.sum_prod_type, Fintype.sum_bool, recombine_mass] <;>
    nlinarith only [congrArg (fun x : ℝ => x*q.mass (false,false)) h,
      congrArg (fun x : ℝ => x*q.mass (false,true)) h,
      congrArg (fun x : ℝ => x*q.mass (true,false)) h,
      congrArg (fun x : ℝ => x*q.mass (true,true)) h]

/-- Uniform sampling of an actual survivor index. -/
def uniformIndex (S : ℕ) (hS : 0 < S) : Law (Fin S) where
  mass _ := 1/(S:ℝ)
  nonneg _ := by positivity
  total := by
    have hs : (S:ℝ) ≠ 0 := by positivity
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

def survivorLaw {S : ℕ} (s : Fin S → Genotype) (hS : 0 < S) : Law Genotype :=
  (uniformIndex S hS).map s

theorem survivorLaw_mass {S : ℕ} (s : Fin S → Genotype) (hS : 0 < S) (g : Genotype) :
    (survivorLaw s hS).mass g=(Epistemic.wordCount s g:ℝ)/S := by
  simp only [survivorLaw, Law.map, Law.prob, uniformIndex]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun i : Fin S => s i=g)).card=Epistemic.wordCount s g := by
    unfold Epistemic.wordCount
    apply congrArg Finset.card
    ext i
    simp
  rw [hc]
  ring

theorem expect_prod_iterated {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (L : Law Ω) (K : Law Λ) (F : Ω×Λ → ℝ) :
    (L.prod K).expect F=L.expect (fun x => K.expect (fun y => F (x,y))) := by
  simp only [Law.expect, Law1.mean, Law.prod, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]

theorem prod_map_expect {Ω Λ Ξ Ψ : Type*} [Fintype Ω] [Fintype Λ]
    [Fintype Ξ] [Fintype Ψ] (L : Law Ω) (K : Law Λ) (f : Ω → Ξ) (g : Λ → Ψ)
    (F : Ξ×Ψ → ℝ) :
    (L.prod K).expect (fun xy => F (f xy.1,g xy.2))=
      ((L.map f).prod (K.map g)).expect F := by
  simp_rw [expect_prod_iterated, Law.expect_map]

/-- Independent actual parent indices, including the diagonal. -/
def independentRosterCrossover {S : ℕ} (s : Fin S → Genotype) (hS : 0 < S) : Law Genotype :=
  ((uniformIndex S hS).prod (uniformIndex S hS)).bind
    (fun ij => pairCrossover (s ij.1) (s ij.2))

theorem independentRosterCrossover_mass {S : ℕ} (s : Fin S → Genotype) (hS : 0 < S)
    (g : Genotype) :
    (independentRosterCrossover s hS).mass g=
      (recombine (survivorLaw s hS) (1/2) (by norm_num) (by norm_num)).mass g := by
  rw [← independentCrossover_mass]
  change (((uniformIndex S hS).prod (uniformIndex S hS)).expect
    (fun ij => (pairCrossover (s ij.1) (s ij.2)).mass g)) =
      (((survivorLaw s hS).prod (survivorLaw s hS)).expect
        (fun p => (pairCrossover p.1 p.2).mass g))
  exact prod_map_expect (uniformIndex S hS) (uniformIndex S hS) s s
    (fun p => (pairCrossover p.1 p.2).mass g)

/-- Symmetric per-locus flip; only children receive this kernel. -/
def flipLaw (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (b : Bool) : Law Bool :=
  MutationBaseline.bernoulli (if b then 1-mu else mu)
    (by cases b <;> simp <;> linarith) (by cases b <;> simp <;> linarith)

theorem flipLaw_mass (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (b a : Bool) :
    (flipLaw mu h0 h1 b).mass a=if b=a then 1-mu else mu := by
  cases b <;> cases a <;> simp [flipLaw, MutationBaseline.bernoulli]

def mutationKernel (muB muA : ℝ) (hB0 : 0 ≤ muB) (hB1 : muB ≤ 1)
    (hA0 : 0 ≤ muA) (hA1 : muA ≤ 1) : Kernel Genotype Genotype :=
  fun g => (flipLaw muB hB0 hB1 g.1).prod (flipLaw muA hA0 hA1 g.2)

def mutate (q : Law Genotype) (muB muA : ℝ) (hB0 : 0 ≤ muB) (hB1 : muB ≤ 1)
    (hA0 : 0 ≤ muA) (hA1 : muA ≤ 1) : Law Genotype :=
  q.bind (mutationKernel muB muA hB0 hB1 hA0 hA1)

theorem mutate_mass (q : Law Genotype) (muB muA : ℝ) (hB0 : 0 ≤ muB) (hB1 : muB ≤ 1)
    (hA0 : 0 ≤ muA) (hA1 : muA ≤ 1) (g : Genotype) :
    (mutate q muB muA hB0 hB1 hA0 hA1).mass g=
      ∑ p : Genotype, q.mass p*(if p.1=g.1 then 1-muB else muB)*
        (if p.2=g.2 then 1-muA else muA) := by
  simp only [mutate, Law.bind, mutationKernel, Law.prod, flipLaw_mass, mul_assoc]

theorem mutate_voterMass (q : Law Genotype) (muB muA : ℝ)
    (hB0 : 0 ≤ muB) (hB1 : muB ≤ 1) (hA0 : 0 ≤ muA) (hA1 : muA ≤ 1) :
    voterMass (mutate q muB muA hB0 hB1 hA0 hA1)=
      (1-muB)*voterMass q+muB*boardMass q := by
  unfold voterMass boardMass
  simp only [mutate_mass, Fintype.sum_prod_type, Fintype.sum_bool]
  simp
  ring

/-- Boundary-safe silent coordinate; no compartment ratio is used here. -/
theorem mutate_silent_coordinate (q : Law Genotype) (muB muA : ℝ)
    (hB0 : 0 ≤ muB) (hB1 : muB ≤ 1) (hA0 : 0 ≤ muA) (hA1 : muA ≤ 1) :
    (mutate q muB muA hB0 hB1 hA0 hA1).mass (false,true)=
      muA*((1-muB)*voterMass q+muB*boardMass q)+
        (1-2*muA)*((1-muB)*q.mass (false,true)+muB*q.mass (true,true)) := by
  unfold voterMass boardMass
  simp only [mutate_mass, Fintype.sum_prod_type, Fintype.sum_bool]
  simp
  ring

/-- Actual next-slot law: elites are unchanged, mutation is offspring-only. -/
def retainedOffspringLaw (q child : Law Genotype) (elite : ℝ)
    (he0 : 0 ≤ elite) (he1 : elite ≤ 1) : Law Genotype :=
  mixture child q elite he0 he1

/-- A conditional frequency requires its voter compartment to have positive mass. -/
def silentFrequency (q : Law Genotype) (_hV : 0 < voterMass q) : ℝ :=
  q.mass (false,true)/voterMass q

theorem retainedOffspring_silentFrequency (q child : Law Genotype) (elite : ℝ)
    (he0 : 0 ≤ elite) (he1 : elite ≤ 1)
    (hV : 0 < voterMass (retainedOffspringLaw q child elite he0 he1)) :
    silentFrequency (retainedOffspringLaw q child elite he0 he1) hV=
      (elite*q.mass (false,true)+(1-elite)*child.mass (false,true))/
        (elite*voterMass q+(1-elite)*voterMass child) := by
  unfold silentFrequency voterMass retainedOffspringLaw mixture
  congr 1 <;> ring

/-- Uniform ordered distinct survivor indices; diagonal pairs have zero mass. -/
def distinctPairLaw (S : ℕ) (hS : 1 < S) : Law (Fin S × Fin S) where
  mass ij := if ij.1=ij.2 then 0 else 1/((S:ℝ)*((S:ℝ)-1))
  nonneg ij := by
    have hs : (1:ℝ)<S := by exact_mod_cast hS
    have hm : 0<(S:ℝ)-1 := by linarith
    split_ifs; rfl; positivity
  total := by
    have hs : (1:ℝ)<S := by exact_mod_cast hS
    have hs0 : (S:ℝ) ≠ 0 := by linarith
    have hs1 : (S:ℝ)-1 ≠ 0 := by linarith
    have hd : (S:ℝ)*((S:ℝ)-1) ≠ 0 := mul_ne_zero hs0 hs1
    have hrow (i : Fin S) :
        (∑ j : Fin S, if i=j then (0:ℝ) else 1/((S:ℝ)*((S:ℝ)-1)))=
          ((S:ℝ)-1)/((S:ℝ)*((S:ℝ)-1)) := by
      calc
        _ = ∑ j : Fin S, (1/((S:ℝ)*((S:ℝ)-1))-
            if i=j then 1/((S:ℝ)*((S:ℝ)-1)) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
        _ = _ := by rw [Finset.sum_sub_distrib]; simp; field_simp [hs0, hs1] <;> ring
    rw [Fintype.sum_prod_type]
    simp_rw [hrow]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hs0, hs1]

theorem distinctPair_expect {S : ℕ} (hS : 1 < S) (F : Fin S × Fin S → ℝ) :
    (distinctPairLaw S hS).expect F=
      ((∑ ij, F ij)-∑ i, F (i,i))/((S:ℝ)*((S:ℝ)-1)) := by
  unfold Law.expect Law1.mean distinctPairLaw
  have he (ij : Fin S×Fin S) :
      (if ij.1=ij.2 then (0:ℝ) else 1/((S:ℝ)*((S:ℝ)-1)))*F ij=
        (F ij-(if ij.1=ij.2 then F ij else 0))/((S:ℝ)*((S:ℝ)-1)) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hd : (∑ ij : Fin S×Fin S, if ij.1=ij.2 then F ij else 0)=∑ i, F (i,i) := by
    rw [Fintype.sum_prod_type]
    simp
  rw [hd]

theorem pairCrossover_diagonal_mass (p g : Genotype) :
    (pairCrossover p p).mass g=if p=g then 1 else 0 := by
  rw [pairCrossover_mass]
  simp only [Prod.mk.eta]
  split_ifs <;> norm_num

theorem independentRoster_mass_sum {S : ℕ} (s : Fin S → Genotype) (hS : 0 < S)
    (g : Genotype) :
    (independentRosterCrossover s hS).mass g=
      (∑ ij : Fin S×Fin S, (pairCrossover (s ij.1) (s ij.2)).mass g)/(S:ℝ)^2 := by
  simp only [independentRosterCrossover, Law.bind, Law.prod, uniformIndex]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ij _
  ring

theorem survivorLaw_mass_indicator {S : ℕ} (s : Fin S → Genotype) (hS : 0 < S)
    (g : Genotype) :
    (survivorLaw s hS).mass g=(∑ i, if s i=g then (1:ℝ) else 0)/(S:ℝ) := by
  simp only [survivorLaw, Law.map, Law.prob, uniformIndex]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

def distinctRosterCrossover {S : ℕ} (s : Fin S → Genotype) (hS : 1 < S) : Law Genotype :=
  (distinctPairLaw S hS).bind (fun ij => pairCrossover (s ij.1) (s ij.2))

def distinctRho (S : ℕ) : ℝ := S/(2*((S:ℝ)-1))

theorem distinctRho_bounds {S : ℕ} (hS : 1 < S) : 0 ≤ distinctRho S ∧ distinctRho S ≤ 1 := by
  have hs : (2:ℝ)≤S := by exact_mod_cast hS
  have hm : 0<(S:ℝ)-1 := by linarith
  unfold distinctRho
  constructor
  · positivity
  · apply (div_le_one (by linarith : 0<2*((S:ℝ)-1))).2
    linarith

/-- Actual distinct-parent sampling gives rho = S/(2(S-1)), for every genotype. -/
theorem distinctRosterCrossover_mass {S : ℕ} (s : Fin S → Genotype) (hS : 1 < S)
    (g : Genotype) :
    (distinctRosterCrossover s hS).mass g=
      (recombine (survivorLaw s (by omega)) (distinctRho S)
        (distinctRho_bounds hS).1 (distinctRho_bounds hS).2).mass g := by
  let q := survivorLaw s (show 0<S by omega)
  have hs : (1:ℝ)<S := by exact_mod_cast hS
  have hs0 : (S:ℝ) ≠ 0 := by positivity
  have hs1 : (S:ℝ)-1 ≠ 0 := by linarith
  have hi := independentRoster_mass_sum s (show 0<S by omega) g
  rw [independentRosterCrossover_mass] at hi
  have hsum : (∑ ij : Fin S×Fin S, (pairCrossover (s ij.1) (s ij.2)).mass g)=
      (S:ℝ)^2*(recombine q (1/2) (by norm_num) (by norm_num)).mass g := by
    apply (eq_div_iff (pow_ne_zero 2 hs0)).mp at hi
    simpa [q, mul_comm] using hi.symm
  have hdiag : (∑ i : Fin S, (pairCrossover (s i) (s i)).mass g)=(S:ℝ)*q.mass g := by
    simp only [pairCrossover_diagonal_mass]
    rw [show q.mass g=(∑ i : Fin S, if s i=g then (1:ℝ) else 0)/(S:ℝ) from
      survivorLaw_mass_indicator s (show 0<S by omega) g]
    field_simp
  change (distinctPairLaw S hS).expect (fun ij => (pairCrossover (s ij.1) (s ij.2)).mass g)=_
  rw [distinctPair_expect, hsum, hdiag]
  simp only [recombine_mass]
  change _=(1-distinctRho S)*q.mass g+
    distinctRho S*(q.mass (g.1,false)+q.mass (g.1,true))*(q.mass (false,g.2)+q.mass (true,g.2))
  unfold distinctRho
  field_simp
  <;> ring

theorem wordCount_le {N : ℕ} {B : Type*} [Fintype B] (z : Fin N → B) (g : B) :
    Epistemic.wordCount z g≤N := by
  calc
    _ ≤ ∑ b, Epistemic.wordCount z b :=
      Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ g)
    _ = N := Epistemic.sum_wordCount z

/-- Histograms are finite bounded vectors with their actual population total. -/
abbrev Histogram (P : ℕ) := {n : Genotype → Fin (P+1) // ∑ g, (n g:ℕ)=P}

def histogram {P : ℕ} (z : Fin P → Genotype) : Histogram P :=
  ⟨fun g => ⟨Epistemic.wordCount z g, by
      have hb := wordCount_le z g
      omega⟩, by simpa using Epistemic.sum_wordCount z⟩

def histogramCount {P : ℕ} (n : Histogram P) (g : Genotype) : ℕ := n.val g

def nextRoster {S M : ℕ} (s : Fin S → Genotype) (w : Fin M → Genotype) :
    Fin (S+M) → Genotype := Fin.addCases s w

theorem wordCount_eq_sum {N : ℕ} {B : Type*} (z : Fin N → B) (g : B) :
    Epistemic.wordCount z g=∑ i, if z i=g then (1:ℕ) else 0 := by
  unfold Epistemic.wordCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem wordCount_real_eq_sum {N : ℕ} {B : Type*} (z : Fin N → B) (g : B) :
    (Epistemic.wordCount z g:ℝ)=∑ i, if z i=g then (1:ℝ) else 0 := by
  rw [wordCount_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem nextRoster_count {S M : ℕ} (s : Fin S → Genotype) (w : Fin M → Genotype)
    (g : Genotype) :
    Epistemic.wordCount (nextRoster s w) g=Epistemic.wordCount s g+Epistemic.wordCount w g := by
  simp only [wordCount_eq_sum]
  rw [Fin.sum_univ_add]
  simp only [nextRoster, Fin.addCases_left, Fin.addCases_right]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : s i=g <;> simp [h]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : w i=g <;> simp [h]

/-- Conditional independent offspring, pushed forward to the actual next histogram. -/
def broodHistogramLaw {S : ℕ} (s : Fin S → Genotype) (child : Law Genotype) (M : ℕ) :
    Law (Histogram (S+M)) :=
  (Epistemic.iidAlphabetLaw child M).map (fun w => histogram (nextRoster s w))

theorem broodHistogram_mass {S M : ℕ} (s : Fin S → Genotype) (child : Law Genotype)
    (n : Histogram (S+M)) :
    (broodHistogramLaw s child M).mass n=
      ∑ w : Fin M → Genotype, if histogram (nextRoster s w)=n then ∏ j, child.mass (w j) else 0 := by
  unfold broodHistogramLaw Law.map Law.prob Epistemic.iidAlphabetLaw Law.pi
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : histogram (nextRoster s w)=n <;> simp [h]

theorem iid_offspring_count_expectation {M : ℕ} (child : Law Genotype) (g : Genotype) :
    (Epistemic.iidAlphabetLaw child M).expect (fun w => (Epistemic.wordCount w g:ℝ))=
      (M:ℝ)*child.mass g := by
  simp_rw [wordCount_real_eq_sum]
  rw [Law.expect_sum]
  have hx : child.expect (fun x => if x=g then (1:ℝ) else 0)=child.mass g := by
    rw [Law.expect_indicator]
    unfold Law.prob
    rw [Finset.sum_eq_single g]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  calc
    _ = ∑ _i : Fin M, child.mass g := by
      apply Finset.sum_congr rfl
      intro i _
      have hc := Law.expect_pi_coord (fun _ : Fin M => child) i
        (fun x => if x=g then (1:ℝ) else 0)
      convert hc.trans hx using 1
      unfold Epistemic.iidAlphabetLaw
      apply congrArg (Law.pi (fun _ : Fin M => child)).expect
      funext w
      by_cases h : w i=g <;> simp [h]
    _ = _ := by simp

/-- The actual next-count first moment, conditional on a fixed survivor roster. -/
theorem broodHistogram_expectedCount {S M : ℕ} (s : Fin S → Genotype)
    (child : Law Genotype) (g : Genotype) :
    (broodHistogramLaw s child M).expect (fun n => (histogramCount n g:ℝ))=
      (Epistemic.wordCount s g:ℝ)+(M:ℝ)*child.mass g := by
  rw [broodHistogramLaw, Law.expect_map]
  change (Epistemic.iidAlphabetLaw child M).expect
    (fun w => (Epistemic.wordCount (nextRoster s w) g:ℝ))=_
  simp_rw [nextRoster_count, Nat.cast_add]
  rw [Law.expect_add, Law.expect_const, iid_offspring_count_expectation]

/-- `σ` retains the full history; the supplied selection law returns an ordered survivor roster.
This is a conditional histogram projection, not a Markov assertion about histograms. -/
def histogramKernel {State : Type*} [Fintype State] {S M : ℕ}
    (selected : Kernel State (Fin S → Genotype)) (child : (Fin S → Genotype) → Law Genotype) :
    Kernel State (Histogram (S+M)) :=
  fun σ => (selected σ).bind (fun s => broodHistogramLaw s (child s) M)

/-- Doc B C4f: the full finite conditional histogram kernel. -/
theorem histogramKernel_mass {State : Type*} [Fintype State] {S M : ℕ}
    (selected : Kernel State (Fin S → Genotype)) (child : (Fin S → Genotype) → Law Genotype)
    (σ : State) (n : Histogram (S+M)) :
    (histogramKernel (M := M) selected child σ).mass n=
      ∑ s : Fin S → Genotype, (selected σ).mass s*
        ∑ w : Fin M → Genotype, if histogram (nextRoster s w)=n then ∏ j, (child s).mass (w j) else 0 := by
  simp only [histogramKernel, Law.bind, broodHistogram_mass]

/-- Doc B C4g: first moment averaged over the history-conditioned survivor law. -/
theorem histogramKernel_expectedCount {State : Type*} [Fintype State] {S M : ℕ}
    (selected : Kernel State (Fin S → Genotype)) (child : (Fin S → Genotype) → Law Genotype)
    (σ : State) (g : Genotype) :
    (histogramKernel (M := M) selected child σ).expect (fun n => (histogramCount n g:ℝ))=
      (selected σ).expect (fun s => (Epistemic.wordCount s g:ℝ)+(M:ℝ)*(child s).mass g) := by
  rw [histogramKernel, Law.expect_bind]
  simp_rw [broodHistogram_expectedCount]

/-- Selection of an actual subset, preserving its original roster order. -/
def selectedRoster {P S : ℕ} (z : Fin P → Genotype) (A : NoisySelection.Survivors P S) :
    Fin S → Genotype := fun i => z (A.val.orderEmbOfFin A.property i)

/-- Actual finite selection laws can be transported into the conditional histogram kernel. -/
def rosterSelectionLaw {P S : ℕ} (z : Fin P → Genotype)
    (L : Law (NoisySelection.Survivors P S)) : Law (Fin S → Genotype) :=
  L.map (selectedRoster z)

/-- Ratio of expected counts, with a positive expected voter count explicit. -/
def ratioOfExpectations {Ω : Type*} [Fintype Ω] (L : Law Ω) (carriers voters : Ω → ℝ)
    (_hV : 0<L.expect voters) : ℝ := L.expect carriers/L.expect voters

/-- Expected realized ratio, with division-zero convention explicitly set to zero.
An estimand conditional on voter presence requires a separate positive event mass. -/
def expectedRatio {Ω : Type*} [Fintype Ω] (L : Law Ω) (carriers voters : Ω → ℝ) : ℝ :=
  L.expect (fun ω => if voters ω=0 then 0 else carriers ω/voters ω)

/-- Doc B C4e: two genuine count outcomes separate the two estimands. -/
theorem ratio_expectation_counterexample :
    let L := MutationBaseline.bernoulli (1/2) (by norm_num) (by norm_num)
    let carriers := fun b : Bool => if b then (1:ℝ) else 0
    let voters := fun b : Bool => if b then (1:ℝ) else 3
    L.expect (fun b => carriers b/voters b)=1/2 ∧
      L.expect carriers/L.expect voters=1/4 := by
  norm_num [Law.expect, Law1.mean, MutationBaseline.bernoulli]

/-- Regrouping genuinely separate per-child/locus product coordinates. -/
theorem iid_product_expectation {M : ℕ} (L K : Law Bool) (F : (Fin M → Genotype) → ℝ) :
    (Epistemic.iidAlphabetLaw (L.prod K) M).expect F=
      ((Epistemic.iidAlphabetLaw L M).prod (Epistemic.iidAlphabetLaw K M)).expect
        (fun ba => F (fun i => (ba.1 i,ba.2 i))) := by
  apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin M) (fun _ => Bool) (fun _ => Bool))
  intro w
  simp only [Law.expect, Law1.mean, Epistemic.iidAlphabetLaw, Law.pi, Law.prod,
    Equiv.arrowProdEquivProdArrow, Finset.prod_mul_distrib]
  rfl

/-- A finite count statistic partitions an expectation into its proved point masses. -/
theorem expect_count_function {Ω : Type*} [Fintype Ω] (L : Law Ω)
    (count : Ω → ℕ) (M : ℕ) (hbound : ∀ ω, count ω≤M) (F : ℕ → ℝ) :
    L.expect (fun ω => F (count ω))=
      ∑ j ∈ Finset.range (M+1), L.prob (fun ω => count ω=j)*F j := by
  unfold Law.expect Law1.mean Law.prob
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_eq_single (count ω)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hn
    exact (hn (Finset.mem_range.mpr (by have h := hbound ω; omega))).elim

def voterCountR {P : ℕ} (z : Fin P → Genotype) : ℝ :=
  ∑ i, if (z i).1 then 0 else 1

def silentCountR {P : ℕ} (z : Fin P → Genotype) : ℝ :=
  ∑ i, if (z i).1 then 0 else if (z i).2 then 1 else 0

theorem voterCountR_eq_count {P : ℕ} (z : Fin P → Genotype) :
    voterCountR z=(Epistemic.wordCount (fun i => (z i).1) false:ℝ) := by
  rw [wordCount_real_eq_sum]
  unfold voterCountR
  apply Finset.sum_congr rfl
  intro i _
  cases (z i).1 <;> simp

theorem silentCountR_eq_count {P : ℕ} (z : Fin P → Genotype) :
    silentCountR z=(Epistemic.wordCount z (false,true):ℝ) := by
  rw [wordCount_real_eq_sum]
  unfold silentCountR
  apply Finset.sum_congr rfl
  intro i _
  rcases h : z i with ⟨b,a⟩
  cases b <;> cases a <;> simp

/-- The realized silent/voter ratio; division gives zero on an empty voter class. -/
def populationSilentRatio {P : ℕ} (z : Fin P → Genotype) : ℝ := silentCountR z/voterCountR z

/-- Actual IID brood expectation conditional on a specified survivor roster. -/
def nextSilentExpectation {S : ℕ} (s : Fin S → Genotype) (child : Law Genotype) (M : ℕ) : ℝ :=
  (Epistemic.iidAlphabetLaw child M).expect (fun w => populationSilentRatio (nextRoster s w))

theorem all00_ratio {S M : ℕ} (b a : Fin M → Bool) :
    populationSilentRatio (nextRoster (fun _ : Fin S => (false,false)) (fun i => (b i,a i)))=
      (∑ i, if b i then (0:ℝ) else if a i then 1 else 0)/
        ((S:ℝ)+(Epistemic.wordCount b false:ℝ)) := by
  unfold populationSilentRatio silentCountR voterCountR
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [nextRoster, Fin.addCases_left, Fin.addCases_right, Bool.false_eq_true,
    ↓reduceIte, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  congr 1
  rw [wordCount_real_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases b i <;> simp

/-- For a fixed board word the advocate bits have an independent Bernoulli law. -/
theorem all00_inner_expectation {S M : ℕ} (b : Fin M → Bool) (muA : ℝ)
    (hA0 : 0 ≤ muA) (hA1 : muA≤1) :
    (Epistemic.iidAlphabetLaw (MutationBaseline.bernoulli muA hA0 hA1) M).expect
      (fun a => populationSilentRatio (nextRoster (fun _ : Fin S => (false,false))
        (fun i => (b i,a i))))=
      muA*(Epistemic.wordCount b false:ℝ)/((S:ℝ)+(Epistemic.wordCount b false:ℝ)) := by
  simp_rw [all00_ratio, div_eq_mul_inv]
  rw [Law.expect_mul_const, Law.expect_sum]
  have he (i : Fin M) :
      (Epistemic.iidAlphabetLaw (MutationBaseline.bernoulli muA hA0 hA1) M).expect
        (fun a => if b i then (0:ℝ) else if a i then 1 else 0)=if b i then 0 else muA := by
    cases hb : b i
    · change (Law.pi (fun _ : Fin M => MutationBaseline.bernoulli muA hA0 hA1)).expect
        (fun a => (fun x : Bool => if x then (1:ℝ) else 0) (a i))=muA
      exact (Law.expect_pi_coord (fun _ : Fin M => MutationBaseline.bernoulli muA hA0 hA1)
        i (fun x : Bool => if x then (1:ℝ) else 0)).trans
          (MutationBaseline.bernoulli_mean muA hA0 hA1)
    · simp [hb]
  simp_rw [he]
  have hs : (∑ i, if b i then (0:ℝ) else muA)=muA*(Epistemic.wordCount b false:ℝ) := by
    rw [wordCount_real_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases b i <;> simp
  rw [hs]

/-- Exact one-step expected ratio, given all survivors 00 and independent offspring locus flips.
This is an actual finite IID expectation, not a ratio of expected counts. -/
theorem all00_expected_silent_ratio {S M : ℕ} (muB muA : ℝ)
    (hB0 : 0 ≤ muB) (hB1 : muB≤1) (hA0 : 0 ≤ muA) (hA1 : muA≤1) :
    nextSilentExpectation (fun _ : Fin S => (false,false))
      ((MutationBaseline.bernoulli muB hB0 hB1).prod
        (MutationBaseline.bernoulli muA hA0 hA1)) M=
      ∑ j ∈ Finset.range (M+1),
        (M.choose j:ℝ)*(1-muB)^j*muB^(M-j)*(muA*j/((S:ℝ)+j)) := by
  unfold nextSilentExpectation
  rw [iid_product_expectation, expect_prod_iterated]
  simp_rw [all00_inner_expectation]
  rw [expect_count_function _ (fun b => Epistemic.wordCount b false) M (fun b => wordCount_le b false)
    (fun j => muA*j/((S:ℝ)+j))]
  apply Finset.sum_congr rfl
  intro j hj
  have hjM : j≤M := by have h := Finset.mem_range.mp hj; omega
  rw [Epistemic.iid_single_label_count_probability _ false hjM]
  simp [MutationBaseline.bernoulli]

/-- G2 one-step fixed-survivor ingredient: no B mutation, four 00 survivors and eight offspring. -/
theorem all00_one_step_one_fifteenth :
    nextSilentExpectation (fun _ : Fin 4 => (false,false))
      ((MutationBaseline.bernoulli 0 (by norm_num) (by norm_num)).prod
        (MutationBaseline.bernoulli (1/10) (by norm_num) (by norm_num))) 8=1/15 := by
  rw [all00_expected_silent_ratio]
  norm_num [Finset.sum_range_succ, Nat.choose]

/-- G2 actual expected ratio with both loci mutated in offspring only; one step, given survivors. -/
theorem all00_one_step_two_locus_expected_ratio :
    nextSilentExpectation (fun _ : Fin 4 => (false,false))
      ((MutationBaseline.bernoulli (1/10) (by norm_num) (by norm_num)).prod
        (MutationBaseline.bernoulli (1/10) (by norm_num) (by norm_num))) 8=
      3523336551/55000000000 := by
  rw [all00_expected_silent_ratio]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem nextRoster_silentCountR {S M : ℕ} (s : Fin S → Genotype) (w : Fin M → Genotype) :
    silentCountR (nextRoster s w)=silentCountR s+silentCountR w := by
  unfold silentCountR
  rw [Fin.sum_univ_add]
  simp [nextRoster]

theorem nextRoster_voterCountR {S M : ℕ} (s : Fin S → Genotype) (w : Fin M → Genotype) :
    voterCountR (nextRoster s w)=voterCountR s+voterCountR w := by
  unfold voterCountR
  rw [Fin.sum_univ_add]
  simp [nextRoster]

theorem iid_silentCountR_mean {M : ℕ} (child : Law Genotype) :
    (Epistemic.iidAlphabetLaw child M).expect silentCountR=(M:ℝ)*child.mass (false,true) := by
  rw [show (silentCountR : (Fin M → Genotype) → ℝ)=
      (fun w => (Epistemic.wordCount w (false,true):ℝ)) from
    funext (fun w => silentCountR_eq_count w)]
  exact iid_offspring_count_expectation child (false,true)

theorem iid_voterCountR_mean {M : ℕ} (child : Law Genotype) :
    (Epistemic.iidAlphabetLaw child M).expect voterCountR=(M:ℝ)*voterMass child := by
  unfold voterCountR
  rw [Law.expect_sum]
  have hx : child.expect (fun g => if g.1 then (0:ℝ) else 1)=voterMass child := by
    simp [Law.expect, Law1.mean, voterMass, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  calc
    _ = ∑ _i : Fin M, voterMass child := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Law.expect_pi_coord (fun _ : Fin M => child) i
        (fun g => if g.1 then (0:ℝ) else 1)).trans hx
    _ = _ := by simp

/-- G2: ratio of expected counts, distinguished from the preceding expected ratio. -/
theorem all00_one_step_ratio_of_expected_counts :
    let child := (MutationBaseline.bernoulli (1/10) (by norm_num) (by norm_num)).prod
      (MutationBaseline.bernoulli (1/10) (by norm_num) (by norm_num))
    let L := Epistemic.iidAlphabetLaw child 8
    let s := fun _ : Fin 4 => (false,false)
    0<L.expect (fun w => voterCountR (nextRoster s w)) ∧
      L.expect (fun w => silentCountR (nextRoster s w))/
        L.expect (fun w => voterCountR (nextRoster s w))=9/140 := by
  dsimp only
  simp_rw [nextRoster_silentCountR, nextRoster_voterCountR]
  rw [Law.expect_add, Law.expect_const, Law.expect_add, Law.expect_const,
    iid_silentCountR_mean, iid_voterCountR_mean]
  norm_num [silentCountR, voterCountR, voterMass, Law.prod, MutationBaseline.bernoulli]

/-- The implemented ranking retains its complete score/tie/index record at the cut. -/
theorem lexSurvivors_record_top {P S : ℕ} (hSP : S≤P)
    (score : Fin P → ℝ) (key : Fin P → ℤ) :
    ∀ i ∈ (NoisySelection.lexSurvivors hSP score key).val,
      ∀ j ∉ (NoisySelection.lexSurvivors hSP score key).val,
        NoisySelection.rankRecord score key i≤NoisySelection.rankRecord score key j := by
  intro i hi j hj
  have hi' : i ∈ (NoisySelection.rankingList score key).take S := by
    simpa [NoisySelection.lexSurvivors] using hi
  have hj' : j ∉ (NoisySelection.rankingList score key).take S := by
    simpa [NoisySelection.lexSurvivors] using hj
  have hjdrop : j ∈ (NoisySelection.rankingList score key).drop S := by
    have hall := NoisySelection.rankingList_mem score key j
    rw [← List.take_append_drop S (NoisySelection.rankingList score key), List.mem_append] at hall
    exact hall.resolve_left hj'
  have hpair := NoisySelection.rankingList_lexicographic score key
  rw [← List.take_append_drop S (NoisySelection.rankingList score key), List.pairwise_append] at hpair
  exact hpair.2.2 i hi' j hjdrop

/-- G1's corrected hypothesis uses at least S zero-advocate individuals, each ahead of every
one-advocate individual in the actual full ranking record. It forces zero-advocate survivors. -/
theorem priority_forces_zero_advocate_survivors {P S : ℕ} (hSP : S≤P)
    (z : Fin P → Genotype) (score : Fin P → ℝ) (key : Fin P → ℤ)
    (hcount : S≤(Finset.univ.filter (fun i => (z i).2=false)).card)
    (hpriority : ∀ i j, (z i).2=false → (z j).2=true →
      NoisySelection.rankRecord score key i<NoisySelection.rankRecord score key j) :
    ∀ i ∈ (NoisySelection.lexSurvivors hSP score key).val, (z i).2=false := by
  let A := NoisySelection.lexSurvivors hSP score key
  let T := Finset.univ.filter (fun i => (z i).2=false)
  intro i hi
  by_contra hn
  have hi1 : (z i).2=true := by cases h : (z i).2 <;> simp_all
  have hmiss : ∃ j ∈ T, j ∉ A.val := by
    by_contra hno
    have hsub : T⊆A.val := by simpa [Finset.subset_iff] using hno
    have he : T=A.val := Finset.eq_of_subset_of_card_le hsub (by simpa [A.property] using hcount)
    have hit : i∈T := he.symm ▸ hi
    exact hn (Finset.mem_filter.mp hit).2
  obtain ⟨j,hj,hjA⟩ := hmiss
  have hj0 : (z j).2=false := (Finset.mem_filter.mp hj).2
  exact (not_le_of_gt (hpriority j i hj0 hi1))
    (lexSurvivors_record_top hSP score key i hi j hjA)

/-- The rank-priority hypothesis produces the actual all-00 survivor roster in the all-voter model. -/
theorem priority_selectedRoster_all00 {P S : ℕ} (hSP : S≤P)
    (z : Fin P → Genotype) (score : Fin P → ℝ) (key : Fin P → ℤ)
    (hV : ∀ i, (z i).1=false)
    (hcount : S≤(Finset.univ.filter (fun i => (z i).2=false)).card)
    (hpriority : ∀ i j, (z i).2=false → (z j).2=true →
      NoisySelection.rankRecord score key i<NoisySelection.rankRecord score key j) :
    selectedRoster z (NoisySelection.lexSurvivors hSP score key)=fun _ => (false,false) := by
  funext i
  apply Prod.ext
  · exact hV _
  · exact priority_forces_zero_advocate_survivors hSP z score key hcount hpriority _
      (Finset.orderEmbOfFin_mem _ _ i)

/-- G1/G2 corrected one-step 1/15, derived from actual priority-selected all-voter survivors.
It is not a multigeneration claim and board-locus mutation is disabled. -/
theorem priority_one_step_one_fifteenth {P : ℕ} (hSP : 4≤P)
    (z : Fin P → Genotype) (score : Fin P → ℝ) (key : Fin P → ℤ)
    (hV : ∀ i, (z i).1=false)
    (hcount : 4≤(Finset.univ.filter (fun i => (z i).2=false)).card)
    (hpriority : ∀ i j, (z i).2=false → (z j).2=true →
      NoisySelection.rankRecord score key i<NoisySelection.rankRecord score key j) :
    nextSilentExpectation (selectedRoster z (NoisySelection.lexSurvivors hSP score key))
      ((MutationBaseline.bernoulli 0 (by norm_num) (by norm_num)).prod
        (MutationBaseline.bernoulli (1/10) (by norm_num) (by norm_num))) 8=1/15 := by
  rw [priority_selectedRoster_all00 hSP z score key hV hcount hpriority]
  exact all00_one_step_one_fifteenth

theorem constant_bind_mass {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (L : Law Ω) (K : Law Λ) (x : Λ) : (L.bind (fun _ => K)).mass x=K.mass x := by
  simp only [Law.bind, ← Finset.sum_mul, L.total, one_mul]

/-- Crossover of actual all-00 parents is 00, before mutation. -/
theorem all00_independentCrossover_law {S : ℕ} (hS : 0<S) :
    independentRosterCrossover (fun _ : Fin S => (false,false)) hS=
      NoisySelection.pointLaw (false,false) := by
  apply Epistemic.law_eq_of_mass_eq
  funext g
  change (((uniformIndex S hS).prod (uniformIndex S hS)).bind
    (fun _ => pairCrossover (false,false) (false,false))).mass g=_
  rw [constant_bind_mass, pairCrossover_diagonal_mass]
  by_cases hg : g=(false,false) <;> simp [NoisySelection.pointLaw, hg, Eq.comm]

/-- The distinct-parent protocol agrees on the fixed all-00 survivor state. -/
theorem all00_distinctCrossover_law {S : ℕ} (hS : 1<S) :
    distinctRosterCrossover (fun _ : Fin S => (false,false)) hS=
      NoisySelection.pointLaw (false,false) := by
  apply Epistemic.law_eq_of_mass_eq
  funext g
  change ((distinctPairLaw S hS).bind
    (fun _ => pairCrossover (false,false) (false,false))).mass g=_
  rw [constant_bind_mass, pairCrossover_diagonal_mass]
  by_cases hg : g=(false,false) <;> simp [NoisySelection.pointLaw, hg, Eq.comm]

/-- Independent offspring locus flips of 00 give exactly the advertised product law. -/
theorem mutate_point00_law (muB muA : ℝ)
    (hB0 : 0 ≤ muB) (hB1 : muB≤1) (hA0 : 0 ≤ muA) (hA1 : muA≤1) :
    mutate (NoisySelection.pointLaw (false,false)) muB muA hB0 hB1 hA0 hA1=
      (MutationBaseline.bernoulli muB hB0 hB1).prod
        (MutationBaseline.bernoulli muA hA0 hA1) := by
  apply Epistemic.law_eq_of_mass_eq
  funext g
  simp [mutate, Law.bind, NoisySelection.pointLaw, mutationKernel, flipLaw]

/-- G2 numerical level after actual independent-index crossover and offspring-only mutation. -/
theorem all00_actual_one_step_two_locus :
    nextSilentExpectation (fun _ : Fin 4 => (false,false))
      (mutate (independentRosterCrossover (fun _ : Fin 4 => (false,false)) (by norm_num))
        (1/10) (1/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) 8=
      3523336551/55000000000 := by
  rw [all00_independentCrossover_law, mutate_point00_law]
  exact all00_one_step_two_locus_expected_ratio

/-- G2's same fixed-survivor expected ratio with actual distinct-index crossover. -/
theorem all00_actual_distinct_one_step_two_locus :
    nextSilentExpectation (fun _ : Fin 4 => (false,false))
      (mutate (distinctRosterCrossover (fun _ : Fin 4 => (false,false)) (by norm_num))
        (1/10) (1/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) 8=
      3523336551/55000000000 := by
  rw [all00_distinctCrossover_law, mutate_point00_law]
  exact all00_one_step_two_locus_expected_ratio

/-- Minimal corrected G1: only a protected set of at least S zero-advocate individuals
must precede every one-advocate individual. Other zero-advocate individuals may rank anywhere. -/
theorem protected_set_forces_zero_advocate_survivors {P S : ℕ} (hSP : S≤P)
    (z : Fin P → Genotype) (score : Fin P → ℝ) (key : Fin P → ℤ) (T : Finset (Fin P))
    (hcount : S≤T.card) (hzero : ∀ i ∈ T, (z i).2=false)
    (hpriority : ∀ i ∈ T, ∀ j, (z j).2=true →
      NoisySelection.rankRecord score key i<NoisySelection.rankRecord score key j) :
    ∀ i ∈ (NoisySelection.lexSurvivors hSP score key).val, (z i).2=false := by
  let A := NoisySelection.lexSurvivors hSP score key
  intro i hi
  by_contra hn
  have hi1 : (z i).2=true := by cases h : (z i).2 <;> simp_all
  have hmiss : ∃ j ∈ T, j ∉ A.val := by
    by_contra hno
    have hsub : T⊆A.val := by simpa [Finset.subset_iff] using hno
    have he : T=A.val := Finset.eq_of_subset_of_card_le hsub (by simpa [A.property] using hcount)
    exact hn (hzero i (he.symm ▸ hi))
  obtain ⟨j,hj,hjA⟩ := hmiss
  exact (not_le_of_gt (hpriority j hj i hi1))
    (lexSurvivors_record_top hSP score key i hi j hjA)

theorem protected_set_selectedRoster_all00 {P S : ℕ} (hSP : S≤P)
    (z : Fin P → Genotype) (score : Fin P → ℝ) (key : Fin P → ℤ) (T : Finset (Fin P))
    (hV : ∀ i, (z i).1=false) (hcount : S≤T.card) (hzero : ∀ i ∈ T, (z i).2=false)
    (hpriority : ∀ i ∈ T, ∀ j, (z j).2=true →
      NoisySelection.rankRecord score key i<NoisySelection.rankRecord score key j) :
    selectedRoster z (NoisySelection.lexSurvivors hSP score key)=fun _ => (false,false) := by
  funext i
  apply Prod.ext
  · exact hV _
  · exact protected_set_forces_zero_advocate_survivors hSP z score key T hcount hzero hpriority _
      (Finset.orderEmbOfFin_mem _ _ i)

/-- G1/G2 exact experiment-size result: the minimal corrected ranking hypothesis,
actual independent survivor-index crossover, offspring-only advocate mutation, and no B mutation. -/
theorem corrected_priority_actual_one_step_one_fifteenth
    (z : Fin 12 → Genotype) (score : Fin 12 → ℝ) (key : Fin 12 → ℤ) (T : Finset (Fin 12))
    (hV : ∀ i, (z i).1=false) (hcount : 4≤T.card) (hzero : ∀ i ∈ T, (z i).2=false)
    (hpriority : ∀ i ∈ T, ∀ j, (z j).2=true →
      NoisySelection.rankRecord score key i<NoisySelection.rankRecord score key j) :
    let s := selectedRoster z (NoisySelection.lexSurvivors (by norm_num : 4≤12) score key)
    nextSilentExpectation s
      (mutate (independentRosterCrossover s (by norm_num))
        0 (1/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) 8=1/15 := by
  dsimp only
  rw [protected_set_selectedRoster_all00 (by norm_num : 4≤12) z score key T hV hcount hzero hpriority]
  rw [all00_independentCrossover_law, mutate_point00_law]
  exact all00_one_step_one_fifteenth

end
end SEKernel.GenotypeTransition
