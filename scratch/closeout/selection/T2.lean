import SEKernel.ScorePooling
open Finset SEKernel.FiniteProbability
open scoped Classical

noncomputable def fairBoard : Law Bool := SEKernel.MutationBaseline.bernoulli (1/2) (by norm_num) (by norm_num)

noncomputable def twelveLaw : Law (Fin 12 → Bool) := Law.pi (fun _ : Fin 12 => fairBoard)

def nt (z : Fin 12 → Bool) : ℕ := (Finset.univ.filter fun i => z i = true).card

theorem twelve_prob (E : (Fin 12 → Bool) → Prop) [DecidablePred E] :
    twelveLaw.prob E = ((Finset.univ.filter E).card : ℝ) / 4096 := by
  have hb : ∀ b, fairBoard.mass b = 1/2 := by
    intro b; cases b
    · simp [fairBoard, SEKernel.MutationBaseline.bernoulli]; norm_num
    · simp [fairBoard, SEKernel.MutationBaseline.bernoulli]
  have hm : ∀ z, twelveLaw.mass z = 1/4096 := by
    intro z
    show ∏ i, fairBoard.mass (z i) = 1/4096
    simp only [hb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [← Law.expect_indicator twelveLaw E]
  unfold Law.expect SEKernel.Law1.mean
  simp_rw [hm]
  rw [← Finset.mul_sum, Finset.sum_boole]
  ring

theorem nt_flip (z : Fin 12 → Bool) : nt (fun i => !z i) + nt z = 12 := by
  unfold nt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 12)))
    (fun i => z i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have he : (Finset.univ.filter fun i => (!z i) = true) = Finset.univ.filter fun i => ¬ z i = true := by
    ext i; simp
  rw [he]
  omega

theorem card_six : ((Finset.univ : Finset (Fin 12 → Bool)).filter (fun z => nt z = 6)).card = 924 := by
  have h := Finset.card_powersetCard 6 (Finset.univ : Finset (Fin 12))
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [show Nat.choose 12 6 = 924 by rfl] at h
  rw [← h]
  apply Finset.card_nbij' (fun z => Finset.univ.filter fun i => z i = true) (fun s i => decide (i ∈ s))
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz
    simp [Finset.mem_powersetCard, nt] at hz ⊢
    exact hz
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, nt]
    simpa using hs.2
  · intro z _
    funext i
    simp
  · intro s _
    ext i
    simp

theorem card_hi_lo : ((Finset.univ : Finset (Fin 12 → Bool)).filter (fun z => 6 < nt z)).card =
    ((Finset.univ : Finset (Fin 12 → Bool)).filter (fun z => nt z < 6)).card := by
  apply Finset.card_nbij' (fun z i => !z i) (fun z i => !z i)
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
    have := nt_flip z
    omega
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
    have := nt_flip z
    omega
  · intro z _; funext i; simp
  · intro z _; funext i; simp

theorem twelve_tie : twelveLaw.prob (fun z => nt z = 6) = 231/1024 := by
  rw [twelve_prob]
  have := card_six
  rw [this]; norm_num
