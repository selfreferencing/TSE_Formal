import SEKernel.SpawnAllocation
open SEKernel.Epistemic
open scoped Classical
example (x y : Bool) : plurality ![some x,some y]=some x := by
  have hu : (Finset.univ : Finset (Fin 2))={0,1} := by ext i; fin_cases i <;> simp
  cases x <;> cases y <;>
    norm_num [plurality,candidatePositions,labelCount,hu,Fin.forall_fin_succ,Fin.ext_iff]
