import SEKernel.SpawnAllocation
open SEKernel.Epistemic
open scoped Classical
example (x y : Bool) : (0 : Fin 2)∈candidatePositions ![some x,some y] := by
  have hu : (Finset.univ : Finset (Fin 2))={0,1} := by ext i; fin_cases i <;> simp
  cases x <;> cases y <;>
    norm_num [candidatePositions,labelCount,hu,Fin.forall_fin_succ]
