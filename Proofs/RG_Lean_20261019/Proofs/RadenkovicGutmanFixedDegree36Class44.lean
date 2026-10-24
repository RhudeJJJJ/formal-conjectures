/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree36Class44Batch000
import Proofs.RadenkovicGutmanFixedDegree36Class44Batch001
import Proofs.RadenkovicGutmanFixedDegree36Class44Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree36Class44
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree36Class44Cell000.slice,FixedDegree36Class44Cell001.slice,FixedDegree36Class44Cell002.slice,FixedDegree36Class44Cell003.slice,FixedDegree36Class44Cell004.slice,FixedDegree36Class44Cell005.slice,FixedDegree36Class44Cell006.slice,FixedDegree36Class44Cell007.slice,FixedDegree36Class44Cell008.slice,FixedDegree36Class44Cell009.slice,FixedDegree36Class44Cell010.slice,FixedDegree36Class44Cell011.slice,FixedDegree36Class44Cell012.slice,FixedDegree36Class44Cell013.slice,FixedDegree36Class44Cell014.slice,FixedDegree36Class44Cell015.slice,FixedDegree36Class44Cell016.slice,FixedDegree36Class44Cell017.slice,FixedDegree36Class44Cell018.slice,FixedDegree36Class44Cell019.slice,FixedDegree36Class44Cell020.slice,FixedDegree36Class44Cell021.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 36 3 3 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree36Class44Cell000.slice_checked,FixedDegree36Class44Cell001.slice_checked,FixedDegree36Class44Cell002.slice_checked,FixedDegree36Class44Cell003.slice_checked,FixedDegree36Class44Cell004.slice_checked,FixedDegree36Class44Cell005.slice_checked,FixedDegree36Class44Cell006.slice_checked,FixedDegree36Class44Cell007.slice_checked,FixedDegree36Class44Cell008.slice_checked,FixedDegree36Class44Cell009.slice_checked,FixedDegree36Class44Cell010.slice_checked,FixedDegree36Class44Cell011.slice_checked,FixedDegree36Class44Cell012.slice_checked,FixedDegree36Class44Cell013.slice_checked,FixedDegree36Class44Cell014.slice_checked,FixedDegree36Class44Cell015.slice_checked,FixedDegree36Class44Cell016.slice_checked,FixedDegree36Class44Cell017.slice_checked,FixedDegree36Class44Cell018.slice_checked,FixedDegree36Class44Cell019.slice_checked,FixedDegree36Class44Cell020.slice_checked,FixedDegree36Class44Cell021.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 36 3 3 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 36 3 3 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=36)
    (hp : ArmClasses.classify p=3) (hq : ArmClasses.classify q=3) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 36 (by decide) hd 3 3 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree36Class44
