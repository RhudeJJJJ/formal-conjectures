/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree22Class11Batch000
import Proofs.RadenkovicGutmanFixedDegree22Class11Batch001
import Proofs.RadenkovicGutmanFixedDegree22Class11Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree22Class11
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree22Class11Cell000.slice,FixedDegree22Class11Cell001.slice,FixedDegree22Class11Cell002.slice,FixedDegree22Class11Cell003.slice,FixedDegree22Class11Cell004.slice,FixedDegree22Class11Cell005.slice,FixedDegree22Class11Cell006.slice,FixedDegree22Class11Cell007.slice,FixedDegree22Class11Cell008.slice,FixedDegree22Class11Cell009.slice,FixedDegree22Class11Cell010.slice,FixedDegree22Class11Cell011.slice,FixedDegree22Class11Cell012.slice,FixedDegree22Class11Cell013.slice,FixedDegree22Class11Cell014.slice,FixedDegree22Class11Cell015.slice,FixedDegree22Class11Cell016.slice,FixedDegree22Class11Cell017.slice,FixedDegree22Class11Cell018.slice,FixedDegree22Class11Cell019.slice,FixedDegree22Class11Cell020.slice,FixedDegree22Class11Cell021.slice,FixedDegree22Class11Cell022.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 22 0 0 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree22Class11Cell000.slice_checked,FixedDegree22Class11Cell001.slice_checked,FixedDegree22Class11Cell002.slice_checked,FixedDegree22Class11Cell003.slice_checked,FixedDegree22Class11Cell004.slice_checked,FixedDegree22Class11Cell005.slice_checked,FixedDegree22Class11Cell006.slice_checked,FixedDegree22Class11Cell007.slice_checked,FixedDegree22Class11Cell008.slice_checked,FixedDegree22Class11Cell009.slice_checked,FixedDegree22Class11Cell010.slice_checked,FixedDegree22Class11Cell011.slice_checked,FixedDegree22Class11Cell012.slice_checked,FixedDegree22Class11Cell013.slice_checked,FixedDegree22Class11Cell014.slice_checked,FixedDegree22Class11Cell015.slice_checked,FixedDegree22Class11Cell016.slice_checked,FixedDegree22Class11Cell017.slice_checked,FixedDegree22Class11Cell018.slice_checked,FixedDegree22Class11Cell019.slice_checked,FixedDegree22Class11Cell020.slice_checked,FixedDegree22Class11Cell021.slice_checked,FixedDegree22Class11Cell022.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 22 0 0 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 22 0 0 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=22)
    (hp : ArmClasses.classify p=0) (hq : ArmClasses.classify q=0) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 22 (by decide) hd 0 0 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree22Class11
