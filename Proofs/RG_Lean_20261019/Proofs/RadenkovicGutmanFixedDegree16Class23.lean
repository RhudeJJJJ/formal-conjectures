/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree16Class23Batch000
import Proofs.RadenkovicGutmanFixedDegree16Class23Batch001
import Proofs.RadenkovicGutmanFixedDegree16Class23Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree16Class23
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree16Class23Cell000.slice,FixedDegree16Class23Cell001.slice,FixedDegree16Class23Cell002.slice,FixedDegree16Class23Cell003.slice,FixedDegree16Class23Cell004.slice,FixedDegree16Class23Cell005.slice,FixedDegree16Class23Cell006.slice,FixedDegree16Class23Cell007.slice,FixedDegree16Class23Cell008.slice,FixedDegree16Class23Cell009.slice,FixedDegree16Class23Cell010.slice,FixedDegree16Class23Cell011.slice,FixedDegree16Class23Cell012.slice,FixedDegree16Class23Cell013.slice,FixedDegree16Class23Cell014.slice,FixedDegree16Class23Cell015.slice,FixedDegree16Class23Cell016.slice,FixedDegree16Class23Cell017.slice,FixedDegree16Class23Cell018.slice,FixedDegree16Class23Cell019.slice,FixedDegree16Class23Cell020.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 16 1 2 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree16Class23Cell000.slice_checked,FixedDegree16Class23Cell001.slice_checked,FixedDegree16Class23Cell002.slice_checked,FixedDegree16Class23Cell003.slice_checked,FixedDegree16Class23Cell004.slice_checked,FixedDegree16Class23Cell005.slice_checked,FixedDegree16Class23Cell006.slice_checked,FixedDegree16Class23Cell007.slice_checked,FixedDegree16Class23Cell008.slice_checked,FixedDegree16Class23Cell009.slice_checked,FixedDegree16Class23Cell010.slice_checked,FixedDegree16Class23Cell011.slice_checked,FixedDegree16Class23Cell012.slice_checked,FixedDegree16Class23Cell013.slice_checked,FixedDegree16Class23Cell014.slice_checked,FixedDegree16Class23Cell015.slice_checked,FixedDegree16Class23Cell016.slice_checked,FixedDegree16Class23Cell017.slice_checked,FixedDegree16Class23Cell018.slice_checked,FixedDegree16Class23Cell019.slice_checked,FixedDegree16Class23Cell020.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 16 1 2 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 16 1 2 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=16)
    (hp : ArmClasses.classify p=1) (hq : ArmClasses.classify q=2) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 16 (by decide) hd 1 2 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree16Class23
