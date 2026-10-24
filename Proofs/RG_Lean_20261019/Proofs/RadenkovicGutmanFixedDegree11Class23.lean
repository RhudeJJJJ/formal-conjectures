/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree11Class23Batch000
import Proofs.RadenkovicGutmanFixedDegree11Class23Batch001

namespace Gebendorfer.RadenkovicGutman.FixedDegree11Class23
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree11Class23Cell000.slice,FixedDegree11Class23Cell001.slice,FixedDegree11Class23Cell002.slice,FixedDegree11Class23Cell003.slice,FixedDegree11Class23Cell004.slice,FixedDegree11Class23Cell005.slice,FixedDegree11Class23Cell006.slice,FixedDegree11Class23Cell007.slice,FixedDegree11Class23Cell008.slice,FixedDegree11Class23Cell009.slice,FixedDegree11Class23Cell010.slice,FixedDegree11Class23Cell011.slice,FixedDegree11Class23Cell012.slice,FixedDegree11Class23Cell013.slice,FixedDegree11Class23Cell014.slice,FixedDegree11Class23Cell015.slice,FixedDegree11Class23Cell016.slice,FixedDegree11Class23Cell017.slice,FixedDegree11Class23Cell018.slice,FixedDegree11Class23Cell019.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 11 1 2 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree11Class23Cell000.slice_checked,FixedDegree11Class23Cell001.slice_checked,FixedDegree11Class23Cell002.slice_checked,FixedDegree11Class23Cell003.slice_checked,FixedDegree11Class23Cell004.slice_checked,FixedDegree11Class23Cell005.slice_checked,FixedDegree11Class23Cell006.slice_checked,FixedDegree11Class23Cell007.slice_checked,FixedDegree11Class23Cell008.slice_checked,FixedDegree11Class23Cell009.slice_checked,FixedDegree11Class23Cell010.slice_checked,FixedDegree11Class23Cell011.slice_checked,FixedDegree11Class23Cell012.slice_checked,FixedDegree11Class23Cell013.slice_checked,FixedDegree11Class23Cell014.slice_checked,FixedDegree11Class23Cell015.slice_checked,FixedDegree11Class23Cell016.slice_checked,FixedDegree11Class23Cell017.slice_checked,FixedDegree11Class23Cell018.slice_checked,FixedDegree11Class23Cell019.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 11 1 2 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 11 1 2 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=11)
    (hp : ArmClasses.classify p=1) (hq : ArmClasses.classify q=2) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 11 (by decide) hd 1 2 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree11Class23
