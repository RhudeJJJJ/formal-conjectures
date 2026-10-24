/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree04Class23Batch000
import Proofs.RadenkovicGutmanFixedDegree04Class23Batch001
import Proofs.RadenkovicGutmanFixedDegree04Class23Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree04Class23
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree04Class23Cell000.slice,FixedDegree04Class23Cell001.slice,FixedDegree04Class23Cell002.slice,FixedDegree04Class23Cell003.slice,FixedDegree04Class23Cell004.slice,FixedDegree04Class23Cell005.slice,FixedDegree04Class23Cell006.slice,FixedDegree04Class23Cell007.slice,FixedDegree04Class23Cell008.slice,FixedDegree04Class23Cell009.slice,FixedDegree04Class23Cell010.slice,FixedDegree04Class23Cell011.slice,FixedDegree04Class23Cell012.slice,FixedDegree04Class23Cell013.slice,FixedDegree04Class23Cell014.slice,FixedDegree04Class23Cell015.slice,FixedDegree04Class23Cell016.slice,FixedDegree04Class23Cell017.slice,FixedDegree04Class23Cell018.slice,FixedDegree04Class23Cell019.slice,FixedDegree04Class23Cell020.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 4 1 2 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree04Class23Cell000.slice_checked,FixedDegree04Class23Cell001.slice_checked,FixedDegree04Class23Cell002.slice_checked,FixedDegree04Class23Cell003.slice_checked,FixedDegree04Class23Cell004.slice_checked,FixedDegree04Class23Cell005.slice_checked,FixedDegree04Class23Cell006.slice_checked,FixedDegree04Class23Cell007.slice_checked,FixedDegree04Class23Cell008.slice_checked,FixedDegree04Class23Cell009.slice_checked,FixedDegree04Class23Cell010.slice_checked,FixedDegree04Class23Cell011.slice_checked,FixedDegree04Class23Cell012.slice_checked,FixedDegree04Class23Cell013.slice_checked,FixedDegree04Class23Cell014.slice_checked,FixedDegree04Class23Cell015.slice_checked,FixedDegree04Class23Cell016.slice_checked,FixedDegree04Class23Cell017.slice_checked,FixedDegree04Class23Cell018.slice_checked,FixedDegree04Class23Cell019.slice_checked,FixedDegree04Class23Cell020.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 4 1 2 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 4 1 2 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=4)
    (hp : ArmClasses.classify p=1) (hq : ArmClasses.classify q=2) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 4 (by decide) hd 1 2 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree04Class23
