/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree12Class11Batch000
import Proofs.RadenkovicGutmanFixedDegree12Class11Batch001
import Proofs.RadenkovicGutmanFixedDegree12Class11Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree12Class11
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree12Class11Cell000.slice,FixedDegree12Class11Cell001.slice,FixedDegree12Class11Cell002.slice,FixedDegree12Class11Cell003.slice,FixedDegree12Class11Cell004.slice,FixedDegree12Class11Cell005.slice,FixedDegree12Class11Cell006.slice,FixedDegree12Class11Cell007.slice,FixedDegree12Class11Cell008.slice,FixedDegree12Class11Cell009.slice,FixedDegree12Class11Cell010.slice,FixedDegree12Class11Cell011.slice,FixedDegree12Class11Cell012.slice,FixedDegree12Class11Cell013.slice,FixedDegree12Class11Cell014.slice,FixedDegree12Class11Cell015.slice,FixedDegree12Class11Cell016.slice,FixedDegree12Class11Cell017.slice,FixedDegree12Class11Cell018.slice,FixedDegree12Class11Cell019.slice,FixedDegree12Class11Cell020.slice,FixedDegree12Class11Cell021.slice,FixedDegree12Class11Cell022.slice,FixedDegree12Class11Cell023.slice,FixedDegree12Class11Cell024.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 12 0 0 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree12Class11Cell000.slice_checked,FixedDegree12Class11Cell001.slice_checked,FixedDegree12Class11Cell002.slice_checked,FixedDegree12Class11Cell003.slice_checked,FixedDegree12Class11Cell004.slice_checked,FixedDegree12Class11Cell005.slice_checked,FixedDegree12Class11Cell006.slice_checked,FixedDegree12Class11Cell007.slice_checked,FixedDegree12Class11Cell008.slice_checked,FixedDegree12Class11Cell009.slice_checked,FixedDegree12Class11Cell010.slice_checked,FixedDegree12Class11Cell011.slice_checked,FixedDegree12Class11Cell012.slice_checked,FixedDegree12Class11Cell013.slice_checked,FixedDegree12Class11Cell014.slice_checked,FixedDegree12Class11Cell015.slice_checked,FixedDegree12Class11Cell016.slice_checked,FixedDegree12Class11Cell017.slice_checked,FixedDegree12Class11Cell018.slice_checked,FixedDegree12Class11Cell019.slice_checked,FixedDegree12Class11Cell020.slice_checked,FixedDegree12Class11Cell021.slice_checked,FixedDegree12Class11Cell022.slice_checked,FixedDegree12Class11Cell023.slice_checked,FixedDegree12Class11Cell024.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 12 0 0 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 12 0 0 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=12)
    (hp : ArmClasses.classify p=0) (hq : ArmClasses.classify q=0) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 12 (by decide) hd 0 0 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree12Class11
