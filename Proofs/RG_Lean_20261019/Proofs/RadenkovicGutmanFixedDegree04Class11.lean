/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree04Class11Batch000
import Proofs.RadenkovicGutmanFixedDegree04Class11Batch001
import Proofs.RadenkovicGutmanFixedDegree04Class11Batch002
import Proofs.RadenkovicGutmanFixedDegree04Class11Batch003

namespace Gebendorfer.RadenkovicGutman.FixedDegree04Class11
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree04Class11Cell000.slice,FixedDegree04Class11Cell001.slice,FixedDegree04Class11Cell002.slice,FixedDegree04Class11Cell003.slice,FixedDegree04Class11Cell004.slice,FixedDegree04Class11Cell005.slice,FixedDegree04Class11Cell006.slice,FixedDegree04Class11Cell007.slice,FixedDegree04Class11Cell008.slice,FixedDegree04Class11Cell009.slice,FixedDegree04Class11Cell010.slice,FixedDegree04Class11Cell011.slice,FixedDegree04Class11Cell012.slice,FixedDegree04Class11Cell013.slice,FixedDegree04Class11Cell014.slice,FixedDegree04Class11Cell015.slice,FixedDegree04Class11Cell016.slice,FixedDegree04Class11Cell017.slice,FixedDegree04Class11Cell018.slice,FixedDegree04Class11Cell019.slice,FixedDegree04Class11Cell020.slice,FixedDegree04Class11Cell021.slice,FixedDegree04Class11Cell022.slice,FixedDegree04Class11Cell023.slice,FixedDegree04Class11Cell024.slice,FixedDegree04Class11Cell025.slice,FixedDegree04Class11Cell026.slice,FixedDegree04Class11Cell027.slice,FixedDegree04Class11Cell028.slice,FixedDegree04Class11Cell029.slice,FixedDegree04Class11Cell030.slice,FixedDegree04Class11Cell031.slice,FixedDegree04Class11Cell032.slice,FixedDegree04Class11Cell033.slice,FixedDegree04Class11Cell034.slice,FixedDegree04Class11Cell035.slice,FixedDegree04Class11Cell036.slice,FixedDegree04Class11Cell037.slice,FixedDegree04Class11Cell038.slice,FixedDegree04Class11Cell039.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 4 0 0 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree04Class11Cell000.slice_checked,FixedDegree04Class11Cell001.slice_checked,FixedDegree04Class11Cell002.slice_checked,FixedDegree04Class11Cell003.slice_checked,FixedDegree04Class11Cell004.slice_checked,FixedDegree04Class11Cell005.slice_checked,FixedDegree04Class11Cell006.slice_checked,FixedDegree04Class11Cell007.slice_checked,FixedDegree04Class11Cell008.slice_checked,FixedDegree04Class11Cell009.slice_checked,FixedDegree04Class11Cell010.slice_checked,FixedDegree04Class11Cell011.slice_checked,FixedDegree04Class11Cell012.slice_checked,FixedDegree04Class11Cell013.slice_checked,FixedDegree04Class11Cell014.slice_checked,FixedDegree04Class11Cell015.slice_checked,FixedDegree04Class11Cell016.slice_checked,FixedDegree04Class11Cell017.slice_checked,FixedDegree04Class11Cell018.slice_checked,FixedDegree04Class11Cell019.slice_checked,FixedDegree04Class11Cell020.slice_checked,FixedDegree04Class11Cell021.slice_checked,FixedDegree04Class11Cell022.slice_checked,FixedDegree04Class11Cell023.slice_checked,FixedDegree04Class11Cell024.slice_checked,FixedDegree04Class11Cell025.slice_checked,FixedDegree04Class11Cell026.slice_checked,FixedDegree04Class11Cell027.slice_checked,FixedDegree04Class11Cell028.slice_checked,FixedDegree04Class11Cell029.slice_checked,FixedDegree04Class11Cell030.slice_checked,FixedDegree04Class11Cell031.slice_checked,FixedDegree04Class11Cell032.slice_checked,FixedDegree04Class11Cell033.slice_checked,FixedDegree04Class11Cell034.slice_checked,FixedDegree04Class11Cell035.slice_checked,FixedDegree04Class11Cell036.slice_checked,FixedDegree04Class11Cell037.slice_checked,FixedDegree04Class11Cell038.slice_checked,FixedDegree04Class11Cell039.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 4 0 0 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 4 0 0 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=4)
    (hp : ArmClasses.classify p=0) (hq : ArmClasses.classify q=0) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 4 (by decide) hd 0 0 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree04Class11
