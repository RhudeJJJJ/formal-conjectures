/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree05Class13Batch000
import Proofs.RadenkovicGutmanFixedDegree05Class13Batch001
import Proofs.RadenkovicGutmanFixedDegree05Class13Batch002
import Proofs.RadenkovicGutmanFixedDegree05Class13Batch003
import Proofs.RadenkovicGutmanFixedDegree05Class13Batch004

namespace Gebendorfer.RadenkovicGutman.FixedDegree05Class13
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree05Class13Cell000.slice,FixedDegree05Class13Cell001.slice,FixedDegree05Class13Cell002.slice,FixedDegree05Class13Cell003.slice,FixedDegree05Class13Cell004.slice,FixedDegree05Class13Cell005.slice,FixedDegree05Class13Cell006.slice,FixedDegree05Class13Cell007.slice,FixedDegree05Class13Cell008.slice,FixedDegree05Class13Cell009.slice,FixedDegree05Class13Cell010.slice,FixedDegree05Class13Cell011.slice,FixedDegree05Class13Cell012.slice,FixedDegree05Class13Cell013.slice,FixedDegree05Class13Cell014.slice,FixedDegree05Class13Cell015.slice,FixedDegree05Class13Cell016.slice,FixedDegree05Class13Cell017.slice,FixedDegree05Class13Cell018.slice,FixedDegree05Class13Cell019.slice,FixedDegree05Class13Cell020.slice,FixedDegree05Class13Cell021.slice,FixedDegree05Class13Cell022.slice,FixedDegree05Class13Cell023.slice,FixedDegree05Class13Cell024.slice,FixedDegree05Class13Cell025.slice,FixedDegree05Class13Cell026.slice,FixedDegree05Class13Cell027.slice,FixedDegree05Class13Cell028.slice,FixedDegree05Class13Cell029.slice,FixedDegree05Class13Cell030.slice,FixedDegree05Class13Cell031.slice,FixedDegree05Class13Cell032.slice,FixedDegree05Class13Cell033.slice,FixedDegree05Class13Cell034.slice,FixedDegree05Class13Cell035.slice,FixedDegree05Class13Cell036.slice,FixedDegree05Class13Cell037.slice,FixedDegree05Class13Cell038.slice,FixedDegree05Class13Cell039.slice,FixedDegree05Class13Cell040.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 5 0 2 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree05Class13Cell000.slice_checked,FixedDegree05Class13Cell001.slice_checked,FixedDegree05Class13Cell002.slice_checked,FixedDegree05Class13Cell003.slice_checked,FixedDegree05Class13Cell004.slice_checked,FixedDegree05Class13Cell005.slice_checked,FixedDegree05Class13Cell006.slice_checked,FixedDegree05Class13Cell007.slice_checked,FixedDegree05Class13Cell008.slice_checked,FixedDegree05Class13Cell009.slice_checked,FixedDegree05Class13Cell010.slice_checked,FixedDegree05Class13Cell011.slice_checked,FixedDegree05Class13Cell012.slice_checked,FixedDegree05Class13Cell013.slice_checked,FixedDegree05Class13Cell014.slice_checked,FixedDegree05Class13Cell015.slice_checked,FixedDegree05Class13Cell016.slice_checked,FixedDegree05Class13Cell017.slice_checked,FixedDegree05Class13Cell018.slice_checked,FixedDegree05Class13Cell019.slice_checked,FixedDegree05Class13Cell020.slice_checked,FixedDegree05Class13Cell021.slice_checked,FixedDegree05Class13Cell022.slice_checked,FixedDegree05Class13Cell023.slice_checked,FixedDegree05Class13Cell024.slice_checked,FixedDegree05Class13Cell025.slice_checked,FixedDegree05Class13Cell026.slice_checked,FixedDegree05Class13Cell027.slice_checked,FixedDegree05Class13Cell028.slice_checked,FixedDegree05Class13Cell029.slice_checked,FixedDegree05Class13Cell030.slice_checked,FixedDegree05Class13Cell031.slice_checked,FixedDegree05Class13Cell032.slice_checked,FixedDegree05Class13Cell033.slice_checked,FixedDegree05Class13Cell034.slice_checked,FixedDegree05Class13Cell035.slice_checked,FixedDegree05Class13Cell036.slice_checked,FixedDegree05Class13Cell037.slice_checked,FixedDegree05Class13Cell038.slice_checked,FixedDegree05Class13Cell039.slice_checked,FixedDegree05Class13Cell040.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 5 0 2 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 5 0 2 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=5)
    (hp : ArmClasses.classify p=0) (hq : ArmClasses.classify q=2) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 5 (by decide) hd 0 2 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree05Class13
