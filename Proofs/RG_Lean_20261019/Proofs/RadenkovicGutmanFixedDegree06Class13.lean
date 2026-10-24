/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree06Class13Batch000
import Proofs.RadenkovicGutmanFixedDegree06Class13Batch001
import Proofs.RadenkovicGutmanFixedDegree06Class13Batch002
import Proofs.RadenkovicGutmanFixedDegree06Class13Batch003

namespace Gebendorfer.RadenkovicGutman.FixedDegree06Class13
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree06Class13Cell000.slice,FixedDegree06Class13Cell001.slice,FixedDegree06Class13Cell002.slice,FixedDegree06Class13Cell003.slice,FixedDegree06Class13Cell004.slice,FixedDegree06Class13Cell005.slice,FixedDegree06Class13Cell006.slice,FixedDegree06Class13Cell007.slice,FixedDegree06Class13Cell008.slice,FixedDegree06Class13Cell009.slice,FixedDegree06Class13Cell010.slice,FixedDegree06Class13Cell011.slice,FixedDegree06Class13Cell012.slice,FixedDegree06Class13Cell013.slice,FixedDegree06Class13Cell014.slice,FixedDegree06Class13Cell015.slice,FixedDegree06Class13Cell016.slice,FixedDegree06Class13Cell017.slice,FixedDegree06Class13Cell018.slice,FixedDegree06Class13Cell019.slice,FixedDegree06Class13Cell020.slice,FixedDegree06Class13Cell021.slice,FixedDegree06Class13Cell022.slice,FixedDegree06Class13Cell023.slice,FixedDegree06Class13Cell024.slice,FixedDegree06Class13Cell025.slice,FixedDegree06Class13Cell026.slice,FixedDegree06Class13Cell027.slice,FixedDegree06Class13Cell028.slice,FixedDegree06Class13Cell029.slice,FixedDegree06Class13Cell030.slice,FixedDegree06Class13Cell031.slice,FixedDegree06Class13Cell032.slice,FixedDegree06Class13Cell033.slice,FixedDegree06Class13Cell034.slice,FixedDegree06Class13Cell035.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 6 0 2 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree06Class13Cell000.slice_checked,FixedDegree06Class13Cell001.slice_checked,FixedDegree06Class13Cell002.slice_checked,FixedDegree06Class13Cell003.slice_checked,FixedDegree06Class13Cell004.slice_checked,FixedDegree06Class13Cell005.slice_checked,FixedDegree06Class13Cell006.slice_checked,FixedDegree06Class13Cell007.slice_checked,FixedDegree06Class13Cell008.slice_checked,FixedDegree06Class13Cell009.slice_checked,FixedDegree06Class13Cell010.slice_checked,FixedDegree06Class13Cell011.slice_checked,FixedDegree06Class13Cell012.slice_checked,FixedDegree06Class13Cell013.slice_checked,FixedDegree06Class13Cell014.slice_checked,FixedDegree06Class13Cell015.slice_checked,FixedDegree06Class13Cell016.slice_checked,FixedDegree06Class13Cell017.slice_checked,FixedDegree06Class13Cell018.slice_checked,FixedDegree06Class13Cell019.slice_checked,FixedDegree06Class13Cell020.slice_checked,FixedDegree06Class13Cell021.slice_checked,FixedDegree06Class13Cell022.slice_checked,FixedDegree06Class13Cell023.slice_checked,FixedDegree06Class13Cell024.slice_checked,FixedDegree06Class13Cell025.slice_checked,FixedDegree06Class13Cell026.slice_checked,FixedDegree06Class13Cell027.slice_checked,FixedDegree06Class13Cell028.slice_checked,FixedDegree06Class13Cell029.slice_checked,FixedDegree06Class13Cell030.slice_checked,FixedDegree06Class13Cell031.slice_checked,FixedDegree06Class13Cell032.slice_checked,FixedDegree06Class13Cell033.slice_checked,FixedDegree06Class13Cell034.slice_checked,FixedDegree06Class13Cell035.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 6 0 2 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 6 0 2 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=6)
    (hp : ArmClasses.classify p=0) (hq : ArmClasses.classify q=2) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 6 (by decide) hd 0 2 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree06Class13
