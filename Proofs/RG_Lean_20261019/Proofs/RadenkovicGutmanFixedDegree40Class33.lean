/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree40Class33Batch000
import Proofs.RadenkovicGutmanFixedDegree40Class33Batch001
import Proofs.RadenkovicGutmanFixedDegree40Class33Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree40Class33
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree40Class33Cell000.slice,FixedDegree40Class33Cell001.slice,FixedDegree40Class33Cell002.slice,FixedDegree40Class33Cell003.slice,FixedDegree40Class33Cell004.slice,FixedDegree40Class33Cell005.slice,FixedDegree40Class33Cell006.slice,FixedDegree40Class33Cell007.slice,FixedDegree40Class33Cell008.slice,FixedDegree40Class33Cell009.slice,FixedDegree40Class33Cell010.slice,FixedDegree40Class33Cell011.slice,FixedDegree40Class33Cell012.slice,FixedDegree40Class33Cell013.slice,FixedDegree40Class33Cell014.slice,FixedDegree40Class33Cell015.slice,FixedDegree40Class33Cell016.slice,FixedDegree40Class33Cell017.slice,FixedDegree40Class33Cell018.slice,FixedDegree40Class33Cell019.slice,FixedDegree40Class33Cell020.slice,FixedDegree40Class33Cell021.slice,FixedDegree40Class33Cell022.slice,FixedDegree40Class33Cell023.slice,FixedDegree40Class33Cell024.slice,FixedDegree40Class33Cell025.slice,FixedDegree40Class33Cell026.slice,FixedDegree40Class33Cell027.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 40 2 2 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree40Class33Cell000.slice_checked,FixedDegree40Class33Cell001.slice_checked,FixedDegree40Class33Cell002.slice_checked,FixedDegree40Class33Cell003.slice_checked,FixedDegree40Class33Cell004.slice_checked,FixedDegree40Class33Cell005.slice_checked,FixedDegree40Class33Cell006.slice_checked,FixedDegree40Class33Cell007.slice_checked,FixedDegree40Class33Cell008.slice_checked,FixedDegree40Class33Cell009.slice_checked,FixedDegree40Class33Cell010.slice_checked,FixedDegree40Class33Cell011.slice_checked,FixedDegree40Class33Cell012.slice_checked,FixedDegree40Class33Cell013.slice_checked,FixedDegree40Class33Cell014.slice_checked,FixedDegree40Class33Cell015.slice_checked,FixedDegree40Class33Cell016.slice_checked,FixedDegree40Class33Cell017.slice_checked,FixedDegree40Class33Cell018.slice_checked,FixedDegree40Class33Cell019.slice_checked,FixedDegree40Class33Cell020.slice_checked,FixedDegree40Class33Cell021.slice_checked,FixedDegree40Class33Cell022.slice_checked,FixedDegree40Class33Cell023.slice_checked,FixedDegree40Class33Cell024.slice_checked,FixedDegree40Class33Cell025.slice_checked,FixedDegree40Class33Cell026.slice_checked,FixedDegree40Class33Cell027.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 40 2 2 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 40 2 2 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=40)
    (hp : ArmClasses.classify p=2) (hq : ArmClasses.classify q=2) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 40 (by decide) hd 2 2 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree40Class33
